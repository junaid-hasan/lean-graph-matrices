import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Basic

open SimpleGraph

set_option diagnostics true

universe u

variable {V : Type} [Fintype V] [DecidableEq V]

structure SpanningTree (G : SimpleGraph V) where
  Tree : SimpleGraph V
  subG : Tree ≤ G
  isTree : Tree.IsTree

/-! ## Decidable `IsTree` -/

instance decidableIsTree (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet] :
    Decidable G.IsTree :=
  decidable_of_iff (G.Connected ∧ Fintype.card G.edgeSet + 1 = Fintype.card V)
    (by
      constructor
      · rintro ⟨hconn, hcard⟩
        rw [G.isTree_iff_connected_and_card]
        exact ⟨hconn, by simpa [Nat.card_eq_fintype_card] using hcard⟩
      · intro h
        rcases G.isTree_iff_connected_and_card.mp h with ⟨hconn, hcard_nat⟩
        exact ⟨hconn, by simpa [Nat.card_eq_fintype_card] using hcard_nat⟩)

/-! ## Fintype instance -/

instance finiteSpanningTree (G : SimpleGraph V) : Finite (SpanningTree G) := by
  refine Finite.of_injective (fun (t : SpanningTree G) => t.Tree) ?_
  intro t1 t2 h
  cases t1; cases t2; congr

noncomputable instance fintypeSpanningTree (G : SimpleGraph V) :
    Fintype (SpanningTree G) :=
  Fintype.ofFinite _

/-! ## `exists_leaf` lemma -/

/--
In any spanning tree on ≥ 2 vertices, for any root `q`,
there exists a leaf `v ≠ q` (a vertex of degree 1).

The proof uses the degree-sum argument: if `q` were the only leaf,
then every other vertex has degree ≥ 2, so the sum of degrees
would be ≥ 1 + 2(|V|-1) = 2|V|-1, but for a tree it's exactly
2|E| = 2(|V|-1) = 2|V|-2, contradiction.
-/
lemma exists_leaf {G : SimpleGraph V} [DecidableRel G.Adj] (T : SpanningTree G) (q : V)
    (hcard : 2 ≤ Fintype.card V) : ∃ v ≠ q, Nat.card (T.Tree.neighborSet v) = 1 := by
  classical
    haveI : DecidableRel T.Tree.Adj := λ a b => Classical.dec (T.Tree.Adj a b)
    have hone_lt : 1 < Fintype.card V := by omega
    have hnontriv : Nontrivial V := (Fintype.one_lt_card_iff_nontrivial.mp hone_lt)
    obtain ⟨v, hv⟩ := T.isTree.exists_vert_degree_one_of_nontrivial
    by_cases hvq : v = q
    · subst v
      -- hv : T.Tree.degree q = 1
      by_cases h_only_q : ∀ w : V, w ≠ q → T.Tree.degree w ≠ 1
      · -- q is the only vertex with degree 1: contradiction via degree sum
        have hconn : T.Tree.Connected := T.isTree.isConnected
        have hpreconn : T.Tree.Preconnected := hconn.preconnected
        -- Edge count for a tree: |E| = |V| - 1
        have hcard_tree : T.Tree.edgeFinset.card + 1 = Fintype.card V := by
          have h_card_edgeFinset : Fintype.card (T.Tree.edgeSet) = T.Tree.edgeFinset.card := by
            dsimp [edgeFinset]; simp
          have htc := ((isTree_iff_connected_and_card).mp T.isTree).2
          have htc' : Fintype.card (T.Tree.edgeSet) + 1 = Fintype.card V := by
            simpa [Nat.card_eq_fintype_card] using htc
          rw [h_card_edgeFinset] at htc'
          omega
        -- Degree sum identity
        have hsum : (∑ v : V, T.Tree.degree v) = 2 * T.Tree.edgeFinset.card :=
          sum_degrees_eq_twice_card_edges T.Tree
        -- In a connected graph with ≥ 2 vertices, every vertex has degree ≥ 1
        have h_degree_ge_one : ∀ x : V, 1 ≤ T.Tree.degree x := by
          intro x
          by_contra! hlt
          have hzero : T.Tree.degree x = 0 := by omega
          have h_nf_empty : T.Tree.neighborFinset x = ∅ := by
            have hcard_nf : (T.Tree.neighborFinset x).card = 0 := by
              rw [card_neighborFinset_eq_degree, hzero]
            exact Finset.card_eq_zero.mp hcard_nf
          have h_no_adj : ∀ u, ¬ T.Tree.Adj x u := by
            intro u hadj
            have : u ∈ T.Tree.neighborFinset x := (mem_neighborFinset _ _ _).mpr hadj
            rw [h_nf_empty] at this
            simp at this
          -- x is reachable from q (connected). If x ≠ q, any walk must start with an edge. If x = q, hv says degree = 1 ≠ 0.
          by_cases hxq : x = q
          · subst x; rw [hzero] at hv; omega
          · have hreach : T.Tree.Reachable x q := hpreconn x q
            rcases hreach with ⟨walk⟩
            cases walk with
            | nil => exact hxq rfl
            | cons hadj _ => exact h_no_adj _ hadj
        -- For w ≠ q: degree ≠ 1 and ≥ 1 implies degree ≥ 2
        have h_degree_ge_two : ∀ w, w ≠ q → 2 ≤ T.Tree.degree w := by
          intro w hwne
          have hge_one := h_degree_ge_one w
          have hne_one := h_only_q w hwne
          omega
        -- Sum lower bound: ∑ degree v ≥ 1 + 2*(|V|-1) = 2|V| - 1
        have hsum_lower : 2 * Fintype.card V - 1 ≤ (∑ v : V, T.Tree.degree v) := by
          have hsum_decomp : (∑ v : V, T.Tree.degree v) = T.Tree.degree q + (∑ w ∈ Finset.univ.erase q, T.Tree.degree w) := by
            calc
              (∑ v : V, T.Tree.degree v) = (∑ w ∈ Finset.univ.erase q, T.Tree.degree w) + T.Tree.degree q :=
                (Finset.sum_erase_add Finset.univ (fun v => T.Tree.degree v) (Finset.mem_univ q)).symm
              _ = T.Tree.degree q + (∑ w ∈ Finset.univ.erase q, T.Tree.degree w) := by rw [add_comm]
          rw [hsum_decomp, hv]
          have hsum_erase_ge : 2 * (Fintype.card V - 1) ≤ (∑ w ∈ Finset.univ.erase q, T.Tree.degree w) := by
            calc
              2 * (Fintype.card V - 1) = (∑ w ∈ Finset.univ.erase q, 2) := by
                simp [Finset.sum_const, smul_eq_mul, mul_comm]
              _ ≤ (∑ w ∈ Finset.univ.erase q, T.Tree.degree w) :=
                Finset.sum_le_sum (fun w hw => h_degree_ge_two w (Finset.ne_of_mem_erase hw))
          omega
        -- But the RHS = 2*(|V|-1) = 2|V| - 2, contradiction
        rw [hsum] at hsum_lower
        rw [hcard_tree.symm] at hsum_lower
        omega
      · push_neg at h_only_q
        rcases h_only_q with ⟨w, hw_ne, hw_deg⟩
        have hw_nat : Nat.card (T.Tree.neighborSet w) = 1 := by
          rw [Nat.card_eq_fintype_card]
          have h_card : Fintype.card (T.Tree.neighborSet w) = (T.Tree.neighborFinset w).card := by
            dsimp [SimpleGraph.neighborFinset]; simp
          rw [h_card, card_neighborFinset_eq_degree, hw_deg]
        exact ⟨w, hw_ne, hw_nat⟩
    · have hv_nat : Nat.card (T.Tree.neighborSet v) = 1 := by
        rw [Nat.card_eq_fintype_card]
        have h_card : Fintype.card (T.Tree.neighborSet v) = (T.Tree.neighborFinset v).card := by
          dsimp [SimpleGraph.neighborFinset]; simp
        rw [h_card, card_neighborFinset_eq_degree, hv]
      exact ⟨v, hvq, hv_nat⟩
