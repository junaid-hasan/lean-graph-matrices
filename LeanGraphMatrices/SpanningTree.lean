import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Basic

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
      by_cases h_only_q : ∀ w : V, w ≠ q → T.Tree.degree w ≠ 1
      · -- q is the only vertex with degree 1. Degrees sum to 2|V|-2,
        -- but each non-q vertex has degree ≥ 2, so sum ≥ 2|V|-1. Contradiction.
        sorry
      · push_neg at h_only_q
        rcases h_only_q with ⟨w, hw_ne, hw_deg⟩
        have hw_nat : Nat.card (T.Tree.neighborSet w) = 1 := by
          -- Nat.card of a Fintype equals Fintype.card
          sorry
        exact ⟨w, hw_ne, hw_nat⟩
    · have hv_nat : Nat.card (T.Tree.neighborSet v) = 1 := by
          -- Nat.card of a Fintype equals Fintype.card
          sorry
      exact ⟨v, hvq, hv_nat⟩
