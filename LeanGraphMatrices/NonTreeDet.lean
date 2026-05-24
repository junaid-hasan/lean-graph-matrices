import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic

import LeanGraphMatrices.SignIncMatrix

open Matrix Finset SimpleGraph
open Classical in
attribute [local instance] Classical.dec Classical.propDecidable

variable {V : Type} [Fintype V] [LinearOrder V] [DecidableEq V]

/-- Graph formed by taking the image of S as edges. -/
def edgeGraph (q : V) (S : {v : V // v ≠ q} ↪ Sym2 V) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (Set.range S)

/-! ## Helper lemma: det = 0 when a nonempty subset of rows sums to zero -/

/-
If some nonempty finset of rows of a square matrix sums to zero (column-wise),
    then the determinant is zero.
    Proof: pick any element v₀ from the finset. Add all other rows in the finset
    to row v₀; each addition preserves det. The result has a zero row.
-/
lemma det_zero_of_sum_rows_eq_zero {n : Type*} [DecidableEq n] [Fintype n]
    {R : Type*} [CommRing R] (A : Matrix n n R)
    (S : Finset n) (hne : S.Nonempty)
    (hsum : ∀ j : n, ∑ i ∈ S, A i j = 0) :
    A.det = 0 := by
  -- Fix any vertex $v₀ \in S$ (use $hne.choose$).
  set v₀ := hne.choose with hv₀_def
  have hsum_zero : ∑ i ∈ S, A i = (0 : n → R) := by
    ext j; simp +decide [ hsum ] ;
  -- By repeatedly applying Matrix.det_updateRow_add_self, we can show that the determinant of the matrix obtained by adding all rows in S to row v₀ is equal to the determinant of A.
  have h_det_updateRow_add_self : ∀ (T : Finset n), (∀ i ∈ T, i ≠ v₀) → (Matrix.det (Matrix.updateRow A v₀ (A v₀ + ∑ i ∈ T, A i))) = Matrix.det A := by
    intro T hT_v₀
    induction' T using Finset.induction with i T hiT ih;
    · simp +decide [ Matrix.updateRow_self ];
    · rw [ ← ih fun j hj => hT_v₀ j ( Finset.mem_insert_of_mem hj ), Finset.sum_insert hiT ];
      have h_det_updateRow_add_self : Matrix.det (Matrix.updateRow (Matrix.updateRow A v₀ (A v₀ + ∑ x ∈ T, A x)) v₀ (A v₀ + ∑ x ∈ T, A x + A i)) = Matrix.det (Matrix.updateRow A v₀ (A v₀ + ∑ x ∈ T, A x)) := by
        convert Matrix.det_updateRow_add_self _ _ using 2;
        rotate_left;
        exact v₀;
        exact i;
        · exact Ne.symm ( hT_v₀ i ( Finset.mem_insert_self i T ) );
        · simp +decide [ Matrix.updateRow_apply, hT_v₀ i ( Finset.mem_insert_self i T ) ];
      convert h_det_updateRow_add_self using 2 ; ext j ; by_cases hj : j = v₀ <;> simp +decide [ hj ] ; ring;
  convert h_det_updateRow_add_self ( S.erase v₀ ) ( fun i hi => by aesop ) |> Eq.symm using 1;
  rw [ show ∑ i ∈ S.erase v₀, A i = -A v₀ from eq_neg_of_add_eq_zero_left <| by rw [ ← hsum_zero, ← Finset.sum_erase_add _ _ hne.choose_spec, add_comm ] ] ; simp +decide [ Matrix.det_eq_zero_of_row_eq_zero ];
  exact Eq.symm ( Matrix.det_eq_zero_of_row_eq_zero v₀ fun j => by simp +decide )

/-! ## Graph-theoretic helpers -/

section GraphTheory

variable {q : V} (S : {v : V // v ≠ q} ↪ Sym2 V)

/-- The edge graph is not a tree implies not connected.
    Key argument: |E(H)| ≤ |V|-1 (since edgeSet ⊆ range S and |range S| = |V|-1).
    If H is connected, then it has a spanning tree with |V|-1 edges, so |E(H)| ≥ |V|-1.
    Combined: |E(H)| = |V|-1 and H is connected, hence H is a tree by isTree_iff_connected_and_card. -/
lemma edgeGraph_not_tree_not_connected
    (hNotTree : ¬ (edgeGraph q S).IsTree) :
    ¬ (edgeGraph q S).Connected := by
  contrapose! hNotTree with h_conn
  obtain ⟨T, hTle, hTtree⟩ := h_conn.exists_isTree_le
  have h_card_T : Nat.card T.edgeSet = Fintype.card V - 1 := by
    have h1 := hTtree.card_edgeFinset
    rw [Nat.card_eq_fintype_card]
    rw [show Fintype.card T.edgeSet = T.edgeFinset.card from by
      rw [← Set.toFinset_card]; rfl]
    omega
  have h_card_le : Nat.card (edgeGraph q S).edgeSet ≤ Fintype.card V - 1 := by
    calc Nat.card (edgeGraph q S).edgeSet
        ≤ Nat.card (Set.range S) := by
          apply Nat.card_mono (Set.toFinite _)
          intro e he
          simp only [edgeGraph, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_diff] at he
          exact he.1
      _ = Fintype.card {v : V // v ≠ q} := by
          rw [Nat.card_eq_fintype_card, Set.card_range_of_injective S.injective]
      _ = Fintype.card V - 1 := by
          simp [Fintype.card_subtype_compl]
  have h_card_ge : Fintype.card V - 1 ≤ Nat.card (edgeGraph q S).edgeSet := by
    calc Fintype.card V - 1 = Nat.card T.edgeSet := h_card_T.symm
      _ ≤ Nat.card (edgeGraph q S).edgeSet := by
          apply Nat.card_mono (Set.toFinite _)
          exact SimpleGraph.edgeSet_mono hTle
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨h_conn, ?_⟩
  have hVpos : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨q⟩
  rw [Nat.card_eq_fintype_card (α := V)]
  omega

/-
If H is not connected and q : V, there exist u : V with ¬ H.Reachable q u.
    In particular, if H.Connected is false, then either V is empty (impossible since q exists)
    or there exist u,v not reachable. We can arrange one of them to be unreachable from q.
-/
lemma exists_unreachable_from_root (H : SimpleGraph V) [DecidableRel H.Adj]
    (q : V) (hNotConn : ¬ H.Connected) :
    ∃ u : V, ¬ H.Reachable q u := by
  simp_all +decide [ SimpleGraph.connected_iff_exists_forall_reachable ]

end GraphTheory

/-! ## Incidence matrix column sum over reachable component -/

section ColumnSum

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-
For an edge e = s(a,b) with a ≠ b, the sum of signedIncMatrix G v e over ALL vertices v is 0.
    This is because the +1 entry (min endpoint) and -1 entry (max endpoint) cancel,
    and all other entries are 0.
-/
lemma signedIncMatrix_col_sum_eq_zero (e : Sym2 V) :
    ∑ v : V, signedIncMatrix G v e = 0 := by
  obtain ⟨v, w⟩ : ∃ v w : V, e = s(v, w) := by
    rcases e with ⟨ v, w ⟩ ; exact ⟨ v, w, rfl ⟩;
  obtain ⟨w, hw⟩ := w;
  by_cases h : G.Adj v w <;> by_cases h' : v = w <;> simp_all +decide [ signedIncMatrix ];
  cases le_total v w <;> simp +decide [ *, Finset.sum_ite, Finset.filter_eq', Finset.filter_ne' ];
  grind +splitIndPred

/-
For an edge e = s(a,b) with a ≠ b, if a vertex v is not an endpoint of e,
    then signedIncMatrix G v e = 0. More precisely, signedIncMatrix G v e ≠ 0
    implies v is an endpoint of e.
-/
lemma signedIncMatrix_support_subset_endpoints (e : Sym2 V) (v : V)
    (hv : signedIncMatrix G v e ≠ 0) :
    v ∈ e := by
  contrapose! hv;
  exact signedIncMatrix_entry_not_incident _ ( show e ∉ G.incidenceSet v from fun h => hv <| by cases e; simp_all +decide [ SimpleGraph.incidenceSet ] )

/-- If H = fromEdgeSet T and H.Adj a b, and H.Reachable u a, then H.Reachable u b.
    (Adjacency within the graph extends reachability.) -/
lemma reachable_of_adj_reachable (H : SimpleGraph V) (u a b : V)
    (hadj : H.Adj a b) (hreach : H.Reachable u a) :
    H.Reachable u b :=
  hreach.trans hadj.reachable

/-
For an edge e ∈ range S (i.e., e is an edge of the edgeGraph),
    and a set C = {w | H.Reachable u w} where H = edgeGraph q S,
    the sum of signedIncMatrix G v e over v ∈ C is 0.

    If e = s(a,b) with a ≠ b: H.Adj a b, so a ∈ C ↔ b ∈ C (by reachability closure).
    Case both in C: sum over C captures both +1 and -1, sum = 0.
    Case neither in C: all entries over C are 0.

    If e = s(a,a): signedIncMatrix entries are all 0 (not adjacent), sum = 0.
-/
lemma signedIncMatrix_sum_over_reachable_component_eq_zero
    (q : V) (S : {v : V // v ≠ q} ↪ Sym2 V)
    (u : V)
    (j : {v : V // v ≠ q}) :
    ∑ v ∈ Finset.univ.filter (fun w => (edgeGraph q S).Reachable u w),
      signedIncMatrix G v (S j) = 0 := by
  have h_col_sum : ∑ v ∈ Finset.univ, signedIncMatrix G v (S j) = 0 := by
    convert signedIncMatrix_col_sum_eq_zero G ( S j ) using 1;
  -- Since $e = S j$ is in the range of $S$, it must be of the form $s(a, b)$ for some $a, b \in V$.
  obtain ⟨a, b, hab⟩ : ∃ a b : V, S j = s(a, b) := by
    cases h : S j ; aesop;
  by_cases h : a = b <;> simp_all +decide;
  · unfold signedIncMatrix; aesop;
  · -- Since $a$ and $b$ are reachable from $u$, both $a$ and $b$ are in the set of vertices reachable from $u$.
    have h_reachable : (edgeGraph q S).Reachable u a ↔ (edgeGraph q S).Reachable u b := by
      have h_adj : (edgeGraph q S).Adj a b := by
        unfold edgeGraph; aesop;
      exact ⟨ fun h => h.trans ( SimpleGraph.Adj.reachable h_adj ), fun h => h.trans ( SimpleGraph.Adj.reachable h_adj.symm ) ⟩;
    by_cases ha : (edgeGraph q S).Reachable u a <;> by_cases hb : (edgeGraph q S).Reachable u b <;> simp_all +decide;
    · rw [ ← h_col_sum, Finset.sum_subset ( Finset.subset_univ _ ) ];
      intro x hx hx'; contrapose! hx'; simp_all +decide [ signedIncMatrix ] ;
      grind +splitImp;
    · refine' Finset.sum_eq_zero fun x hx => _;
      by_contra h_nonzero;
      have := signedIncMatrix_support_subset_endpoints G s(a, b) x h_nonzero; simp_all +decide ;
      rcases this with ( rfl | rfl ) <;> tauto

end ColumnSum

/-! ## Main theorem -/

section prove

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-
If a selection of |V|-1 edges does not form a spanning tree of G, then the
    determinant of the corresponding submatrix of the reduced signed incidence
    matrix is zero.
-/
theorem signedInc_det_nontree (q : V) (S : {v : V // v ≠ q} ↪ Sym2 V)
    (hNotTree : ¬ (edgeGraph q S).IsTree) :
    ((reducedSignedIncMatrix G q).submatrix id S).det = 0 := by
  -- Step 1: not tree → not connected
  have hNotConn := edgeGraph_not_tree_not_connected S hNotTree
  -- Step 2: get vertex u unreachable from q
  obtain ⟨u, hu⟩ := exists_unreachable_from_root (edgeGraph q S) q hNotConn
  -- u ≠ q (since Reachable q q holds by refl)
  have huq : u ≠ q := by
    intro heq
    apply hu
    rw [heq]
  -- Step 3: define the row set T = {v : {v // v ≠ q} | Reachable u v.val}
  set T := Finset.univ.filter (fun (v : {v : V // v ≠ q}) =>
    (edgeGraph q S).Reachable u v.val) with hT_def
  -- T is nonempty (u is in it)
  have hTne : T.Nonempty := ⟨⟨u, huq⟩, by simp [hT_def]⟩
  -- Step 4: apply det_zero_of_sum_rows_eq_zero
  apply det_zero_of_sum_rows_eq_zero _ T hTne
  -- Need: ∀ j, ∑ i ∈ T, M i j = 0
  intro j
  -- reducedSignedIncMatrix unfolds to signedIncMatrix on the val
  -- We need to relate this to signedIncMatrix_sum_over_reachable_component_eq_zero
  -- Key: q is not reachable from u
  have huq_reach : ¬ (edgeGraph q S).Reachable u q := fun h => hu h.symm
  -- The sum over T of reducedSignedIncMatrix = sum over component C of signedIncMatrix
  -- because every vertex in C satisfies v ≠ q (since q ∉ C)
  have h_component_sum := signedIncMatrix_sum_over_reachable_component_eq_zero G q S u j
  -- C = Finset.univ.filter (fun w => Reachable u w)
  set C := Finset.univ.filter (fun w => (edgeGraph q S).Reachable u w) with hC_def
  -- Need: ∑ x ∈ T, reducedSignedIncMatrix G q x (S j) = ∑ v ∈ C, signedIncMatrix G v (S j)
  -- Then the latter is 0.
  -- The sum over T equals the sum over C because:
  -- 1. reducedSignedIncMatrix G q x e = signedIncMatrix G x.val e
  -- 2. T and C are in bijection via x ↦ x.val (since q ∉ C)
  convert h_component_sum using 1;
  refine' Finset.sum_bij ( fun x hx => x ) _ _ _ _ <;> simp +decide [ * ];
  · exact fun v hv => ⟨ hv, by rintro rfl; exact huq_reach hv ⟩;
  · unfold reducedSignedIncMatrix; aesop;

end prove