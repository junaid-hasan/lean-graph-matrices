import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

import LeanGraphMatrices.SignIncMatrix
import LeanGraphMatrices.SpanningTree

open Matrix SimpleGraph Finset

variable {V : Type} [Fintype V] [LinearOrder V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj]

/-! ## Parent function in a rooted spanning tree -/

/-- The parent of a non-root vertex v ≠ q: the next vertex on the unique
    simple path from v to q in `T.Tree`. Defined as `getVert 1` of this path. -/
noncomputable def treeParent (T : SpanningTree G) (q : V) (v : {v : V // v ≠ q}) : V :=
  let p := (T.isTree.existsUnique_path v.val q).exists.choose
  p.getVert 1

lemma treeParent_adj (T : SpanningTree G) (q : V) (v : {v : V // v ≠ q}) :
    T.Tree.Adj v.val (treeParent T q v) := by
  dsimp [treeParent]
  let p := (T.isTree.existsUnique_path v.val q).exists.choose
  have hp : p.IsPath := (T.isTree.existsUnique_path v.val q).exists.choose_spec
  have hne : v.val ≠ q := v.property
  have hpos : 0 < p.length := by
    by_contra! h
    have hlen0 : p.length = 0 := by omega
    have heq : v.val = q := Walk.eq_of_length_eq_zero hlen0
    exact hne heq
  have hadj := Walk.adj_getVert_succ p (by omega)
  simpa [p.getVert_zero] using hadj

lemma treeParent_edge_mem (T : SpanningTree G) (q : V) (v : {v : V // v ≠ q}) :
    s(v.val, treeParent T q v) ∈ T.Tree.edgeSet :=
  (T.Tree.mem_edgeSet).mpr (treeParent_adj T q v)

/-! ## Edge embedding: bijection between non-root vertices and tree edges -/

/-
The map `v ↦ s(v, parent(v))` from non-root vertices to tree edges is injective.
    This uses the uniqueness of simple paths in a tree.
-/
lemma treeParent_edge_injective (T : SpanningTree G) (q : V) :
    Function.Injective (fun (v : {v : V // v ≠ q}) => s(v.val, treeParent T q v)) := by
  intro x y h
  -- By Sym2 equality, the ordered pairs are either equal or swapped.
  -- In either case, tree path uniqueness forces x = y.
  have := Sym2.eq_iff.mp h
  -- This gives a disjunction; both cases lead to x = y via tree properties.
  cases this <;> simp_all +decide [ Subtype.ext_iff ];
  -- By definition of treeParent, we know that treeParent T q y is the vertex adjacent to y in the path from y to q.
  obtain ⟨p_y, hp_y⟩ : ∃ p_y : SimpleGraph.Walk T.Tree y.val q, p_y.IsPath ∧ p_y.getVert 1 = treeParent T q y := by
    exact ⟨ _, ( T.isTree.existsUnique_path y.val q ).exists.choose_spec, rfl ⟩;
  -- By definition of treeParent, we know that treeParent T q x is the vertex adjacent to x in the path from x to q.
  obtain ⟨p_x, hp_x⟩ : ∃ p_x : SimpleGraph.Walk T.Tree x.val q, p_x.IsPath ∧ p_x.getVert 1 = treeParent T q x := by
    exact ⟨ _, ( T.isTree.existsUnique_path x.val q ).exists.choose_spec, rfl ⟩
  generalize_proofs at *; (
  have h_tail_path : ∃ p_tail : SimpleGraph.Walk T.Tree y.val q, p_tail.IsPath ∧ p_tail.getVert 0 = y.val ∧ p_tail.getVert 1 = p_x.getVert 2 := by
    -- Since p_x is a path, its tail is also a path.
    have h_tail_path : (p_x.tail).IsPath := by
      grind +suggestions
    generalize_proofs at *; (
    grind +suggestions)
  generalize_proofs at *; (
  have h_unique_path : ∀ p q : SimpleGraph.Walk T.Tree y.val q, p.IsPath → q.IsPath → p = q := by
    have := T.isTree.existsUnique_path y.val q; obtain ⟨ p, hp ⟩ := this; aesop;
  generalize_proofs at *; (
  grind +suggestions)))

/-- Embedding of non-root vertices into tree edges via the parent edge. -/
noncomputable def edgeEmbedding (T : SpanningTree G) (q : V) : {v : V // v ≠ q} ↪ Sym2 V :=
  ⟨fun v => s(v.val, treeParent T q v), treeParent_edge_injective T q⟩

/-! ## Leaf row has single non-zero entry -/

/-
For a leaf `v ≠ q`, its row in the reduced signed incidence submatrix
    has exactly one non-zero entry (±1 at column `v`). For any `j ≠ v`,
    `signedIncMatrix G v.val ((edgeEmbedding T q) j) = 0`.
    `hleaf` is `Nat.card (T.Tree.neighborSet v.val) = 1`, as from `exists_leaf`.
-/
lemma leaf_row_single_nonzero (T : SpanningTree G) (q : V) (v : {v : V // v ≠ q})
    (hleaf : Nat.card (T.Tree.neighborSet v.val) = 1) (j : {v : V // v ≠ q}) (hj : j ≠ v) :
    signedIncMatrix G v.val ((edgeEmbedding T q) j) = 0 := by
  apply signedIncMatrix_entry_not_incident;
  simp +decide [ SimpleGraph.incidenceSet, edgeEmbedding ];
  intro h;
  constructor <;> intro H;
  · exact hj ( Subtype.ext H.symm );
  · have h_contra : j.val ∈ T.Tree.neighborSet v.val ∧ treeParent T q v ∈ T.Tree.neighborSet v.val := by
      have h_contra : T.Tree.Adj j.val v.val := by
        have := treeParent_adj T q j; aesop;
      exact ⟨ by simpa [ SimpleGraph.adj_comm ] using h_contra, by simpa [ SimpleGraph.adj_comm ] using treeParent_adj T q v ⟩;
    have h_contra : j.val = treeParent T q v := by
      rw [ Nat.card_eq_one_iff_unique ] at hleaf;
      exact Subtype.ext_iff.mp ( hleaf.1.elim ⟨ j.val, h_contra.1 ⟩ ⟨ treeParent T q v, h_contra.2 ⟩ );
    have := treeParent_edge_injective T q ( show edgeEmbedding T q j = edgeEmbedding T q v from ?_ ) ; aesop;
    unfold edgeEmbedding; aesop;

/-! ## Helper lemmas for the determinantal theorem -/

/-
The entry M(w, i) of the tree submatrix is zero unless w.val is an endpoint
    of the edge s(i.val, treeParent T q i).
-/
lemma submatrix_entry_eq_zero_of_not_endpoint (T : SpanningTree G) (q : V)
    (w i : {v : V // v ≠ q})
    (hw1 : w.val ≠ i.val) (hw2 : w.val ≠ treeParent T q i) :
    signedIncMatrix G w.val ((edgeEmbedding T q) i) = 0 := by
  convert signedIncMatrix_entry_not_incident G _;
  simp_all +decide [ edgeEmbedding, mk'_mem_incidenceSet_iff ]

/-
The diagonal entry M(i, i) = signedIncMatrix G i.val s(i.val, treeParent T q i)
    is ±1, since i.val is an endpoint of its parent edge.
-/
lemma submatrix_diag_pm_one (T : SpanningTree G) (q : V) (i : {v : V // v ≠ q}) :
    signedIncMatrix G i.val ((edgeEmbedding T q) i) = 1 ∨
    signedIncMatrix G i.val ((edgeEmbedding T q) i) = -1 := by
  have h_adj : G.Adj i.val (treeParent T q i) := by
    exact T.subG ( treeParent_adj T q i );
  unfold signedIncMatrix edgeEmbedding; simp_all +decide [ Sym2.lift ] ;
  grind

/-- The depth of a non-root vertex: the length of the unique simple path to q. -/
noncomputable def treeDepth (T : SpanningTree G) (q : V) (v : {v : V // v ≠ q}) : ℕ :=
  (T.isTree.existsUnique_path v.val q).exists.choose.length

lemma treeDepth_pos (T : SpanningTree G) (q : V) (v : {v : V // v ≠ q}) :
    0 < treeDepth T q v := by
  have h_len_pos : ∀ {u v : V}, u ≠ v → ∀ p : T.Tree.Walk u v, p.length > 0 := by
    intros u v huv p; induction p <;> aesop;
  exact h_len_pos v.property _

/-
The parent of a vertex at depth 1 is q.
-/
lemma treeParent_eq_q_of_depth_one (T : SpanningTree G) (q : V) (v : {v : V // v ≠ q})
    (hd : treeDepth T q v = 1) : treeParent T q v = q := by
  convert T.isTree.existsUnique_path v.val q |> ExistsUnique.exists |> Classical.choose_spec |> fun h => ?_;
  have := hd;
  convert T.isTree.existsUnique_path v.val q |> ExistsUnique.exists |> Classical.choose_spec |> fun h => ?_;
  convert SimpleGraph.Walk.getVert_length ( Classical.choose ( T.isTree.existsUnique_path v.val q |> ExistsUnique.exists ) );
  unfold treeDepth at this; aesop;

/-
Key combinatorial lemma: if σ is a permutation of non-root vertices such that
    for every i, σ(i).val ∈ {i.val, treeParent T q i}, then σ = id.
    This uses the tree structure (acyclicity) to rule out non-trivial permutations.
-/
lemma perm_eq_id_of_endpoint_condition (T : SpanningTree G) (q : V)
    (σ : Equiv.Perm {v : V // v ≠ q})
    (h : ∀ i, (σ i).val = i.val ∨ (σ i).val = treeParent T q i) : σ = 1 := by
  -- We prove σ = 1 by contradiction. Assume σ ≠ 1. Then there exists some vertex i with σ(i) ≠ i.
  by_contra h_contra
  obtain ⟨i, hi⟩ : ∃ i : { v // v ≠ q }, σ i ≠ i := by
    exact not_forall.mp fun h => h_contra <| Equiv.Perm.ext h;
  -- Among all vertices v with σ(v) ≠ v, pick one with minimum treeDepth T q v. Call it v₀.
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : { v // v ≠ q }, σ v₀ ≠ v₀ ∧ ∀ v : { v // v ≠ q }, σ v ≠ v → treeDepth T q v₀ ≤ treeDepth T q v := by
    apply_rules [ Set.exists_min_image ];
    · exact Set.toFinite _;
    · exact ⟨ i, hi ⟩;
  -- Since σ(v₀) ≠ v₀, by hypothesis h, (σ v₀).val = treeParent T q v₀.
  have hv₀_parent : (σ v₀).val = treeParent T q v₀ := by
    exact Or.resolve_left ( h v₀ ) fun h' => hv₀.1 <| Subtype.ext h';
  -- Since treeDepth T q (σ v₀) < treeDepth T q v₀, by minimality of v₀, σ(σ v₀) = σ v₀.
  have hv₀_min : treeDepth T q (⟨treeParent T q v₀, by
    grind +revert⟩ : { v // v ≠ q }) < treeDepth T q v₀ := by
    have h_path_tail : (T.isTree.existsUnique_path v₀.val q).exists.choose.tail = (T.isTree.existsUnique_path (treeParent T q v₀) q).exists.choose := by
      have h_path_tail : (T.isTree.existsUnique_path v₀.val q).exists.choose.tail.IsPath := by
        have := Exists.choose_spec ( T.isTree.existsUnique_path v₀.val q |> ExistsUnique.exists );
        exact Walk.IsPath.tail this
      generalize_proofs at *;
      have h_unique_path : ∀ p₁ p₂ : SimpleGraph.Walk T.Tree (treeParent T q v₀) q, p₁.IsPath → p₂.IsPath → p₁ = p₂ := by
        intros p₁ p₂ hp₁ hp₂
        have h_unique_path : ∀ u v : V, ∀ p₁ p₂ : SimpleGraph.Walk T.Tree u v, p₁.IsPath → p₂.IsPath → p₁ = p₂ := by
          intros u v p₁ p₂ hp₁ hp₂
          have h_unique_path : ∀ u v : V, ∀ p₁ p₂ : SimpleGraph.Walk T.Tree u v, p₁.IsPath → p₂.IsPath → p₁ = p₂ := by
            intros u v p₁ p₂ hp₁ hp₂
            have h_unique_path : T.Tree.IsTree := by
              exact T.isTree
            have := h_unique_path.existsUnique_path u v;
            exact this.unique hp₁ hp₂
          generalize_proofs at *;
          exact h_unique_path u v p₁ p₂ hp₁ hp₂
        generalize_proofs at *;
        exact h_unique_path _ _ _ _ hp₁ hp₂
      generalize_proofs at *;
      grind +locals;
    simp +decide [ treeDepth ];
    grind +suggestions
  generalize_proofs at *;
  -- By minimality of v₀, σ(σ v₀) = σ v₀.
  have hv₀_sigma_sigma : σ (⟨treeParent T q v₀, by
    assumption⟩ : { v // v ≠ q }) = ⟨treeParent T q v₀, by
    assumption⟩ := by
    exact Classical.not_not.1 fun h => not_lt_of_ge ( hv₀.2 _ h ) hv₀_min
  generalize_proofs at *;
  have := σ.injective ( hv₀_sigma_sigma.trans ( Eq.symm <| show σ v₀ = ⟨ treeParent T q v₀, by assumption ⟩ from Subtype.ext hv₀_parent ) ) ; aesop;

/-
For σ ≠ id, the Leibniz product ∏ i, M(σ i, i) = 0.
-/
lemma prod_eq_zero_of_perm_ne_one (T : SpanningTree G) (q : V)
    (σ : Equiv.Perm {v : V // v ≠ q}) (hσ : σ ≠ 1) :
    ∏ i, signedIncMatrix G (σ i).val ((edgeEmbedding T q) i) = 0 := by
  -- By the contrapositive of `perm_eq_id_of_endpoint_condition`, there exists some `i` such that `(σ i).val ≠ i.val` and `(σ i).val ≠ treeParent T q i`.
  obtain ⟨i, hi⟩ : ∃ i : {v : V // v ≠ q}, (σ i).val ≠ i.val ∧ (σ i).val ≠ treeParent T q i := by
    contrapose! hσ;
    apply perm_eq_id_of_endpoint_condition T q σ;
    exact fun i => Classical.or_iff_not_imp_left.2 fun hi => hσ i hi;
  exact Finset.prod_eq_zero ( Finset.mem_univ i ) ( submatrix_entry_eq_zero_of_not_endpoint T q ( σ i ) i hi.1 hi.2 )

/-
A product of ±1 values is ±1.
-/
lemma prod_pm_one {ι : Type*} [Fintype ι] (f : ι → ℤ)
    (hf : ∀ i, f i = 1 ∨ f i = -1) :
    (∏ i, f i) = 1 ∨ (∏ i, f i) = -1 := by
  exact eq_or_eq_neg_of_abs_eq ( by rw [ Finset.abs_prod ] ; exact Finset.prod_eq_one fun i _ => by cases hf i <;> simp +decide [ * ] )

/-! ## Determinantal Lemma for Trees -/

theorem signedInc_det_tree (T : SpanningTree G) (q : V) :
    ((reducedSignedIncMatrix G q).submatrix id (edgeEmbedding T q)).det = 1 ∨
    ((reducedSignedIncMatrix G q).submatrix id (edgeEmbedding T q)).det = -1 := by
  set M : Matrix {v : V // v ≠ q} {v : V // v ≠ q} ℤ :=
    (reducedSignedIncMatrix G q).submatrix id (edgeEmbedding T q)
  -- Use the Leibniz formula: det M = ∑ σ, sign(σ) * ∏ i, M(σ i, i)
  rw [Matrix.det_apply]
  -- Only σ = 1 contributes; all other terms vanish.
  have hsum : ∑ σ : Equiv.Perm {v : V // v ≠ q}, Equiv.Perm.sign σ • ∏ i, M (σ i) i =
      ∏ i, M i i := by
    rw [Finset.sum_eq_single (1 : Equiv.Perm {v : V // v ≠ q})]
    · simp [Equiv.Perm.sign_one, Equiv.Perm.one_apply]
    · intro σ _ hσ
      have hprod : ∏ i, M (σ i) i = 0 := by
        show ∏ i, signedIncMatrix G (σ i).val ((edgeEmbedding T q) i) = 0
        exact prod_eq_zero_of_perm_ne_one T q σ hσ
      simp [hprod]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hsum]
  -- Each M(i, i) is ±1
  exact prod_pm_one _ (fun i => submatrix_diag_pm_one T q i)