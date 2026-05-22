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

lemma treeParent_edge_injective (T : SpanningTree G) (q : V) :
    Function.Injective (fun (v : {v : V // v ≠ q}) => s(v.val, treeParent T q v)) := by
  intro x y h
  rcases Sym2.eq_iff.mp h with (⟨hxy, _⟩ | ⟨hxp, hpy⟩)
  · exact Subtype.ext hxy
  · let px := (T.isTree.existsUnique_path x.val q).exists.choose
    have hpx_isPath : px.IsPath := (T.isTree.existsUnique_path x.val q).exists.choose_spec
    have hpx0 : px.getVert 0 = x.val := px.getVert_zero
    have hpx1 : px.getVert 1 = y.val := by
      calc
        px.getVert 1 = treeParent T q x := rfl
        _ = y.val := hpy
    have hx_ne_q : x.val ≠ q := x.property
    let py := (T.isTree.existsUnique_path y.val q).exists.choose
    have hpy_isPath : py.IsPath := (T.isTree.existsUnique_path y.val q).exists.choose_spec
    have hpy1 : py.getVert 1 = x.val := by
      calc
        py.getVert 1 = treeParent T q y := rfl
        _ = x.val := hxp.symm
    let px_tail' : T.Tree.Walk y.val q := px.tail.copy hpx1 rfl
    have hpx_tail'_isPath : px_tail'.IsPath := by
      simpa [px_tail'] using hpx_isPath.tail
    have h_tail_eq_py : px_tail' = py :=
      (T.isTree.existsUnique_path y.val q).unique hpx_tail'_isPath hpy_isPath
    -- Helper lemma: changing start vertex via ▸ preserves getVert
    have h_getVert_inv {a a' b : V} (w : T.Tree.Walk a b) (h : a = a') (k : ℕ) :
        (h ▸ w).getVert k = w.getVert k := by
      subst h; rfl
    have hpx2_eq_x : px.getVert 2 = x.val := by
      calc
        px.getVert 2 = px.tail.getVert 1 := by simp
        _ = (px_tail' : T.Tree.Walk y.val q).getVert 1 := by
          dsimp [px_tail', Walk.copy]; rw [h_getVert_inv px.tail hpx1 1]
        _ = py.getVert 1 := by rw [h_tail_eq_py]
        _ = x.val := hpy1
    by_cases hlen2 : 2 ≤ px.length
    · have h_inj := hpx_isPath.getVert_injOn
      have h0le : (0 : ℕ) ≤ px.length := by omega
      have h2le : 2 ≤ px.length := hlen2
      have hvals : px.getVert 0 = px.getVert 2 := by rw [hpx0, hpx2_eq_x]
      apply h_inj (Set.mem_setOf.mpr h0le) (Set.mem_setOf.mpr h2le) at hvals
      omega
    · have hpast : px.getVert 2 = q := px.getVert_of_length_le (by omega)
      rw [hpast] at hpx2_eq_x
      exfalso; exact hx_ne_q hpx2_eq_x.symm

noncomputable def edgeEmbedding (T : SpanningTree G) (q : V) : {v : V // v ≠ q} ↪ Sym2 V :=
  ⟨fun v => s(v.val, treeParent T q v), treeParent_edge_injective T q⟩

/-! ## Leaf row has single non-zero entry -/

lemma leaf_row_single_nonzero (T : SpanningTree G) (q : V) (v : {v : V // v ≠ q})
    (hleaf : Nat.card (T.Tree.neighborSet v.val) = 1) (j : {v : V // v ≠ q}) (hj : j ≠ v) :
    signedIncMatrix G v.val ((edgeEmbedding T q) j) = 0 := by
  dsimp [edgeEmbedding]
  have hv_ne_jval : v.val ≠ j.val := by
    intro heq; exact hj (Subtype.ext heq.symm)
  by_cases h_eq_parent : v.val = treeParent T q j
  · have hadj_jv : T.Tree.Adj j.val v.val := by
      rw [h_eq_parent]
      exact treeParent_adj T q j
    have hncard1 : (T.Tree.neighborSet v.val).ncard = 1 := by
      rw [← Nat.card_coe_set_eq, hleaf]
    rcases Set.ncard_eq_one.mp hncard1 with ⟨u, hu⟩
    have hparent_mem : treeParent T q v ∈ T.Tree.neighborSet v.val := by
      rw [SimpleGraph.mem_neighborSet]
      exact treeParent_adj T q v
    have hj_mem : j.val ∈ T.Tree.neighborSet v.val := by
      rw [SimpleGraph.mem_neighborSet]
      exact hadj_jv.symm
    have hparent_eq_u : treeParent T q v = u := by
      rw [hu] at hparent_mem; simpa using hparent_mem
    have hj_eq_u : j.val = u := by
      rw [hu] at hj_mem; simpa using hj_mem
    have h_parent_eq_jval : treeParent T q v = j.val := by
      rw [hparent_eq_u, hj_eq_u]
    have h_edges_eq : s(v.val, treeParent T q v) = s(j.val, treeParent T q j) := by
      calc
        s(v.val, treeParent T q v) = s(v.val, j.val) := by rw [h_parent_eq_jval]
        _ = s(j.val, v.val) := Sym2.eq_swap (a := v.val) (b := j.val)
        _ = s(j.val, treeParent T q j) := by rw [h_eq_parent]
    exfalso
    exact hj (treeParent_edge_injective T q h_edges_eq).symm
  · apply signedIncMatrix_entry_not_incident G
    rw [mk'_mem_incidenceSet_iff]
    have hadj : G.Adj j.val (treeParent T q j) := T.subG (treeParent_adj T q j)
    refine fun h => ?_
    rcases h.2 with (h1 | h2)
    · exact hv_ne_jval h1
    · exact h_eq_parent h2

/-! ## Determinantal Lemma for Trees -/

/--
Helper lemma: if a row `r` of a matrix `M` (indexed by fintype `n`) has
`M r r = c` and `M r j = 0` for `j ≠ r`, then `det M = c * det M_sub`
where `M_sub` is the matrix with row `r` and column `r` removed.

PROVIDED SOLUTION
Use the Leibniz formula `det_apply`:
  det M = ∑ σ : Perm n, (sign σ : ℤ) • ∏ i, M (σ i) i

Split the sum into permutations fixing r and those not fixing r.

For σ NOT fixing r: let j := σ.symm r. Then j ≠ r (since σ r ≠ r).
The factor M (σ j) j = M r j = 0 by hzero. So the product is 0.

For σ fixing r: σ r = r, so M (σ r) r = M r r = c.
The permutations fixing r are in bijection with Perm {x // x ≠ r}
via `Perm.subtypeCongr (1 : Perm {x // x = r})`.

Define f : Perm {x // x ≠ r} → Perm n by
  f(τ) = Perm.subtypeCongr (1 : Perm {x // x = r}) τ
Then:
- sign (f τ) = sign τ (by `Equiv.Perm.sign_subtypeCongr`)
- For i = r: f τ r = r, factor = M r r = c
- For i ≠ r: f τ i = τ ⟨i, hi⟩ and the factor is M_sub (τ ⟨i, hi⟩) ⟨i, hi⟩
  where M_sub := M.submatrix Subtype.val Subtype.val

Thus (sign σ : ℤ) • ∏ i, M (σ i) i = (sign τ : ℤ) • (c • ∏ x, M_sub (τ x) x).
Summing over τ gives c * det M_sub.

Use `Finset.sum_bij` or `Finset.sum_equiv` with this bijection.
-/
lemma det_factor_row_single {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℤ) (r : n) (c : ℤ)
    (hdiag : M r r = c) (hzero : ∀ j, j ≠ r → M r j = 0) :
    M.det = c * ((Matrix.submatrix M (fun x : {x // x ≠ r} => x.val)
      (fun x : {x // x ≠ r} => x.val)).det) := by
  sorry

/-- The determinant of the reduced signed incidence submatrix for a spanning tree is ±1.

PROVIDED SOLUTION
Let I := {v : V // v ≠ q}, M := (reducedSignedIncMatrix G q).submatrix id (edgeEmbedding T q).
Induction on `Fintype.card V`.

Base case |V| ≤ 1: then I is empty (every vertex equals q). The determinant of the
empty matrix is 1. Return `Or.inl rfl`.

Inductive step |V| ≥ 2: use `exists_leaf` from issue 004 to get a leaf v ≠ q.
Let vi : I be the subtype element for v.

- By `leaf_row_single_nonzero`, M vi j = 0 for all j ≠ vi.
- The diagonal M vi vi = ±1 (by checking the linear order on V).
- Apply `det_factor_row_single` to get: det M = M[vi][vi] * det(minor)
  where minor is the submatrix with row vi and column vi removed.
- The minor is indexed by {x : I // x ≠ vi}, which is equivalent to
  {w : V // w ≠ q ∧ w ≠ v}. This corresponds to the tree T with v removed.
- Since removing a leaf yields a tree on |V|-1 vertices, the induction hypothesis
  (applied to the subgraph of T.Tree with vertex v deleted) gives det(minor) = ±1.
- Therefore det M = (±1) * (±1) = ±1.

For the induction to work, we need that the submatrix after removing vi
is exactly the matrix for the subtree (T without v). This follows because
edgeEmbedding restricted to vertices ≠ v is the same as the edgeEmbedding
for the subtree.
-/
theorem signedInc_det_tree (T : SpanningTree G) (q : V) :
    ((reducedSignedIncMatrix G q).submatrix id (edgeEmbedding T q)).det = 1 ∨
    ((reducedSignedIncMatrix G q).submatrix id (edgeEmbedding T q)).det = -1 := by
  sorry
