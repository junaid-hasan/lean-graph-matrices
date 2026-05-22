## Parent PRD

`issues/prd.md`

## What to build

Prove the "tree direction" of the determinantal lemma: if a set of `n-1` edges forms a spanning tree, then the determinant of the corresponding `(n-1) × (n-1)` submatrix of the reduced signed incidence matrix is `±1`.

**Proof by leaf induction:**

1. Base case: a tree on 2 vertices has 1 edge. The reduced incidence matrix (after removing the root row) is `1 × 1` with entry `±1`. Determinant = `±1`.

2. Inductive step: a tree on `n ≥ 2` vertices has a leaf `v ≠ q`. The row for `v` in the reduced incidence submatrix has exactly one non-zero entry (`±1`, at the column for its unique incident edge). Expand the determinant along this row — you get `±1` times the determinant of an `(n-2) × (n-2)` minor, which is the reduced incidence matrix for the tree with `v` and its edge removed (still a tree on `n-1` vertices). By induction, this minor has determinant `±1`.

The result is `det(B₀[S]) = 1 ∨ det(B₀[S]) = -1`.

## Acceptance criteria

- [ ] `signedInc_det_tree` lemma: if `T : SpanningTree G` and `B₀` is the reduced signed incidence matrix with root `q`, then `det(B₀.submatrix id (edgeEmbedding T)) = 1 ∨ det = -1`
- [ ] Lemma compiles with 0 sorries
- [ ] The proof uses `exists_leaf` from issue 004
- [ ] `#eval` smoke test on triangle: verify determinant of appropriate submatrix is `±1` (not `0`)

## Blocked by

- Blocked by `issues/001-signed-incidence-matrix.md` ✓ (completed)
- Blocked by `issues/004-spanning-tree-fintype-leaf.md` ✓ (completed)

## User stories addressed

- User story 7: determinantal lemma for spanning trees

## Progress notes (2026-05-22 iteration)

- [x] `treeParent_edge_injective`: fully proved using Walk.copy, IsPath.getVert_injOn, and path uniqueness
- [x] `leaf_row_single_nonzero`: fully proved using Set.ncard_eq_one (from Nat.card = 1) + treeParent_edge_injective
- [x] `edgeEmbedding`: defined via treeParent_edge_injective (noncomputable, uses walks)
- [ ] `det_factor_row_single`: STILL SORRIED. Key missing lemma: if a matrix row r has only M[r][r] ≠ 0, then det = M[r][r] * det(minor). Proof sketch: Leibniz formula + Perm.subtypeCongr bijection between permutations fixing r and permutations of I\{r}.
- [ ] `signedInc_det_tree`: STILL SORRIED. Will use det_factor_row_single + leaf induction on |V|.
- [ ] `#eval` smoke tests: not yet

## Implementation notes

- The `treeParent_edge_injective` proof uses a helper lemma `h_getVert_inv` for transporting getVert across a start-vertex equality. The core argument: if x = parent(y) and y = parent(x), then px.getVert 0 = px.getVert 2, contradicting IsPath.getVert_injOn.
- The `leaf_row_single_nonzero` proof uses `Nat.card_coe_set_eq` to convert the hleaf condition to Set.ncard, then Set.ncard_eq_one to get a singleton. The unique neighbor can't be both parent of v and j.val unless v = j.
- `det_factor_row_single` is a standard linear algebra lemma. The cleanest approach: use `det_apply` (Leibniz formula), split the sum over permutations into those fixing r and those not, show the non-fixing ones give 0, and use `Perm.subtypeCongr` to relate the fixing ones to permutations of I\{r}.
- `signedInc_det_tree` then follows by induction on card V: base case (empty index set → det=1), inductive step (find leaf, factor determinant, apply IH to minor).

## Next steps

1. Submit `det_factor_row_single` to Aristotle (cloud ATP) for automated proof
2. Once that compiles, complete `signedInc_det_tree` via induction
3. Add `#eval` smoke tests on triangle and house graph
