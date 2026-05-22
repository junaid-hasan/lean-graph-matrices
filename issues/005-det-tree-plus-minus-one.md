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

- Blocked by `issues/001-signed-incidence-matrix.md`
- Blocked by `issues/004-spanning-tree-fintype-leaf.md`

## User stories addressed

- User story 7: determinantal lemma for spanning trees

## Implementation notes

- The leaf row has a single non-zero entry — use `Matrix.det_expand_row` or expand via Laplace expansion
- After removing the leaf and its edge, the remaining subgraph is still a tree — this follows because removing a leaf from a tree produces a tree
- The sign (±1) comes from the row/column index of the leaf — don't need to determine the exact sign, just that it's ±1
- The `edgeEmbedding` function (extracting an order-embedding of edges from a spanning tree) may need to be defined or adapted from the existing `edgeChoiceGraph` in `MatrixTreeThm.lean`
- The induction can use `Nat` recursion on `Fintype.card V` or structural induction on the tree itself
- Need to handle the `n=1` edge case (single vertex, no edges): the reduced Laplacian is `0×0`, determinant = 1 (empty product). There are no leaves, but the statement is vacuously true since `|V|-1 = 0` edges
