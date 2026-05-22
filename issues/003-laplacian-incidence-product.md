## Parent PRD

`issues/prd.md`

## What to build

Prove the fundamental matrix factorization identity: the Laplacian matrix equals the signed incidence matrix times its transpose.

For the full Laplacian: `L = B_signed · (B_signed)^T`
For the reduced Laplacian: `L₀ = B₀_signed · (B₀_signed)^T`

The proof is a Finset-sum rewriting argument: each edge `{a,b}` contributes a rank-1 matrix whose `(a,a)` and `(b,b)` entries are `1`, and `(a,b)` and `(b,a)` entries are `-1`. Summing over all edges gives the degree matrix on the diagonal (sum of 1's = degree) and `-1` for adjacency entries on the off-diagonal — exactly the Laplacian `D - A`.

The reduced version follows from the full version by applying `Matrix.submatrix_mul` and the fact that the row/column restriction is a reindexing.

## Acceptance criteria

- [ ] `lapMatrix_eq_signedInc_mul_transpose` lemma proved for the full Laplacian
- [ ] `redLapMatrix_eq_reducedSignedInc_mul_transpose` lemma proved for the reduced Laplacian
- [ ] Both lemmas use `signedIncMatrix` from issue 001 (not the old `incMatrix` alias)
- [ ] `#eval` smoke test: compute both sides on the house graph and verify matrix equality
- [ ] The proof does not introduce new `sorry` statements

## Blocked by

- Blocked by `issues/001-signed-incidence-matrix.md`

## User stories addressed

- User story 3: identity `L = B * B^T` proved

## Implementation notes

- The existing `lapMatrix_incMatrix_prod` and `redLapMatrix_incMatrix_prod` in `MatrixTreeThm.lean` are sorried and use the wrong `incMatrix` — replace both
- The key sub-computation: for edge `e = s(a,b)` with `a ≤ b`, the outer product `B[:,e] ⊗ B[:,e]^T` has entries `(a,a)=1, (b,b)=1, (a,b)=-1, (b,a)=-1`
- Use `Finset.sum_congr` with `Sym2` induction (`Sym2.ind`) to decompose the sum over edges
- Mathlib's `Matrix.mul_apply` and `Matrix.transpose_apply` will be the main tools
- The reduced version can likely be proved via `Matrix.submatrix_mul` + `lapMatrix_eq_signedInc_mul_transpose`
