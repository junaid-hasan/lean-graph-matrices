## Parent PRD

`issues/prd.md`

## What to build

Assemble all the lemmas into the final Matrix Tree Theorem statement and proof:

$$\det(L_0(G, q)) = \#\{\text{spanning trees of } G\}$$

The proof chains together:

1. **Laplacian factorization** (issue 003): `L₀ = B₀ · B₀^T`
2. **Cauchy-Binet** (issue 002): `det(B₀ · B₀^T) = Σ_S det(B₀[S]) · det(B₀^T[S])`
3. **Simplification:** Since `det(B₀^T[S]) = det(B₀[S])`, each term is `det(B₀[S])²`
4. **Determinantal lemma** (issues 005, 006): `det(B₀[S])² = 1` if S is a spanning tree, `0` otherwise
5. **Counting:** The sum equals the number of spanning trees
6. **Equality:** `det(L₀) = (Fintype.card (SpanningTree G) : ℤ)`

The proof is a single chain of `rw` and `calc` statements — the heavy lifting was done in the earlier issues. This issue is about connecting the pieces correctly.

## Acceptance criteria

- [ ] `matrix_tree_theorem` lemma compiles with 0 sorries
- [ ] Statement: `∀ q : V, det (redLapMatrix G q) = (Fintype.card (SpanningTree G) : ℤ)`
- [ ] The proof is a single `calc` block (or equivalent chain) referencing lemmas from issues 001–006
- [ ] All `sorry` stubs in `MatrixTreeThm.lean` are resolved (not just `matrix_tree_theorem` — also the helper sorries if any remain)
- [ ] `#eval` smoke test: compute `det(L₀)` for triangle (expect 3) and house graph (expect 11)

## Blocked by

- Blocked by `issues/002-vendor-cauchy-binet.md`
- Blocked by `issues/003-laplacian-incidence-product.md`
- Blocked by `issues/005-det-tree-plus-minus-one.md`
- Blocked by `issues/006-det-nontree-zero.md`

## User stories addressed

- User story 8: `matrix_tree_theorem` as an accessible theorem statement

## Implementation notes

- The type of the sum in faabian's Cauchy-Binet uses `Finset.powersetCard n (Finset.univ : Finset (Fin m))`. The transport to arbitrary fintypes requires:
  1. Fix an equivalence `e : V\{q} ≃ Fin (|V|-1)` via `Fintype.equivFin`
  2. Reindex the reduced Laplacian via `det_submatrix_equiv_self e`
  3. Apply the Fin-version of Cauchy-Binet
  4. Translate the sum back through the equivalence
- The counting step (`Σ_S det² = #trees`) requires a bijection between the `powersetCard` sum index and actual `SpanningTree` values. This may need a small lemma proving that `Finset.filter (λ S => IsTree (fromEdgeSet S)) (powersetCard (|V|-1) edgeFinset)` is in bijection with `SpanningTree G`.
- The `redLapMatrix` in `MatrixTreeThm.lean` currently uses `{v : V // v ≠ q}` as the index type — this is correct and should be preserved
- The old `spanningTreeFinset` definition (all `(n-1)`-subsets) is wrong and should be replaced with `Fintype.card (SpanningTree G)`
- The `redSignIncMatrix` definition should use the new `signedIncMatrix` from issue 001
