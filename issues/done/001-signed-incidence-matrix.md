## Parent PRD

`issues/prd.md`

## What to build

Define the **signed incidence matrix** of a simple graph and its basic API. The signed incidence matrix is the foundation of the Matrix Tree Theorem proof — the Laplacian factors as `B_signed · B_signed^T`, and Cauchy-Binet is applied to the reduced version.

The matrix entry `B_signed[v][e]` is:
- `+1` if `v` is the endpoint of edge `e` with the smaller index (per `LinearOrder V`)
- `-1` if `v` is the endpoint of edge `e` with the larger index
- `0` if `v` is not incident to `e`

This canonical orientation (using `min`/`max` from `LinearOrder V`) avoids `Classical.choice` and keeps the matrix decidable — required for `#eval` smoke tests.

The reduced version `reducedSignedIncMatrix G q` drops the row for vertex `q` (the root), yielding a `(n-1) × m` matrix where `n = |V|` and `m = |Sym2 V|`.

## Acceptance criteria

- [ ] `signedIncMatrix` defined and compiles
- [ ] `signedIncMatrix_entry_fst` lemma: for edge `s(a,b)` with `a ≤ b`, `B[a][s(a,b)] = 1`
- [ ] `signedIncMatrix_entry_snd` lemma: for edge `s(a,b)` with `a ≤ b`, `B[b][s(a,b)] = -1`
- [ ] `signedIncMatrix_entry_not_incident` lemma: if `v` not incident to `e`, `B[v][e] = 0`
- [ ] `reducedSignedIncMatrix` defined and compiles
- [ ] `#eval` smoke test: confirm entries on a concrete edge of the house graph return expected `±1` / `0` values
- [ ] No `Classical.choice` or `Nonempty` in the definition path (required for `#eval` to work)

## Blocked by

None — can start immediately.

## User stories addressed

- User story 2: signed incidence matrix definition with simple API

## Implementation notes

- Requires `[LinearOrder V]`, `[DecidableEq V]`, `[DecidableRel G.Adj]`
- Use `Sym2.mem_iff` to check incidence, `min`/`max` for sign
- The existing `SignIncMatrix.lean` file has a placeholder that aliases `G.incMatrix ℤ` — replace it entirely
- The current `redSignIncMatrix` can be adapted once the signed version exists
