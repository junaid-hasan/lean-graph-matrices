## Parent PRD

`issues/prd.md`

## What to build

Add concrete computational tests verifying the Matrix Tree Theorem on known graphs, and clean up dead code / sorries from the codebase.

**Tests:**

- Triangle ($K_3$): `det(L₀) = 3`, `Fintype.card (SpanningTree G) = 3`
- House graph: `det(L₀) = 11`, `Fintype.card (SpanningTree G) = 11`
- $K_4$: `det(L₀) = 16`, `Fintype.card (SpanningTree G) = 16` (Cayley's formula gives $4^2 = 16$)
- Edge case: single vertex graph — `det(L₀)` should be `1` (empty product), spanning trees = 1
- Edge case: disconnected graph (two triangles) — `det(L₀) = 0`, spanning trees = 0

**Cleanup:**
- Remove dead `#check`/`#eval` experiments from `Basic.lean`
- Remove or archive old sorried code (old `CauchyBinet.lean`, old `signIncMatrix` alias)
- Remove the `ForMathlim.lean` `MultilinearMap.ext_ring` if it collides with Mathlib
- Verify the module import chain (`LeanGraphMatrices.lean`) is correct
- Verify the project builds with `lake build` and 0 sorries across all files

## Acceptance criteria

- [ ] `#eval` confirms `det(L₀) = 3` for triangle, `11` for house, `16` for $K_4$
- [ ] `#eval` confirms `Fintype.card (SpanningTree G)` matches determinant for all test graphs
- [ ] Edge cases (single vertex, disconnected) produce correct results
- [ ] `lake build` succeeds with 0 errors
- [ ] `grep -r "sorry" LeanGraphMatrices/` returns empty (no remaining sorries)
- [ ] Dead code removed: no orphaned `#check`, no duplicated definitions
- [ ] `LeanGraphMatrices.lean` imports only the final, clean modules

## Blocked by

- Blocked by `issues/007-main-theorem-assembly.md`

## User stories addressed

- User story 9: concrete computational tests on small graphs

## Implementation notes

- The `Example.lean` file already has the house graph definition and `#eval` for determinant — extend it with spanning tree counting
- The `Basic.lean` file has triangle computations — clean and expand
- $K_4$ test: can be defined similarly to the existing triangle test using `completeGraph (Fin 4)`
- The `DecidableRel` instances for test graphs must be provided (they already exist in the codebase for house and triangle)
- Edge-case tests should be separate `example` blocks, not mixed into the main theorem file
- The `lean-toolchain` should stay at `v4.28.0` throughout
- If any `#eval` fails due to noncomputability, identify the offending definition and make it computable (remove `noncomputable`, eliminate `Classical.choice`)
