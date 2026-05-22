## Parent PRD

`issues/prd.md`

## What to build

Vendor the complete, sorried-free Cauchy-Binet proof from faabian's `algebraic-combinatorics` project into our project so it can be used as a dependency for the main theorem. The original project is Apache-licensed and compatible.

The vendored files are:
- `AlgebraicCombinatorics/CauchyBinet.lean` → `LeanGraphMatrices/CauchyBinet.lean` (~4000 lines)
- `AlgebraicCombinatorics/Determinants/PermFinset.lean` → `LeanGraphMatrices/PermFinset.lean` (transitive dependency, ~?? lines)

The import `import AlgebraicCombinatorics.Determinants.PermFinset` in CauchyBinet.lean must be changed to `import LeanGraphMatrices.PermFinset`. No other changes needed — both files are sorried-free.

Faabian's `cauchyBinet` theorem is stated for `Fin n` / `Fin m` matrices. A thin adapter lemma (in this issue or a follow-up) will transport it to arbitrary fintype indices via `det_submatrix_equiv_self`.

## Acceptance criteria

- [ ] `LeanGraphMatrices/CauchyBinet.lean` compiles with 0 errors
- [ ] `LeanGraphMatrices/PermFinset.lean` compiles with 0 errors
- [ ] Import works: `import LeanGraphMatrices.CauchyBinet` succeeds
- [ ] `AlgebraicCombinatorics.cauchyBinet` is accessible (namespaced or re-exported)
- [ ] Old `CauchyBinet.lean` file (with sorried `Matrix.det_mul'`) is removed or renamed to avoid collision
- [ ] Attribution comment added at top of vendored files referencing faabian's project and Apache license

## Blocked by

None — can start immediately.

## User stories addressed

- User story 6: Cauchy-Binet formula available for `Fin`-indexed matrices

## Implementation notes

- The faabian project source is at `~/work/lean/algebraic-combinatorics/`
- Both files import only Mathlib (no deeper vendor dependencies beyond PermFinset)
- The current `LeanGraphMatrices/CauchyBinet.lean` has sorried attempts at `Matrix.det_mul'` — archive or delete it
- The transport lemma (general fintype version) is a 30-line wrapper and can live in this file or in the main theorem assembly
- If the `PermFinset.lean` file conflicts with any existing module, rename it or place in a subdirectory
