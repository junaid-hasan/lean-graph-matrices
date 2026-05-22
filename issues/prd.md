# PRD: Matrix Tree Theorem in Lean 4

## Problem Statement

The **Matrix Tree Theorem** (also known as Kirchhoff's theorem) is a fundamental result in algebraic graph theory: for a finite simple graph $G$ and any vertex $q$, the determinant of the reduced Laplacian matrix $L_0(G)$ equals the number of spanning trees of $G$. While this theorem is well-known in mathematics, it has **not been formalized in Mathlib**. This project aims to produce a complete, sorried-free formalization of the Matrix Tree Theorem in Lean 4, contributing both the theorem itself and any required supporting lemmas.

The current codebase has partial work (skeletons, sorried lemmas, experiments with Laplacian determinants on concrete graphs) but no completed proof. The goal is to reach **0 sorries** with a verified proof that compiles under the Lean 4 kernel.

## Solution

Formalize the Matrix Tree Theorem using the classical **Cauchy-Binet proof strategy**:

$$\det(L_0(G)) = \det(B_0 \cdot B_0^T) = \sum_{S} \det(B_0[S])^2 = \#\{\text{spanning trees}\}$$

The proof decomposes into five independent modules:

1. **Signed incidence matrix** — define a signed/oriented incidence matrix $B$ where each edge column has one $+1$ and one $-1$, and prove $L = B \cdot B^T$.
2. **Cauchy-Binet adapter** — leverage an existing complete proof of the Cauchy-Binet formula to express $\det(B_0 \cdot B_0^T)$ as a sum over minors.
3. **Spanning trees** — define spanning trees as a type and establish their basic combinatorial properties (including the existence of a leaf).
4. **Determinantal lemma** — prove that $\det(B_0[S]) \in \{0, \pm 1\}$, with $\pm 1$ exactly when the selected edges form a spanning tree.
5. **Main theorem assembly** — chain the lemmas together to produce the final result.

The proof uses existing Mathlib infrastructure for matrices, determinants, and graph theory, plus an existing external formalization of Cauchy-Binet.

## User Stories

1. As a mathematician, I want the Matrix Tree Theorem formalized in Lean 4, so that I can cite a machine-verified proof of this classical result.
2. As a Lean user, I want a `signedIncMatrix` definition with a simple API (entry lemmas), so that I can use signed incidence matrices without worrying about orientation choices.
3. As a Lean user, I want the identity `L = B * B^T` proved, so that the Laplacian can be factored as an incidence matrix product.
4. As a Lean user, I want a `SpanningTree` type with a `Fintype` instance, so that I can count spanning trees of any finite graph.
5. As a Lean user, I want the lemma that every spanning tree on ≥2 vertices has a leaf distinct from a chosen root, so that I can do induction on trees.
6. As a Lean user, I want the Cauchy-Binet formula available for matrices indexed by `Fin n` and `Fin m`, so that it can be applied to the reduced Laplacian.
7. As a Lean user, I want the determinantal lemma that $\det(B_0[S]) = \pm 1$ for spanning trees and $0$ otherwise, so that the Cauchy-Binet sum collapses to a count.
8. As a Lean user, I want `matrix_tree_theorem` as a theorem statement in the project, so that the result is immediately accessible.
9. As a project contributor, I want concrete computational tests on small graphs (triangle, house graph), so that I can sanity-check the proof against known values.
10. As a project contributor, I want hard sub-lemmas submitted to an automated theorem prover (Aristotle), so that the most tedious parts of the proof are handled automatically.

## Implementation Decisions

### Architectural decisions

- **Cauchy-Binet route, not deletion-contraction.** The deletion-contraction proof requires graph edge contraction (quotient types, type-changing induction), which is disproportionately hard in dependent type theory. The Cauchy-Binet route keeps vertex types fixed throughout and lives mostly in linear algebra, where Mathlib support is strongest.
- **Reuse faabian's Cauchy-Binet proof.** The `algebraic-combinatorics` project by faabian has a complete (0 sorries) proof of Cauchy-Binet for `Fin n` × `Fin m` matrices. Rather than re-proving it, the project will import or copy this proof and transport it via `det_submatrix_equiv_self` to the arbitrary fintype indices needed for the Matrix Tree Theorem.
- **Canonical orientation via `LinearOrder` min/max.** The signed incidence matrix orientation is defined deterministically: for each edge $\{a,b\}$ with $a \le b$, the smaller vertex gets $+1$ and the larger vertex gets $-1$. This avoids `Classical.choice` and keeps the matrix decidable.
- **`SpanningTree` structure, not edge-set counting.** The spanning tree type uses the `SpanningTree` structure (subgraph, subgraph relation, `IsTree` proof) already sketched in the codebase. The connection to counting uses `Fintype.card`.

### Module interfaces

- **Signed Incidence Matrix module:**
  - `signedIncMatrix G v e : ℤ` — returns `±1` if `v ∈ e` (sign by min/max order), `0` otherwise
  - `signedIncMatrix_entry_fst` / `signedIncMatrix_entry_snd` — entry lemmas for the two endpoints
  - `reducedSignedIncMatrix G q` — submatrix removing row `q`
  - `lapMatrix_eq_signedInc_mul_transpose` — the key identity $L = B_{\text{signed}} \cdot B_{\text{signed}}^T$

- **Cauchy-Binet Adapter module:**
  - Import faabian's `AlgebraicCombinatorics.CauchyBinet`
  - Thin transport lemma applying `det_submatrix_equiv_self` to bridge `Fin` and arbitrary fintypes

- **Spanning Tree module:**
  - `SpanningTree G` structure — `Tree`, `subG : Tree ≤ G`, `isTree : Tree.IsTree`
  - `Fintype (SpanningTree G)` instance
  - `exists_leaf` — every spanning tree on ≥2 vertices has a vertex of degree 1 ≠ root
  - `card_spanningTree_eq_finset_card` — equivalence between Fintype.card and Finset-based count

- **Determinantal Lemma module:**
  - `signedInc_det_tree` — if edges form a spanning tree, determinant is ±1 (proved by leaf induction)
  - `signedInc_det_nontree` — if edges do not form a spanning tree, determinant is 0
  - `signedInc_det_spanningTree` — corollary giving the `{0, ±1}` characterization

- **Main Theorem module:**
  - `matrix_tree_theorem` — the final statement: `det(L₀(G, q)) = (Fintype.card (SpanningTree G) : ℤ)`

### Technical clarifications

- The reduced Laplacian is defined on the type `{v : V // v ≠ q}` (vertices except the root), not on the full vertex set.
- `det_submatrix_equiv_self` already exists in Mathlib (`LinearAlgebra/Matrix/Determinant/Basic.lean`) and preserves determinant under reindexing by any equivalence.
- Mathlib already has `isTree_iff_connected_and_card` (in `Acyclic.lean`), which characterizes trees as connected graphs with $|V|-1$ edges. This will be used for decidability.
- Mathlib does **not** have a lemma that trees have leaves — this must be proved from scratch (longest path argument).
- The `AlgebraicCombinatorics` project (faabian) will be referenced as a local dependency or copied into the project. It is a separate Lean project that formalizes the textbook "Algebraic Combinatorics" by Grinberg.

### Project integration with automated provers

- The hard sub-lemma `det(B₀[S]) = 0` for non-tree edge sets will be submitted to **Aristotle** (Harmonic's cloud ATP for Lean 4) with an explicit proof sketch (cycle argument and disconnected forest argument).
- Aristotle has already successfully proved the helper sub-lemma `det_submatrix_eq_zero_of_not_injective` for this project.
- The toolchain version is set to `leanprover/lean4:v4.28.0` to match Aristotle's supported version.

## Testing Decisions

### What makes a good test

Tests should verify external behavior — that the theorems hold on concrete, computable examples — not implementation details. In Lean, this means `#eval` computations against known correct values.

### Modules that will be tested

- **Signed Incidence Matrix** — compute entries of `signedIncMatrix` for concrete edges and verify they match the expected $+1$, $-1$, or $0$ values.
- **Matrix Tree Theorem** — compute `det(reducedLapMatrix G q)` for concrete graphs and verify it equals the known number of spanning trees.

### Concrete test cases

The project already contains test infrastructure in `Example.lean` and `Basic.lean`:

- **Triangle ($K_3$):** 3 vertices, 3 edges. Reduced Laplacian determinant = 3. Number of spanning trees = 3. ✓
- **House graph:** 5 vertices (0–1–2–3–4–0 with chord 1–4), 6 edges. Reduced Laplacian determinant = 11. Number of spanning trees = 11. This test is already partially present and passes for `det = 11`. ✓
- **Additional test:** $K_4$ (complete graph on 4 vertices) — spanning trees = $4^2 = 16$ (Cayley's formula). Reduced Laplacian determinant should equal 16.

## Out of Scope

- **Cayley's formula** ($n^{n-2}$ spanning trees for $K_n$). Proving this requires a separate argument beyond the Matrix Tree Theorem and is not part of this PRD.
- **Generalizing the signed incidence matrix to arbitrary orientations.** Only the canonical orientation (min/max) is needed. A general `OrientedGraph` abstraction is future work for a Mathlib PR.
- **Proving total unimodularity of incidence matrices.** The determinantal lemma only needs the $\{0, \pm 1\}$ characterization for $(n-1) \times (n-1)$ submatrices, not the full TU property.
- **Deletion-contraction recurrence.** As decided, this route will not be pursued due to type-theoretic overhead.
- **Formalizing the Cauchy-Binet formula from scratch.** The faabian project's existing proof will be reused.
- **Weighted graphs or multigraphs.** Only simple graphs are in scope. The Laplacian is defined with entries in $\mathbb{Z}$.
- **The directed/edge-weighted Matrix Tree Theorem (Tutte's version).** Only the classical version for simple graphs.

## Further Notes

- The faabian `algebraic-combinatorics` project has 4000+ lines of Cauchy-Binet and determinant identities, all sorried-free. This is a significant existing asset that dramatically reduces the effort needed.
- The Clawristotle project (10 days, $6,300 API cost, 10K lines) provides a proven methodology for semi-autonomous formalization: run critique→plan→prove→submit-to-Aristotle loops with human steering at key decision points.
- The `lean-toolchain` has been downgraded from `v4.30.0-rc2` to `v4.28.0` to match Aristotle's supported version.
- The `lake-manifest.json` may need updating after the toolchain change to use compatible Mathlib versions.
- The `ForMathlib.lean` file may contain lemmas that have since been upstreamed to Mathlib and should be checked for name collisions (Aristotle already identified one such collision with `MultilinearMap.ext_ring`).
