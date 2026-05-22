## Parent PRD

`issues/prd.md`

## What to build

Prove the "non-tree direction" of the determinantal lemma: if a set of `n-1` edges does **not** form a spanning tree of `G`, then the determinant of the corresponding `(n-1) × (n-1)` submatrix of the reduced signed incidence matrix is `0`.

**Primary approach: submit to Aristotle**

Submit the lemma statement with an explicit proof sketch to Aristotle (Harmonic's cloud ATP for Lean 4). The proof sketch describes both sub-cases:

- **Case 1 (cycle):** The selected edges contain a cycle. Taking the signed sum of rows corresponding to the cycle vertices yields a nontrivial linear dependence among the rows (each edge in the cycle contributes cancelling ±1 entries). Thus the submatrix has linearly dependent rows → determinant = 0.

- **Case 2 (disconnected forest):** The selected edges are a forest but disconnected. There is a connected component that does not contain the root vertex `q`. The sum of rows for vertices in this component is zero (each edge in the component contributes +1 to one endpoint and -1 to the other, with no edges leaving the component). Linear dependence → determinant = 0.

**Fallback: manual proof**

If Aristotle fails to prove the lemma (returns `sorry` or disproves an incorrectly-stated version), implement the manual proof. The cycle case requires constructing an explicit cycle from a non-acyclic edge set, while the disconnected case requires reasoning about connected components. Estimated 150–250 lines.

## Acceptance criteria

- [ ] `signedInc_det_nontree` lemma: if `S` is a set of `n-1` edges that does not form a spanning tree of `G`, then `det(B₀[S]) = 0`
- [ ] Lemma compiles with 0 sorries
- [ ] If Aristotle proved it: no `sorry` remains, proof integrates cleanly
- [ ] If Aristotle failed: manual proof is complete and compiles
- [ ] `#eval` smoke test on a non-tree 3-edge subset of triangle edges (there are none — use a house graph subset that is not a tree): verify determinant = 0

## Blocked by

- Blocked by `issues/001-signed-incidence-matrix.md`
- Blocked by `issues/004-spanning-tree-fintype-leaf.md`

## User stories addressed

- User story 7: determinantal lemma (non-tree case)
- User story 10: Aristotle submission for hard sub-lemmas

## Implementation notes

### Aristotle submission guidance

The `aristotle submit` command should include:
- The full Lean statement
- The proof sketch (both cases) in natural language
- Reference to relevant Mathlib lemmas (`Matrix.det_eq_zero_of_row_eq`, cycle detection lemmas, `SimpleGraph.IsAcyclic`, etc.)
- The project directory for context

Example command:
```
uv run aristotle submit "Prove: if S : Finset (Sym2 V) has |S| = |V|-1 and does not form a spanning tree, then det(reducedSignedIncMatrix G q) = 0. [proof sketch follows]" --project-dir .
```

### Manual proof fallback details

If Aristotle cannot complete the proof:

- **Cycle detection:** Mathlib's `SimpleGraph.IsAcyclic` is defined as `∀ cycle, ¬cycle.IsCycle`. The negation gives a concrete cycle. Extract its vertex set and edge set.
- **Linear dependence for cycles:** For a cycle `v₁ - v₂ - ... - vₖ - v₁`, the alternating sum `row(v₁) - row(v₂) + row(v₃) - ... ± row(vₖ)` is zero because each column (edge) appears exactly twice with opposite signs.
- **Linear dependence for disconnected components:** Use `SimpleGraph.ConnectedComponent`. A component `C` not containing `q` has all its vertices in the reduced row set. Summing those rows gives zero.
- **Connecting to determinant:** `Matrix.det_eq_zero_of_row_eq` or `Matrix.det_eq_zero_of_sum_row_eq_zero`.

### Aristotle failure handling

- If Aristotle returns `sorry`: implement manual proof
- If Aristotle disproves the statement (returns a counterexample): the statement was incorrectly formalized — fix the statement and re-submit
- Track Aristotle job IDs for reference
