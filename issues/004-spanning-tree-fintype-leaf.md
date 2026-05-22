## Parent PRD

`issues/prd.md`

## What to build

Complete the `SpanningTree` infrastructure needed by the Matrix Tree Theorem:

1. **`Fintype (SpanningTree G)` instance** — every finite graph has finitely many spanning trees, so the type is fintype and `Fintype.card` gives the count. This requires decidability of `IsTree`, which Mathlib provides as `isTree_iff_connected_and_card` (connectivity and edge count are both decidable for finite graphs).

2. **`exists_leaf` lemma** — in any spanning tree on `≥2` vertices, for any chosen root vertex `q`, there exists a vertex `v ≠ q` of degree 1 (a leaf). This is proved by taking the longest path in the tree and noting its endpoints must have degree 1 (otherwise a longer path or a cycle would exist).

3. **`#eval` smoke test** — compute `Fintype.card (SpanningTree G)` for the triangle (expect 3) and house graph (expect 11).

## Acceptance criteria

- [ ] `Fintype (SpanningTree G)` instance compiles under `[Fintype V] [DecidableEq V] [Fintype G.edgeSet]`
- [ ] `#eval (Fintype.card (SpanningTree (triangle : SimpleGraph (Fin 3))))` returns `3`
- [ ] `#eval` returns `11` on house graph (or at minimum, the instance does not block `#eval`)
- [ ] `exists_leaf` lemma: if `T : SpanningTree G` and `Fintype.card V ≥ 2`, then `∃ v ≠ q, T.Tree.degree v = 1`
- [ ] `Decidable G.IsTree` instance is filled (currently sorried in `SpanningTree.lean`)
- [ ] `Decidable G.Connected` is filled or proven unnecessary for the `Fintype` instance

## Blocked by

None — can start immediately.

## User stories addressed

- User story 4: `Fintype` instance so spanning trees can be counted
- User story 5: `exists_leaf` lemma for tree induction

## Implementation notes

- Mathlib's `isTree_iff_connected_and_card` gives decidability: `IsTree` iff `Connected ∧ nat_card(edges) + 1 = nat_card(V)`, and both sides are decidable for finite graphs
- Mathlib's `Connected.exists_isTree_le` gives a spanning tree for any connected graph — useful for proving non-emptiness
- Mathlib has no `exists_leaf` lemma for trees — must be proved from scratch using the longest-path argument or via the edge-count characterization
- The existing `SpanningTree.lean` has a sorried `Fintype` instance and sorried `Decidable` instances — these should be completed, not replaced
- The `SpanningTree` structure has `subG : Tree ≤ G` and `isTree : Tree.IsTree` — these are the right fields
- Edge-case: empty graph (0 vertices) or single-vertex graph — `exists_leaf` should not be asserted vacuously. Consider restricting to `Fintype.card V ≥ 2` in the lemma statement
