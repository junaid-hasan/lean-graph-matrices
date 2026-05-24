# Blueprint: Kirchhoff's Matrix-Tree Theorem (Cauchy-Binet Proof)

## TL;DR

### File Hierarchy

```
┌─────────────────────────────────────────────────────────────────────┐
│                    LeanGraphMatrices.lean (root)                    │
│  imports: Basic, CauchyBinet, SignIncMatrix, MatrixTreeThm,        │
│           SpanningTree, TreeDet, NonTreeDet                        │
└─────────────────────────────────────────────────────────────────────┘
                                  │
                    ┌─────────────┴─────────────┐
                    │                           │
                    ▼                           ▼
┌──────────────────────────────┐
│        Basic.lean            │
│  (test code, not proof)      │
│  NOT used by any proof file  │
└──────────────────────────────┘
                                                │
                                                ▼
                              ┌──────────────────────────────────────┐
                              │         CauchyBinet.lean             │
                              │  (adapted: cauchyBinet theorem)      │
                              │  225 lines                           │
                              └──────────────┬───────────────────────┘
                                             │
┌──────────────────────┐  ┌─────────────────┐│
│  SignIncMatrix.lean  │  │SpanningTree.lean ││
│  (signed incidence   │  │(SpanningTree     ││
│   matrix, L = B\u00b7B\u1d40)  │  │ structure +      ││
│  ──────────────────  │  │ Finite/Fintype)  ││
│  defs: 2             │  │ ───────────────  ││
│  lemmas: 8           │  │ defs: 1          ││
│                      │  │ instances: 2     ││
└────────┬─────────────┘  └────────┬─────────┘│
         │                         │           │
         │    ┌────────────────────┘           │
         │    │                                │
         ▼    ▼                                │
┌───────────────────┐  ┌───────────────────┐   │
│   TreeDet.lean     │  │  NonTreeDet.lean   │   │
│  (tree det = \u00b11)   │  │  (non-tree det = 0)│   │
│  ────────────────  │  │  ───────────────── │   │
│  defs: 4           │  │  defs: 1           │   │
│  lemmas: 9          │  │  lemmas: 7         │   │
│  theorem: 1        │  │  theorem: 1        │   │
│  (signedInc_det_   │  │  (signedInc_det_   │   │
│   tree)            │  │   nontree)         │   │
└────────┬───────────┘  └────────┬───────────┘   │
         │                       │               │
         │    ┌──────────────────┘               │
         │    │                                  │
         ▼    ▼                                  ▼
┌──────────────────────────────────────────────────────────────────┐
│                    MatrixTreeThm.lean                             │
│  ─────────────────────────────────────────────                   │
│  defs: 3    (redLapMatrix, spanningTreeToEdgeFinset,             │
│               spanningTree_equiv_edgeFinset)                     │
│  lemmas: 15  (Cauchy-Binet bridge, submatrix helpers,            │
│               sum classification, cardinality)                   │
│  theorem: 1  ──►  matrix_tree_theorem  ◄──                      │
│                                                                  │
│  det(L\u2080) = #{spanning trees of G}                               │
└──────────────────────────────────────────────────────────────────┘
```

### Proof Chain (4 Steps)

```
  SignIncMatrix  ──►  L\u2080 = B\u2080\u00b7B\u2080\u1d40
         +
  CauchyBinet    ──►  det(B\u2080\u00b7B\u2080\u1d40) = \u03a3|T|=|V|-1 det(B\u2080[:,T])\u00b2
         +
  TreeDet        ──►  if T forms tree:  det(B\u2080[:,T])\u00b2 = 1
  NonTreeDet     ──►  if T not tree:    det(B\u2080[:,T])\u00b2 = 0
         +
  SpanningTree   ──►  \u03a3 1 over trees = Fintype.card (SpanningTree G)
         =
  MatrixTreeThm  ──►  det(L\u2080) = #{spanning trees}
```

---

## Project Overview

**Goal:** Formally prove that for any finite simple graph `G` and any vertex `q`,
`det(L₀) = #{spanning trees of G}`, where `L₀` is the reduced Laplacian (row `q`
and column `q` removed).

**Proof strategy:** Cauchy-Binet approach (matching the LaTeX notes):

1. Factor the Laplacian as a signed incidence matrix: `L = B·Bᵀ`
2. Apply Cauchy-Binet to `det(L₀) = det(B₀·B₀ᵀ)`
3. Classify each term `det(B₀[:,T])²` as `1` (if `T` forms a spanning tree) or `0` (otherwise)

**Dependencies:** Mathlib v4.28.0 (general graph theory, matrices, determinants, `SimpleGraph.IsTree`)
plus an adapted Cauchy-Binet proof from `faabian/algebraic-combinatorics`.

---

## File Map

```
LeanGraphMatrices/
├── LeanGraphMatrices.lean          — root imports
├── Basic.lean                      — test definitions, not part of the proof
├── SignIncMatrix.lean              — signed incidence matrix, L = B·Bᵀ
├── SpanningTree.lean               — SpanningTree structure, Fintype instance
├── CauchyBinet.lean                — adapted Cauchy-Binet formula (225 lines)
├── SignIncMatrix.lean              — signed incidence matrix, L = B·Bᵀ
├── TreeDet.lean                    — tree determinant = ±1
├── NonTreeDet.lean                 — non-tree determinant = 0
└── MatrixTreeThm.lean              — main theorem + Cauchy-Binet bridge
```

---

## 1. SignIncMatrix.lean — Signed Incidence Matrix

### Context
```lean
variable {V : Type} [LinearOrder V] [DecidableEq V] (G : SimpleGraph V)
variable [DecidableRel G.Adj]
```

Assets required: `LinearOrder V` (to orient edges canonically as min→max).

---

### 1.1 Definition: `signedIncMatrix`

```lean
def signedIncMatrix : Matrix V (Sym2 V) ℤ :=
  fun v e => Sym2.lift ⟨(fun a b =>
    if G.Adj a b then
      if v = min a b then 1 else if v = max a b then -1 else 0
    else 0), ...⟩ e
```

**English:** For vertex `v` and unordered edge `e = s(a,b)`:
- `+1` if `v` is the **smaller** endpoint (per `LinearOrder V`)
- `-1` if `v` is the **larger** endpoint
- `0` if `v` is not incident to `e`

This is well-defined on `Sym2 V` because the `min`/`max` are symmetric under swapping `(a,b)`.

**Matches LaTeX:** `B ∈ ℤ^{|V|×|E|}`, one column per edge with exactly one +1 and one -1.

---

### 1.2 Lemma: `signedIncMatrix_entry_fst`

```lean
lemma signedIncMatrix_entry_fst {x y : V} (h : G.Adj x y) (hle : x ≤ y) :
    signedIncMatrix G x s(x,y) = 1
```

**English:** If `x ≤ y` and they're adjacent, the entry at row `x` and edge `s(x,y)` is `+1`.

---

### 1.3 Lemma: `signedIncMatrix_entry_snd`

```lean
lemma signedIncMatrix_entry_snd {x y : V} (h : G.Adj x y) (hle : x ≤ y) :
    signedIncMatrix G y s(x,y) = -1
```

**English:** If `x ≤ y` and they're adjacent, the entry at row `y` and edge `s(x,y)` is `-1`.

---

### 1.4 Lemma: `signedIncMatrix_entry_not_incident`

```lean
lemma signedIncMatrix_entry_not_incident {v : V} {e : Sym2 V} (h : e ∉ G.incidenceSet v) :
    signedIncMatrix G v e = 0
```

**English:** If edge `e` is not incident to vertex `v`, the entry is `0`.

---

### 1.5 Definition: `reducedSignedIncMatrix`

```lean
def reducedSignedIncMatrix (q : V) : Matrix ({v : V // v ≠ q}) (Sym2 V) ℤ :=
  (signedIncMatrix G).submatrix (fun x => x.val) id
```

**English:** \(B_0\) — the signed incidence matrix with row `q` deleted. Rows indexed by `{v : V // v ≠ q}`.

**Matches LaTeX:** \(B[i]\) (drop row `i`).

---

### 1.6 Lemma: `signedIncMatrix_sq_eq_incMatrix`

```lean
lemma signedIncMatrix_sq_eq_incMatrix (i : V) (e : Sym2 V) :
    (signedIncMatrix G i e)^2 = (G.incMatrix ℤ) i e
```

**English:** Squaring the signed incidence matrix entry gives the unoriented incidence matrix entry (±1² = 1 = indicator). Both are `1` if `e` is incident to `i`, `0` otherwise.

---

### 1.7 Lemma: `signedIncMatrix_mul_of_adj`

```lean
lemma signedIncMatrix_mul_of_adj {i j : V} (hij : i ≠ j) (hadj : G.Adj i j) (e : Sym2 V) :
    signedIncMatrix G i e * signedIncMatrix G j e =
    if e = s(i, j) then (-1 : ℤ) else 0
```

**English:** For distinct adjacent vertices `i,j`, the product `B(i,e)·B(j,e)` is `-1` if `e = s(i,j)`, and `0` otherwise (the two signs cancel if the edge matches the pair).

---

### 1.8 Lemma: `signedIncMatrix_mul_of_not_adj`

```lean
lemma signedIncMatrix_mul_of_not_adj {i j : V} (hij : i ≠ j) (hnadj : ¬ G.Adj i j) (e : Sym2 V) :
    signedIncMatrix G i e * signedIncMatrix G j e = 0
```

**English:** For distinct non-adjacent vertices, the product of entries for any edge is always `0` (no edge is incident to both).

---

### 1.9 Lemma: `lapMatrix_eq_signedInc_mul_transpose`

```lean
lemma lapMatrix_eq_signedInc_mul_transpose :
    G.lapMatrix ℤ = signedIncMatrix G * (signedIncMatrix G)ᵀ
```

**English:** The Laplacian matrix equals `B·Bᵀ`, where `B` is the signed incidence matrix.

Off-diagonal `(i,j)`: product gives `-1` if `s(i,j)` is an edge, `0` otherwise.
Diagonal `(i,i)`: sum of squares = degree.

**Matches LaTeX:** `L_G = B B^T`.

---

### 1.10 Lemma: `redLapMatrix_eq_reducedSignedInc_mul_transpose`

```lean
lemma redLapMatrix_eq_reducedSignedInc_mul_transpose (q : V) :
    (G.lapMatrix ℤ).submatrix (Subtype.val) (Subtype.val) = reducedSignedIncMatrix G q * (reducedSignedIncMatrix G q)ᵀ
```

**English:** The **reduced** Laplacian equals `B₀·B₀ᵀ`, where `B₀` is the reduced signed incidence matrix (drop row `q`). This follows directly from the full version by restricting rows/columns.

**Matches LaTeX:** `L_G[i] = B[i]·B[i]ᵀ`.

---

## 2. SpanningTree.lean — Spanning Tree Structure

### Context
```lean
variable {V : Type} [Fintype V] [DecidableEq V]
```

---

### 2.1 Structure: `SpanningTree`

```lean
structure SpanningTree (G : SimpleGraph V) where
  Tree : SimpleGraph V
  subG : Tree ≤ G
  isTree : Tree.IsTree
```

**English:** A **spanning tree** of `G` is:
- `Tree` — a graph on the **same vertex set** `V`
- `subG` — every edge of `Tree` is an edge of `G` (`Tree ≤ G` is edge-subgraph containment)
- `isTree` — `Tree.IsTree` (connected + acyclic)

Since `Tree : SimpleGraph V`, the vertex set is exactly `V`, so it spans all vertices.

**Mathlib `IsTree` definition:** "connected and acyclic", equivalent to "connected with `|E| = |V| - 1`".

---

### 2.2 Instance: `finiteSpanningTree`

```lean
instance finiteSpanningTree (G : SimpleGraph V) : Finite (SpanningTree G)
```

**English:** The set of spanning trees of a finite graph is finite. (Injective map: `SpanningTree G → SimpleGraph V` via `Tree`.)

---

### 2.3 Instance: `fintypeSpanningTree`

```lean
noncomputable instance fintypeSpanningTree (G : SimpleGraph V) : Fintype (SpanningTree G)
```

**English:** The set of spanning trees carries a `Fintype` instance (noncomputable, via `Fintype.ofFinite`).

---

## 3. TreeDet.lean — Determinant of Tree Submatrix

### Context
```lean
variable {V : Type} [Fintype V] [LinearOrder V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj]
```

Depends on: `SignIncMatrix`, `SpanningTree`, Mathlib (walks, paths, determinants).

---

### 3.1 Definition: `treeParent`

```lean
noncomputable def treeParent (T : SpanningTree G) (q : V) (v : {v : V // v ≠ q}) : V :=
  let p := (T.isTree.existsUnique_path v.val q).exists.choose
  p.getVert 1
```

**English:** For a rooted spanning tree with root `q`, the **parent** of a non-root vertex `v ≠ q` is the second vertex on the **unique** simple path from `v` to `q`. That is, `parent(v)` is the neighbor of `v` that lies one step closer to `q`.

**Uses:** `T.isTree.existsUnique_path` — trees have unique simple paths between any two vertices.

---

### 3.2 Lemma: `treeParent_adj`

```lean
lemma treeParent_adj (T : SpanningTree G) (q : V) (v : {v : V // v ≠ q}) :
    T.Tree.Adj v.val (treeParent T q v)
```

**English:** The parent is adjacent to the child in the tree.

---

### 3.3 Lemma: `treeParent_edge_mem`

```lean
lemma treeParent_edge_mem (T : SpanningTree G) (q : V) (v : {v : V // v ≠ q}) :
    s(v.val, treeParent T q v) ∈ T.Tree.edgeSet
```

**English:** The unordered edge `s(v, parent(v))` is in the tree's edge set.

---

### 3.4 Lemma: `treeParent_edge_injective`

```lean
lemma treeParent_edge_injective (T : SpanningTree G) (q : V) :
    Function.Injective (fun (v : {v : V // v ≠ q}) => s(v.val, treeParent T q v))
```

**English:** The map `v ↦ s(v, parent(v))` from non-root vertices to tree edges is **injective**. If two vertices produce the same undirected edge, they must be the same vertex (by uniqueness of paths in a tree).

---

### 3.5 Definition: `edgeEmbedding`

```lean
noncomputable def edgeEmbedding (T : SpanningTree G) (q : V) : {v : V // v ≠ q} ↪ Sym2 V :=
  ⟨fun v => s(v.val, treeParent T q v), treeParent_edge_injective T q⟩
```

**English:** The injection from non-root vertices `{v // v ≠ q}` to undirected edges, sending each `v` to its parent edge `s(v, parent(v))`. Since there are `|V|-1` non-root vertices and a tree on `|V|` vertices has `|V|-1` edges, this is a **bijection** onto the tree's edge set.

---

### 3.6 Lemma: `submatrix_entry_eq_zero_of_not_endpoint`

```lean
lemma submatrix_entry_eq_zero_of_not_endpoint (T : SpanningTree G) (q : V)
    (w i : {v : V // v ≠ q}) (hw1 : w.val ≠ i.val) (hw2 : w.val ≠ treeParent T q i) :
    signedIncMatrix G w.val ((edgeEmbedding T q) i) = 0
```

**English:** In the submatrix `B₀[:, edgeEmbedding T q]`, the entry at row `w`, column `i` is `0` unless `w.val` is an endpoint of the edge `s(i.val, parent(i))`. That is, non-endpoint entries are zero.

---

### 3.7 Lemma: `submatrix_diag_pm_one`

```lean
lemma submatrix_diag_pm_one (T : SpanningTree G) (q : V) (i : {v : V // v ≠ q}) :
    signedIncMatrix G i.val ((edgeEmbedding T q) i) = 1 ∨
    signedIncMatrix G i.val ((edgeEmbedding T q) i) = -1
```

**English:** The diagonal entry `M(i,i)` of the tree submatrix is `±1`, since `i.val` is an endpoint of the edge `s(i.val, parent(i))` (by `treeParent_adj`).

---

### 3.8 Definition: `treeDepth`

```lean
noncomputable def treeDepth (T : SpanningTree G) (q : V) (v : {v : V // v ≠ q}) : ℕ :=
  (T.isTree.existsUnique_path v.val q).exists.choose.length
```

**English:** The **depth** of a non-root vertex — the length (= number of edges) of the unique path from `v` to `q` in the tree.

---

### 3.9 Lemma: `treeDepth_pos`

```lean
lemma treeDepth_pos (T : SpanningTree G) (q : V) (v : {v : V // v ≠ q}) : 0 < treeDepth T q v
```

**English:** Depth is positive for any non-root vertex (path length > 0 since `v ≠ q`).

---

### 3.10 Lemma: `treeParent_eq_q_of_depth_one`

```lean
lemma treeParent_eq_q_of_depth_one (T : SpanningTree G) (q : V) (v : {v : V // v ≠ q})
    (hd : treeDepth T q v = 1) : treeParent T q v = q
```

**English:** If `v` is at depth 1 (adjacent to the root), its parent **is** the root `q`.

---

### 3.11 Lemma: `perm_eq_id_of_endpoint_condition` ⭐

```lean
lemma perm_eq_id_of_endpoint_condition (T : SpanningTree G) (q : V)
    (σ : Equiv.Perm {v : V // v ≠ q})
    (h : ∀ i, (σ i).val = i.val ∨ (σ i).val = treeParent T q i) : σ = 1
```

**English:** If `σ` is a permutation of the non-root vertices such that for every `i`, `σ(i)` is either `i` itself or the **parent** of `i`, then `σ` must be the identity permutation.

**Why this is true:** Suppose `σ` moves some vertex. Pick a moved vertex `v₀` with **minimum depth**. Since `σ(v₀) ≠ v₀`, we must have `σ(v₀) = parent(v₀)` (by the endpoint condition). But `parent(v₀)` has strictly smaller depth. By minimality of `v₀`, `σ(parent(v₀)) = parent(v₀)`. But then `σ(v₀) = parent(v₀) = σ(parent(v₀))`, contradicting injectivity unless `v₀ = parent(v₀)`, which would mean depth 0 — impossible since `v₀ ≠ q`.

This is the **key combinatorial lemma** for the tree determinant proof.

---

### 3.12 Lemma: `prod_eq_zero_of_perm_ne_one`

```lean
lemma prod_eq_zero_of_perm_ne_one (T : SpanningTree G) (q : V)
    (σ : Equiv.Perm {v : V // v ≠ q}) (hσ : σ ≠ 1) :
    ∏ i, signedIncMatrix G (σ i).val ((edgeEmbedding T q) i) = 0
```

**English:** For any non-identity permutation `σ`, the Leibniz product `∏_i M(σ(i), i)` is zero. This follows from `perm_eq_id_of_endpoint_condition`: if `σ ≠ 1`, there exists `i` where `σ(i)` is not an endpoint of the edge at column `i`, making that entry zero.

---

### 3.13 Lemma: `prod_pm_one`

```lean
lemma prod_pm_one {ι : Type*} [Fintype ι] (f : ι → ℤ) (hf : ∀ i, f i = 1 ∨ f i = -1) :
    (∏ i, f i) = 1 ∨ (∏ i, f i) = -1
```

**English:** A product of `±1` integers is always ±1.

---

### 3.14 Theorem: `signedInc_det_tree` ⭐

```lean
theorem signedInc_det_tree (T : SpanningTree G) (q : V) :
    ((reducedSignedIncMatrix G q).submatrix id (edgeEmbedding T q)).det = 1 ∨
    ((reducedSignedIncMatrix G q).submatrix id (edgeEmbedding T q)).det = -1
```

**English:** The determinant of the submatrix `B₀[:, edgeEmbedding T q]` is `±1`.

**Proof sketch:**
1. Expand determinant via Leibniz formula: `det M = Σ_σ sign(σ) · ∏_i M(σ(i), i)`
2. All `σ ≠ 1` terms vanish (Lemma 3.12: `prod_eq_zero_of_perm_ne_one`)
3. Only the identity term remains: `det M = ∏_i M(i,i)`
4. Each diagonal entry is ±1 (Lemma 3.7)
5. Product of ±1's is ±1 (Lemma 3.13)

**Matches LaTeX Lemma:** "If S is a spanning tree, `|det(B_S[i])| = 1`"

---

## 4. NonTreeDet.lean — Determinant of Non-Tree Submatrix

### Context
```lean
variable {V : Type} [Fintype V] [LinearOrder V] [DecidableEq V]
```

Depends on: `SignIncMatrix`, `SpanningTree`, Mathlib (connectivity, walks, determinants).

---

### 4.1 Definition: `edgeGraph`

```lean
def edgeGraph (q : V) (S : {v : V // v ≠ q} ↪ Sym2 V) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (Set.range S)
```

**English:** Given an injection `S` selecting `|V|-1` edges, `edgeGraph q S` is the graph on `V` whose edge set is exactly `range S`. (The parameter `q` is unused but present for symmetry.)

---

### 4.2 Lemma: `det_zero_of_sum_rows_eq_zero`

```lean
lemma det_zero_of_sum_rows_eq_zero {n : Type*} [DecidableEq n] [Fintype n]
    {R : Type*} [CommRing R] (A : Matrix n n R)
    (S : Finset n) (hne : S.Nonempty) (hsum : ∀ j : n, ∑ i ∈ S, A i j = 0) : A.det = 0
```

**English:** If a nonempty set of rows of a square matrix sums to the zero vector (column-wise), then the determinant is zero.

**Proof:** Pick any row `v₀ ∈ S`. Repeatedly add all other rows in `S` to row `v₀`; each addition preserves det. The resulting `v₀`-th row is zero, so det = 0.

---

### 4.3 Lemma: `edgeGraph_not_tree_not_connected`

```lean
lemma edgeGraph_not_tree_not_connected (hNotTree : ¬ (edgeGraph q S).IsTree) :
    ¬ (edgeGraph q S).Connected
```

**English:** If a graph `H = edgeGraph q S` (on `|V|` vertices with `|V|-1` edges) is **not** a tree, then `H` is **disconnected**.

**Proof sketch:** 
- `|E(H)| ≤ |V|-1` (edge set ⊆ image of S, and `|S| = |V|-1`)
- If `H` were connected, it would contain a spanning tree with `|V|-1` edges
- So `|E(H)| ≥ |V|-1`, hence equality: `|E(H)| = |V|-1`
- A connected graph with `|V|-1` edges is a tree (`isTree_iff_connected_and_card`)
- Contradiction.

---

### 4.4 Lemma: `exists_unreachable_from_root`

```lean
lemma exists_unreachable_from_root (H : SimpleGraph V) [DecidableRel H.Adj]
    (q : V) (hNotConn : ¬ H.Connected) : ∃ u : V, ¬ H.Reachable q u
```

**English:** If a graph is disconnected, there exists a vertex `u` that is **not reachable** from `q`.

---

### 4.5 Lemma: `signedIncMatrix_col_sum_eq_zero`

```lean
lemma signedIncMatrix_col_sum_eq_zero (e : Sym2 V) : ∑ v : V, signedIncMatrix G v e = 0
```

**English:** For any edge `e`, the sum of entries across all vertices is `0` (the `+1` and `-1` cancel).

---

### 4.6 Lemma: `signedIncMatrix_support_subset_endpoints`

```lean
lemma signedIncMatrix_support_subset_endpoints (e : Sym2 V) (v : V)
    (hv : signedIncMatrix G v e ≠ 0) : v ∈ e
```

**English:** If `signedIncMatrix G v e ≠ 0`, then `v` is an endpoint of `e`.

---

### 4.7 Lemma: `reachable_of_adj_reachable`

```lean
lemma reachable_of_adj_reachable (H : SimpleGraph V) (u a b : V)
    (hadj : H.Adj a b) (hreach : H.Reachable u a) : H.Reachable u b
```

**English:** If `a` is reachable from `u` and `a,b` are adjacent, then `b` is also reachable from `u`.

---

### 4.8 Lemma: `signedIncMatrix_sum_over_reachable_component_eq_zero`

```lean
lemma signedIncMatrix_sum_over_reachable_component_eq_zero (q : V) (S : ...) (u : V) (j : ...) :
    ∑ v ∈ Finset.univ.filter (fun w => (edgeGraph q S).Reachable u w),
      signedIncMatrix G v (S j) = 0
```

**English:** For any edge `e = S j` and any vertex `u`, the sum of signed incidence entries over the **reachable component** of `u` (in the graph `edgeGraph q S`) is zero.

**Proof:** If `e = s(a,b)`, both endpoints are in the same reachable component (if one is reachable, the other is). So the `+1` and `-1` both appear in the sum or neither does. Either way, the sum is 0.

---

### 4.9 Theorem: `signedInc_det_nontree` ⭐

```lean
theorem signedInc_det_nontree (q : V) (S : {v : V // v ≠ q} ↪ Sym2 V)
    (hNotTree : ¬ (edgeGraph q S).IsTree) :
    ((reducedSignedIncMatrix G q).submatrix id S).det = 0
```

**English:** If an edge selection `S` of `|V|-1` edges does **not** form a spanning tree, then `det(B₀[:, S]) = 0`.

**Proof sketch:**
1. Not a tree → disconnected (Lemma 4.3)
2. There exists a vertex `u` unreachable from `q` (Lemma 4.4)
3. Define `T` = rows corresponding to the reachable component of `u`
4. For each column `j`, the sum of entries over rows in `T` is `0` (Lemma 4.8)
5. Apply `det_zero_of_sum_rows_eq_zero` (Lemma 4.2): a nonempty set of rows summing to zero forces det = 0

Key insight: since `q` is **not** in the reachable component of `u` (we chose `u` unreachable from `q`), all rows in `T` map to vertices `≠ q`, so they correspond to valid rows in the reduced matrix.

**Matches LaTeX Lemma:** "If S is not a spanning tree, `det(B_S[i]) = 0`"

---

## 5. MatrixTreeThm.lean — Main Theorem

### Context
```lean
variable {V : Type} [Fintype V] [LinearOrder V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
```

Depends on: `CauchyBinet`, `SignIncMatrix`, `TreeDet`, `NonTreeDet`, `SpanningTree`.

---

### 5.1 Definition: `redLapMatrix`

```lean
noncomputable def redLapMatrix (q : V) : Matrix {v : V // v ≠ q} {v : V // v ≠ q} ℤ :=
  (G.lapMatrix ℤ).submatrix Subtype.val Subtype.val
```

**English:** The **reduced Laplacian** `L₀` — the graph Laplacian with row and column `q` removed. Square matrix indexed by `{v : V // v ≠ q}`.

**Matches LaTeX:** `L_G[i]`.

---

### Cauchy-Binet Bridge (Section)

These three lemmas transport the `cauchyBinet` theorem (proved for `Fin n × Fin m` matrices) to arbitrary finite types and specialize to `det(A·Aᵀ)`.

---

### 5.2 Lemma: `cauchyBinet_det_sq`

```lean
lemma cauchyBinet_det_sq {n m : ℕ} (A' : Matrix (Fin n) (Fin m) ℤ) :
    (A' * A'ᵀ).det =
    ∑ S ∈ (Finset.univ : Finset (Fin m)).powersetCard n,
      if h : S.card = n then ((A'.submatrix id (S.orderEmbOfFin h)).det) ^ 2 else 0
```

**English:** Applies the existing `cauchyBinet` to `A'·A'ᵀ` and simplifies: `det(A'ᵀ[S,:]) = det(A'[:,S])`, so each term becomes `det(A'[:,S])²`.

---

### 5.3 Lemma: `cauchyBinet_reindex_sq`

```lean
lemma cauchyBinet_reindex_sq {n : ℕ} (M : Matrix (Fin n) J ℤ) (eJ : J ≃ Fin (Fintype.card J)) :
    (sum over S ⊆ Fin m of det(M[:, eJ.symm ∘ S.emb])²) =
    (sum over T ⊆ J of det(M[:, T.emb])²)
```

**English:** Reindexes the sum from `Fin m` subsets to `J` subsets via `eJ`. For each `S ↔ T`, the two determinants differ by a column permutation whose sign vanishes when squared.

---

### 5.4 Lemma: `det_mul_transpose_cauchyBinet` ⭐

```lean
lemma det_mul_transpose_cauchyBinet (A : Matrix I J ℤ) :
    (A * Aᵀ).det = ∑ T ∈ (Finset.univ : Finset J).powersetCard (Fintype.card I),
      if h : T.card = Fintype.card I then
        ((A.submatrix (Fintype.equivFin I).symm (T.orderEmbOfFin h)).det) ^ 2
      else 0
```

**English (the Cauchy-Binet bridge):** For any `A : Matrix I J ℤ`:
```
det(A·Aᵀ) = Σ_{T ⊆ J, |T| = |I|} det(A[:,T])²
```
where `A[:,T]` is the square submatrix taking all rows and columns indexed by `T`.

**Proof:** Transport to `Fin n × Fin m`, apply `cauchyBinet_det_sq`, reindex back via `cauchyBinet_reindex_sq`.

This is the main formula needed for the matrix-tree proof.

---

### Submatrix Helpers (Section)

---

### 5.5 Lemma: `exists_perm_of_image_eq`

```lean
lemma exists_perm_of_image_eq (f g : I' ↪ J') (h_img : Set.range f = Set.range g) :
    ∃ τ : Equiv.Perm I', ∀ i, g i = f (τ i)
```

**English:** Two injections with the same image differ by a permutation of the domain.

---

### 5.6 Lemma: `det_submatrix_sq_eq_of_comp_perm`

```lean
lemma det_submatrix_sq_eq_of_comp_perm (M : Matrix n J' R) (f : n ↪ J') (τ : Equiv.Perm n) :
    ((M.submatrix id (f ∘ τ)).det) ^ 2 = ((M.submatrix id f).det) ^ 2
```

**English:** Reindexing columns by a permutation changes det by `±1` (the sign of the permutation). Squaring cancels the sign, so the squared determinants are equal.

---

### Submatrix Det Value: Tree vs Non-Tree (Section)

---

### 5.7 Lemma: `signedInc_submatrix_det_sq_tree`

```lean
lemma signedInc_submatrix_det_sq_tree (f : {v : V // v ≠ q} ↪ Sym2 V)
    (hf_edges : ∀ i, f i ∈ G.edgeSet) (htree : (edgeGraph q f).IsTree) :
    ((reducedSignedIncMatrix G q).submatrix id f).det ^ 2 = 1
```

**English:** If an edge selection `f` from non-root vertices to edges forms a **spanning tree** of `G`, then `det(B₀[:,f])² = 1`.

**Proof:**
1. Construct a `SpanningTree T` whose tree is `edgeGraph q f` (valid because `htree` and `hf_edges`)
2. `det(B₀[:, edgeEmbedding T q]) = ±1` by Theorem 3.14
3. Both `f` and `edgeEmbedding T q` are injections with the same image (the tree's edge set), so they differ by a permutation (Lemma 5.5)
4. Squaring cancels the permutation sign (Lemma 5.6)
5. Hence `det(B₀[:,f])² = det(B₀[:, edgeEmbedding T q])² = 1`

---

### 5.8 Lemma: `signedInc_submatrix_det_sq_nontree`

```lean
lemma signedInc_submatrix_det_sq_nontree (f : {v : V // v ≠ q} ↪ Sym2 V)
    (hntree : ¬(edgeGraph q f).IsTree) :
    ((reducedSignedIncMatrix G q).submatrix id f).det ^ 2 = 0
```

**English:** If the edge selection does **not** form a spanning tree, the determinant is `0` (by Theorem 4.9), so its square is `0`.

---

### Main Theorem Helpers (Section)

---

### 5.9 Lemma: `det_zero_of_non_edge`

```lean
lemma det_zero_of_non_edge (q : V) (f : {v : V // v ≠ q} → Sym2 V)
    (i : {v : V // v ≠ q}) (hi : f i ∉ G.edgeSet) :
    ((reducedSignedIncMatrix G q).submatrix id f).det = 0
```

**English:** If `f` maps some index to a non-edge of `G`, then the corresponding column in `B₀` is all zeros, so `det = 0`.

---

### 5.10 Lemma: `det_sq_transport`

```lean
lemma det_sq_transport {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I (Sym2 V) ℤ) (g : Fin (Fintype.card I) → Sym2 V) :
    ((M.submatrix (Fintype.equivFin I).symm g).det) ^ 2 =
    ((M.submatrix id (g ∘ (Fintype.equivFin I))).det) ^ 2
```

**English:** Reindexing rows by `(Fintype.equivFin I).symm` doesn't change the squared determinant.

---

### 5.11 Definition: `spanningTreeToEdgeFinset`

```lean
noncomputable def spanningTreeToEdgeFinset (T : SpanningTree G) :
    {S : Finset (Sym2 V) // S.card = Fintype.card V - 1 ∧
      (∀ e ∈ S, e ∈ G.edgeFinset) ∧
      (SimpleGraph.fromEdgeSet (S : Set (Sym2 V))).IsTree}
```

**English:** Maps a spanning tree to its edge Finset, with proofs that:
- Cardinality = `|V| - 1` (property of trees)
- Each edge is in `G.edgeFinset` (since `T.Tree ≤ G`)
- `fromEdgeSet(T.Tree.edgeFinset)` is a tree (since it reconstructs `T.Tree`)

---

### 5.12 Lemma: `spanningTreeToEdgeFinset_injective`

```lean
lemma spanningTreeToEdgeFinset_injective : Function.Injective (spanningTreeToEdgeFinset G)
```

**English:** Distinct spanning trees have distinct edge Finsets. (A tree is determined by its edge set.)

---

### 5.13 Lemma: `spanningTreeToEdgeFinset_surjective`

```lean
lemma spanningTreeToEdgeFinset_surjective : Function.Surjective (spanningTreeToEdgeFinset G)
```

**English:** Any Finset `S` of edges with the right cardinality that forms a tree is the edge set of some spanning tree.

---

### 5.14 Definition: `spanningTree_equiv_edgeFinset`

```lean
noncomputable def spanningTree_equiv_edgeFinset :
    SpanningTree G ≃ {T : Finset (Sym2 V) // T.card = Fintype.card V - 1 ∧
      (∀ e ∈ T, e ∈ G.edgeFinset) ∧
      (SimpleGraph.fromEdgeSet (T : Set (Sym2 V))).IsTree}
```

**English:** Bijection between `SpanningTree G` and edge Finsets `T` with `|T| = |V|-1`, all edges in `G`, and `fromEdgeSet T` is a tree.

---

### 5.15 Lemma: `cauchyBinet_term_tree`

```lean
lemma cauchyBinet_term_tree (G q) (T : Finset (Sym2 V)) (h : T.card = card {v≠q})
    (hsubset : ∀ e ∈ T, e ∈ G.edgeFinset)
    (htree : (SimpleGraph.fromEdgeSet (T : Set (Sym2 V))).IsTree) :
    ((reducedSignedIncMatrix G q).submatrix
      (Fintype.equivFin {v≠q}).symm (T.orderEmbOfFin h)).det ^ 2 = 1
```

**English:** In the Cauchy-Binet sum, if `T` is a valid edge set forming a tree, the term contributes `1`.

**Proof:** Construct an injection `f` from non-root vertices to edges using `T.orderEmbOfFin` composed with `Fintype.equivFin`, apply `signedInc_submatrix_det_sq_tree`.

---

### 5.16 Lemma: `cauchyBinet_term_nontree`

```lean
lemma cauchyBinet_term_nontree (G q) (T h hntree) :
    ((reducedSignedIncMatrix G q).submatrix
      (Fintype.equivFin {v≠q}).symm (T.orderEmbOfFin h)).det ^ 2 = 0
```

**English:** If `T` is NOT a valid edge set forming a tree (either contains non-edges or doesn't form a tree), the term contributes `0`.

---

### 5.17 Lemma: `spanningTree_edgeFinset_mem_powersetCard`

```lean
lemma spanningTree_edgeFinset_mem_powersetCard (G q) (T : SpanningTree G) :
    T.Tree.edgeFinset ∈ (Finset.univ : Finset (Sym2 V)).powersetCard
      (Fintype.card {v : V // v ≠ q})
```

**English:** A spanning tree's edge Finset has the right cardinality to appear in the Cauchy-Binet sum.

---

### 5.18 Lemma: `summand_at_spanningTree`

```lean
lemma summand_at_spanningTree (G q) (T : SpanningTree G)
    (h : T.Tree.edgeFinset.card = Fintype.card {v : V // v ≠ q}) :
    ((reducedSignedIncMatrix G q).submatrix ...).det ^ 2 = 1
```

**English:** At the Finset corresponding to a spanning tree, the Cauchy-Binet summand equals `1`.

---

### 5.19 Lemma: `summand_zero_of_not_spanningTree`

```lean
lemma summand_zero_of_not_spanningTree (G q) (T hT hT_not h) :
    ((reducedSignedIncMatrix G q).submatrix ...).det ^ 2 = 0
```

**English:** If `T` is in `powersetCard` but not the edge Finset of any spanning tree, the summand is `0`.

---

### 5.20 Lemma: `cauchyBinet_sum_eq_spanningTree_card` ⭐

```lean
lemma cauchyBinet_sum_eq_spanningTree_card [LinearOrder (Sym2 V)]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj] (q : V) :
    (∑ T ∈ ...powersetCard..., if ... then det² else 0) = Fintype.card (SpanningTree G)
```

**English:** The Cauchy-Binet sum equals the **number of spanning trees**.

**Proof:**
1. Split the sum into two parts: spanning-tree edge sets and others
2. Each spanning tree contributes `1` (Lemma 5.18)
3. Each non-spanning-tree contributes `0` (Lemma 5.19)
4. The sum over spanning-tree edge sets equals the count of spanning trees (via the bijection `spanningTree_equiv_edgeFinset`)

---

### 5.21 Theorem: `matrix_tree_theorem` ⭐⭐⭐

```lean
theorem matrix_tree_theorem [LinearOrder (Sym2 V)]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj] :
    ∀ q : V, (redLapMatrix G q).det = Fintype.card (SpanningTree G)
```

**English (Kirchhoff's Matrix-Tree Theorem):** For any finite simple graph `G` and any vertex `q`, the determinant of the reduced Laplacian (row `q`, column `q` removed) equals the number of spanning trees of `G`.

**Proof (4 lines):**
```lean
  intro q
  rw [show redLapMatrix G q = reducedSignedIncMatrix G q * (reducedSignedIncMatrix G q)ᵀ from
    redLapMatrix_eq_reducedSignedInc_mul_transpose G q]
  rw [det_mul_transpose_cauchyBinet]
  exact cauchyBinet_sum_eq_spanningTree_card G q
```

1. `L₀ = B₀·B₀ᵀ` (Lemma 1.10)
2. `det(B₀·B₀ᵀ) = Σ_{|T|=|V|-1} det(B₀[:,T])²` (Lemma 5.4)
3. This sum equals `Fintype.card (SpanningTree G)` (Lemma 5.20)

**Axioms used:** `propext`, `Classical.choice`, `Quot.sound` — standard Lean axioms, nothing additional.

**Hypotheses:**
- `Fintype V`, `LinearOrder V`, `DecidableEq V` — vertex set is finite and ordered
- `LinearOrder (Sym2 V)` — edges can be ordered (for determinant/PowerSetCard)
- `Fintype G.edgeSet` — finite edge set
- `DecidableRel G.Adj` — adjacency is decidable

`SpanningTree G` includes only subgraphs that share the vertex set `V` (since `Tree : SimpleGraph V`), so "spanning" is enforced.

---

├── CauchyBinet.lean                — adapted Cauchy-Binet formula (225 lines)

---

## Dependency Graph (theorems only)

```
matrix_tree_theorem (5.21)
├── redLapMatrix_eq_reducedSignedInc_mul_transpose (1.10)
│   └── lapMatrix_eq_signedInc_mul_transpose (1.9)
│       ├── signedIncMatrix_sq_eq_incMatrix (1.6)
│       ├── signedIncMatrix_mul_of_adj (1.7)
│       └── signedIncMatrix_mul_of_not_adj (1.8)
├── det_mul_transpose_cauchyBinet (5.4)
│   ├── cauchyBinet (CauchyBinet.lean)
│   ├── cauchyBinet_det_sq (5.2)
│   └── cauchyBinet_reindex_sq (5.3)
│       └── det_submatrix_sq_eq_of_comp_perm (5.6)
└── cauchyBinet_sum_eq_spanningTree_card (5.20)
    ├── cauchyBinet_term_tree (5.15)
    │   ├── signedInc_submatrix_det_sq_tree (5.7)
    │   │   ├── signedInc_det_tree (3.14)
    │   │   │   ├── prod_eq_zero_of_perm_ne_one (3.12)
    │   │   │   │   └── perm_eq_id_of_endpoint_condition (3.11)
    │   │   │   ├── prod_pm_one (3.13)
    │   │   │   └── submatrix_diag_pm_one (3.7)
    │   │   └── exists_perm_of_image_eq (5.5)
    │   └── det_sq_transport (5.10)
    ├── cauchyBinet_term_nontree (5.16)
    │   ├── signedInc_submatrix_det_sq_nontree (5.8)
    │   │   └── signedInc_det_nontree (4.9)
    │   │       ├── edgeGraph_not_tree_not_connected (4.3)
    │   │       ├── exists_unreachable_from_root (4.4)
    │   │       └── signedIncMatrix_sum_over_reachable_component_eq_zero (4.8)
    │   │           └── signedIncMatrix_col_sum_eq_zero (4.5)
    │   └── det_zero_of_non_edge (5.9)
    ├── summand_at_spanningTree (5.18)
    ├── summand_zero_of_not_spanningTree (5.19)
    └── spanningTree_equiv_edgeFinset (5.14)
        ├── spanningTreeToEdgeFinset_injective (5.12)
        └── spanningTreeToEdgeFinset_surjective (5.13)
```
