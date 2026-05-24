# Blueprint: Formal Proof of Kirchhoff's Matrix-Tree Theorem

## Chapter 0 — Proof Strategy and Architecture

### What is being proved?

Let $G = (V,E)$ be a finite simple graph. Choose any vertex $q$. Remove the $q$-th row and column from the Laplacian $L_G$ to get the **reduced Laplacian** $L_G[q]$. Kirchhoff's theorem says:

$$ \det(L_G[q]) = \text{number of spanning trees of } G $$

### Which proof did we formalise?

The Lean formalisation follows the **Cauchy-Binet formula**. The proof has five stages:

1. **Factor the Laplacian.** Write $L_G = B \cdot B^T$ where $B$ is a *signed incidence matrix* — for each edge $e = \{u,v\}$, give the smaller endpoint a $+1$ and the larger a $-1$. Dropping row $q$ from both sides gives $L_G[q] = B[q] \cdot B[q]^T$.

2. **Apply Cauchy-Binet.** The formula says $\det(A \cdot A^T) = \sum_{|S|=n-1} \det(A_S)^2$, where $A_S$ takes columns indexed by $S \subseteq E$. With $A = B[q]$, this gives $\det(L_G[q]) = \sum_{|S|=n-1} \det(B[q]_S)^2$.

3. **Classify the summands.** For a subset $S$ of $n-1$ edges, prove:

   - If the edges of $S$ form a spanning tree of $G$, then $\det(B[q]_S)^2 = 1$ (the determinant itself is $\pm 1$).
   - If they do not form a spanning tree, then $\det(B[q]_S)^2 = 0$.

4. **Count spanning trees.** The sum over all $S$ counts $1$ for each spanning tree and $0$ otherwise, so the total equals the number of spanning trees.

5. **Conclude.** $\det(L_G[q]) = \text{number of }\{\text{spanning trees of } G\}$.

### How the code is organised

The project is split into one file per major concept, each doing exactly one job and depending only on earlier files:

```
SpanningTree.lean    — what is a spanning tree? (data type, finiteness)
SignIncMatrix.lean   — the signed incidence matrix and its properties,
                          especially the factorisation L_G = B · B^T
CauchyBinet.lean     — the general Cauchy-Binet formula for Fin matrices
TreeDet.lean         — determinant = ±1 when edges form a spanning tree
NonTreeDet.lean      — determinant = 0 when edges do not form a spanning tree
MatrixTreeThm.lean   — assembles everything into the main theorem
```

Auxiliary files:
```
Basic.lean           — scratch / exploratory code (not imported)
ForMathlib.lean      — an unused extension lemma (MultilinearMap.ext_ring)
Example.lean         — exercises with sorries (not imported)
```

---

## Chapter 1 — What Is a Spanning Tree?

The file `SpanningTree.lean` defines the fundamental data type: a spanning tree of a graph $G$. This is the object we are counting, so it must be defined first and cleanly.

### The SpanningTree structure

```
structure SpanningTree (G : SimpleGraph V) where
  Tree : SimpleGraph V
  subG : Tree ≤ G
  isTree : Tree.IsTree
```

A spanning tree of $G$ is a triple:

- **`Tree`** — another simple graph on the same vertex set $V$. This *is* the tree.
- **`subG`** — a proof that $Tree$ is a subgraph of $G$, written as `Tree ≤ G`. This means every edge of the tree is an edge of $G$.
- **`isTree`** — a proof that $Tree$ is a tree (connected and acyclic).

There is no explicit "spans $V$" condition because Mathlib's `IsTree` on a graph over vertex set $V$ already implies the graph is connected, which for a subgraph of $G$ implies it uses all vertices reachable in $G$. Combined with the cardinality condition used later, this gives the spanning property.

### Finiteness: there are only finitely many spanning trees

```
instance finiteSpanningTree (G : SimpleGraph V) : Finite (SpanningTree G) := ...
instance fintypeSpanningTree (G : SimpleGraph V) : Fintype (SpanningTree G) := ...
```

Since $V$ is finite, there are only finitely many simple graphs on $V$, hence only finitely many spanning trees. The `SpanningTree` type is given `Finite` and `Fintype` instances, so we can later write `Fintype.card (SpanningTree G)` — the integer we claim equals $\det(L_G[q])$.

The proof of finiteness uses the injective map `t ↦ t.Tree` from spanning trees to simple graphs; the latter type is known to be finite.

---

## Chapter 2 — The Signed Incidence Matrix

The file `SignIncMatrix.lean` defines an oriented incidence matrix $B$ and proves the fundamental factorisation $L_G = B \cdot B^T$. This is stage 1 of the overall proof.

### Why signed incidence?

The ordinary (unoriented) incidence matrix has $0/1$ entries: a $1$ at $(v, e)$ if $v$ is incident to $e$. The Laplacian satisfies $L_G = (\text{inc}) \cdot (\text{inc})^T$, but the incidence matrix is *vertex×edge* and the product doesn't produce $\pm 1$ off-diagonals correctly without orientation.

Instead we assign each edge $e = \{u, v\}$ an **arbitrary direction** — we declare the smaller vertex (via a `LinearOrder`) to be the "head" and the larger to be the "tail". Then:

- $B(v, e) = +1$ if $v$ is the smaller endpoint of $e$.
- $B(v, e) = -1$ if $v$ is the larger endpoint of $e$.
- $B(v, e) = 0$ if $v$ is not incident to $e$.

This makes $L_G = B \cdot B^T$ hold *exactly* at every entry, because for adjacent vertices $i \neq j$, the product $(B \cdot B^T)_{ij} = \sum_e B(i,e) B(j,e) = -1$ (since one gets $+1$, the other $-1$, and they share exactly one edge), while for the diagonal $(B \cdot B^T)_{ii} = \sum_e B(i,e)^2 = \deg(i)$.

### Defining the matrix

The tricky part is that edges are unordered pairs (`Sym2 V`). The matrix entry $B(v, e)$ must be independent of whether we write $e$ as `s(a,b)` or `s(b,a)`. The function `Sym2.lift` handles this: we supply a function $V \times V \to \mathbb{Z}$ that is symmetric in its two arguments, and `Sym2.lift` extends it to `Sym2 V`.

```
def signedIncMatrix : Matrix V (Sym2 V) ℤ :=
  fun v e =>
    Sym2.lift ⟨(fun a b =>
      if G.Adj a b then
        if v = min a b then 1 else if v = max a b then -1 else 0
      else 0),
    -- Proof that the function is symmetric in a and b
    ...⟩ e
```

The inner function says: given an ordered pair $(a,b)$, if they're adjacent in $G$, check whether $v$ is the minimum (return $+1$) or maximum (return $-1$) of $\{a,b\}$. If not adjacent, return $0$. The proof of symmetry ensures that swapping $a$ and $b$ doesn't change the value, since $\min(a,b) = \min(b,a)$ and adjacency is symmetric.

### Entry-level lemmas

Three lemmas extract values from the matrix in the three possible cases:

- `signedIncMatrix_entry_fst` — when $x \leq y$ and $x$ is adjacent to $y$, then $B(x, s(x,y)) = 1$.
- `signedIncMatrix_entry_snd` — when $x \leq y$ and $x$ is adjacent to $y$, then $B(y, s(x,y)) = -1$.
- `signedIncMatrix_entry_not_incident` — when the edge $e$ is not incident to $v$, then $B(v, e) = 0$.

The first two use the `≤` relation to decide which endpoint gets $+1$ and which gets $-1$. The third uses `Sym2.ind` (induction on unordered pairs) to break $e$ into $s(a,b)$ and check all possibilities.

### The reduced signed incidence matrix

```
def reducedSignedIncMatrix (q : V) : Matrix ({v : V // v ≠ q}) (Sym2 V) ℤ :=
  (signedIncMatrix G).submatrix (fun x => x.val) id
```

This is the matrix $B[q]$: it's $B$ with the row for vertex $q$ removed. The domain is `{v : V // v ≠ q}`, the subtype of vertices that are *not* $q$. The `submatrix` operation reindexes: the row index $x$ is sent to $x.val$, picking out the corresponding row of the full signed incidence matrix.

### The core identity: B(i,e)² = inc(i,e)

```
lemma signedIncMatrix_sq_eq_incMatrix (i : V) (e : Sym2 V) :
    (signedIncMatrix G i e)^2 = (G.incMatrix ℤ) i e := ...
```

Squaring removes the sign. Whether $B(i,e)$ is $+1$ or $-1$, its square is $1$, and both cases correspond exactly to $i$ being incident to $e$. If $i$ is not incident to $e$, both are $0$. The proof decomposes $e$ into $s(a,b)$, checks which endpoint equals $i$, and handles both $a \leq b$ and $b \leq a$ cases.

### Product of two rows: adjacent vertices

```
lemma signedIncMatrix_mul_of_adj {i j : V} (_hij : i ≠ j) (hadj : G.Adj i j) (e : Sym2 V) :
    signedIncMatrix G i e * signedIncMatrix G j e =
    if e = s(i, j) then (-1 : ℤ) else 0 := ...
```

When $i$ and $j$ are adjacent, the product $B(i,e) \cdot B(j,e)$ can only be non-zero for exactly one edge: $e = s(i,j)$. For that edge, one vertex gets $+1$ and the other gets $-1$ (which one depends on the order), so the product is $-1$. For any other edge, at least one of $i$ or $j$ is not incident, so the product is $0$.

The proof uses `incidenceSet_inter_incidenceSet_of_adj` from Mathlib: adjacent vertices share exactly one edge in their incidence sets, namely `s(i,j)`.

### Product of two rows: non-adjacent vertices

```
lemma signedIncMatrix_mul_of_not_adj {i j : V} (hij : i ≠ j) (hnadj : ¬ G.Adj i j) (e : Sym2 V) :
    signedIncMatrix G i e * signedIncMatrix G j e = 0 := ...
```

If $i$ and $j$ are **not** adjacent, their incidence sets are disjoint, so no edge can be incident to both. The product is always $0$.

### The big theorem: L_G = B · B^T

```
lemma lapMatrix_eq_signedInc_mul_transpose :
    G.lapMatrix ℤ = signedIncMatrix G * (signedIncMatrix G)ᵀ := ...
```

This proves the entrywise equality that is the foundation of everything. Let's walk through the proof:

**Case 1: $i = j$ (diagonal).** We need $(L_G)_{ii} = \deg(i)$. The right-hand side is $\sum_e B(i,e)^2$. By `signedIncMatrix_sq_eq_incMatrix`, $B(i,e)^2 = \text{inc}(i,e)$, and the sum of $\text{inc}(i,e)$ over all edges is exactly $\deg(i)$ — this is `G.sum_incMatrix_apply` from Mathlib.

**Case 2: $i \neq j$, adjacent.** We need $(L_G)_{ij} = -1$. The sum $\sum_e B(i,e) \cdot B(j,e)$ has exactly one non-zero term (for $e = s(i,j)$), and that term equals $-1$ by `signedIncMatrix_mul_of_adj`. The Laplacian off-diagonal for adjacent vertices is $-1$ by definition, so the two sides match.

**Case 3: $i \neq j$, not adjacent.** Both sides are $0$. The left side is $0$ because there's no adjacency. The right side uses `signedIncMatrix_mul_of_not_adj` to show every term in the sum is $0$.

### Reduced factorisation

```
lemma redLapMatrix_eq_reducedSignedInc_mul_transpose (q : V) :
    (G.lapMatrix ℤ).submatrix (fun x : {v // v ≠ q} => x.val) (fun x : {v // v ≠ q} => x.val) =
    reducedSignedIncMatrix G q * (reducedSignedIncMatrix G q)ᵀ := ...
```

This drops the $q$-th row and column from both sides of the factorisation. It follows directly from the full version: the submatrix of a product is the product of submatrices when the index maps compose correctly. The proof is a straightforward `ext i j` followed by rewriting with the definitions.

---

## Chapter 3 — The Cauchy-Binet Formula

The file `CauchyBinet.lean` proves the general Cauchy-Binet formula for matrices indexed by `Fin n` and `Fin m` over any commutative ring $R$. This is a self-contained general result, adapted from the `algebraic-combinatorics` project. The proof is long but the statement is simple.

### The statement

```
theorem cauchyBinet {n m : ℕ} (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin m) (Fin n) R) :
    (A * B).det = ∑ S ∈ (Finset.univ : Finset (Fin m)).powersetCard n,
      if h : S.card = n then
        (colsSubmatrix A S h).det * (rowsSubmatrix B S h).det
      else 0 := ...
```

In words: the determinant of the $n \times n$ product $A \cdot B$ equals the sum over all $n$-element subsets $S$ of $\{0, \dots, m-1\}$ of $\det(A_S) \cdot \det(B_S)$, where $A_S$ picks columns $S$ of $A$ and $B_S$ picks rows $S$ of $B$.

### Submatrix selectors

```
def colsSubmatrix {n m : ℕ} (A : Matrix (Fin n) (Fin m) R)
    (S : Finset (Fin m)) (hcard : S.card = n) : Matrix (Fin n) (Fin n) R :=
  A.submatrix id (S.orderEmbOfFin hcard)
```

`S.orderEmbOfFin hcard` is the unique order-preserving bijection from `Fin n` to $S$ (where $S$ inherits the order of `Fin m`). So `colsSubmatrix` selects $n$ columns of $A$ indexed by $S$, pulled back to `Fin n` in increasing order. Dually for `rowsSubmatrix`.

### Key lemma: only injective selections contribute

```
lemma det_mul_aux_nonsquare ... (hf : ¬Function.Injective f) : ... = 0 := ...
```

When we expand $\det(A \cdot B)$ using the Leibniz formula, we get a double sum over $\sigma \in S_n$ and functions $f : [n] \to [m]$ (one entry per column of $B$). This lemma says: if $f$ is not injective, the inner sum over $\sigma$ vanishes. The proof uses a sign-reversing involution: when $f(i) = f(j)$ for $i \neq j$, swapping $i$ and $j$ in the permutation $\sigma$ flips the sign while preserving the product term, causing pairwise cancellation.

### The decomposition

The main proof then:
1. Expands $(A \cdot B)_{ij} = \sum_k A_{ik} \cdot B_{kj}$.
2. Expands the product over $i$ as a sum over all functions $f : [n] \to [m]$.
3. Keeps only injective $f$ (others cancel).
4. Partitions injective $f$ by their image $S \subseteq [m]$ (an $n$-element subset).
5. Within each fiber over $S$, bijects $f$'s to permutations of $[n]$ (since $f$ factors uniquely as a permutation followed by the order-preserving bijection $S \to [n]$).
6. Recognises the resulting sum as $\det(A_S) \cdot \det(B_S)$.

---

## Chapter 4 — Adapting Cauchy-Binet to Our Setting

The Cauchy-Binet formula is proved for `Fin`-indexed matrices, but our signed incidence matrix has vertex set $V$ and edge set `Sym2 V` as indices. The file `MatrixTreeThm.lean` contains bridge lemmas that adapt the formula.

### Cauchy-Binet for A · A^T

```
lemma cauchyBinet_det_sq {n m : ℕ} (A' : Matrix (Fin n) (Fin m) ℤ) :
    (A' * A'ᵀ).det = ∑ S ..., if h : S.card = n then ((A'.submatrix id (S.orderEmbOfFin h)).det) ^ 2 else 0 := ...
```

This specialises the general `cauchyBinet` to the case $B = A^T$. Then $\det(A_S) \cdot \det(B_S) = \det(A_S) \cdot \det((A^T)_S) = \det(A_S) \cdot \det(A_S)^T = \det(A_S)^2$, so we get a sum of squared determinants.

### Reindexing the sum

```
lemma cauchyBinet_reindex_sq ... := ...
```

The Cauchy-Binet sum runs over subsets of `Fin m`. We need it over subsets of an arbitrary type $J$ (our edge set). This lemma uses `Finset.sum_bij` with the bijection $S \mapsto e_J^{-1}(S)$ to reindex from `Fin m` subsets to $J$ subsets. The non-trivial part is proving that reindexing the columns by a permutation doesn't change $\det^2$ — the permutation's sign is $\pm 1$, which squares to $1$.

### The final bridge: det_mul_transpose_cauchyBinet

```
lemma det_mul_transpose_cauchyBinet (A : Matrix I J ℤ) :
    (A * Aᵀ).det = ∑ T ∈ (Finset.univ : Finset J).powersetCard (Fintype.card I),
      if h : T.card = Fintype.card I then
        ((A.submatrix (Fintype.equivFin I).symm (T.orderEmbOfFin h)).det) ^ 2
      else 0 := ...
```

This is the statement we actually use. It says: for any matrix $A$ indexed by fintypes $I$ and $J$, the determinant of $A \cdot A^T$ equals the sum over all $|I|$-element subsets $T$ of $J$ of $\det(A_T)^2$, where $A_T$ is the $|I| \times |I|$ square matrix formed by taking rows $I$ (all of them, via the reindexing `Fintype.equivFin I`) and columns $T$.

The proof uses `Fintype.equivFin` to transport the problem to `Fin` types, applies `cauchyBinet_det_sq`, then reindexes back.

---

## Chapter 5 — Determinant = ±1 for Spanning Trees

The file `TreeDet.lean` proves that when the selected edges form a spanning tree, the determinant of the reduced signed incidence submatrix is $\pm 1$. This corresponds to the "spanning tree" case of the key Lemma in the LaTeX proof.

### The parent function

Given a spanning tree $T$ rooted at $q$, and a non-root vertex $v \neq q$, what is the "parent" of $v$? In a tree, there is a unique simple path from $v$ to $q$. The parent is the **second vertex** on that path (the first being $v$ itself).

```
noncomputable def treeParent (T : SpanningTree G) (q : V) (v : {v : V // v ≠ q}) : V :=
  let p := (T.isTree.existsUnique_path v.val q).exists.choose
  p.getVert 1
```

We pick the unique simple path $p$ from $v$ to $q$ in $T.Tree$ (it exists because $T$ is a tree, hence connected). `p.getVert 0` is $v$, `p.getVert 1` is the parent. The `noncomputable` tag is needed because `existsUnique_path.choose` involves classical choice.

Three lemmas describe the parent:

- `treeParent_adj` — $v$ is adjacent to its parent in $T.Tree$. This follows from `Walk.adj_getVert_succ`.
- `treeParent_edge_mem` — the unordered pair $\{v, \text{parent}(v)\}$ is an edge of $T.Tree$.
- `treeParent_eq_q_of_depth_one` — if the path from $v$ to $q$ has length $1$, the parent is $q$.

### The edge embedding

```
noncomputable def edgeEmbedding (T : SpanningTree G) (q : V) : {v : V // v ≠ q} ↪ Sym2 V :=
  ⟨fun v => s(v.val, treeParent T q v), treeParent_edge_injective T q⟩
```

This maps each non-root vertex $v$ to the edge $\{v, \text{parent}(v)\}$. It is an injection (proved by `treeParent_edge_injective`). Since there are $|V|-1$ non-root vertices and a spanning tree has exactly $|V|-1$ edges, this injection is in fact a bijection between non-root vertices and tree edges — a $1$-$1$ correspondence that is crucial for the determinant argument.

### The key combinatorial lemma: perm_eq_id_of_endpoint_condition

This is the heart of the tree case. Suppose we have a permutation $\sigma$ of the non-root vertices with the property that for every $i$, $\sigma(i)$ is *either* $i$ itself *or* the parent of $i$. Then $\sigma$ must be the identity.

```
lemma perm_eq_id_of_endpoint_condition (T : SpanningTree G) (q : V)
    (σ : Equiv.Perm {v : V // v ≠ q})
    (h : ∀ i, (σ i).val = i.val ∨ (σ i).val = treeParent T q i) : σ = 1 := ...
```

**Why is this true?** Suppose $\sigma$ is not the identity. Pick a vertex $v_0$ with $\sigma(v_0) \neq v_0$ of *minimum depth* (distance to $q$ along the tree). Since $\sigma(v_0) \neq v_0$, the condition forces $\sigma(v_0) = \text{parent}(v_0)$. By the depth-minimality, $\sigma(\text{parent}(v_0)) = \text{parent}(v_0)$. But then $\sigma$ maps both $v_0$ and $\text{parent}(v_0)$ to $\text{parent}(v_0)$, contradicting injectivity.

The formal proof constructs the depth argument carefully:
1. **Depth** is defined as the length of the unique path to $q$.
2. A lemma `treeDepth_pos` says depth $> 0$ for any non-root vertex.
3. The key inequality uses that `treeDepth(parent(v)) < treeDepth(v)` — the parent is closer to $q$ by exactly one edge.
4. The minimum over a finite set is found using `Set.exists_min_image`.

This lemma is the *only* place where the tree structure (acyclicity) is used to exclude non-trivial permutations. It is the combinatorial core of the entire proof.

### Why non-identity permutations vanish in the determinant

```
lemma prod_eq_zero_of_perm_ne_one (T : SpanningTree G) (q : V)
    (σ : Equiv.Perm {v : V // v ≠ q}) (hσ : σ ≠ 1) :
    ∏ i, signedIncMatrix G (σ i).val ((edgeEmbedding T q) i) = 0 := ...
```

In the Leibniz expansion of $\det(M)$, each permutation $\sigma \neq \text{id}$ contributes a term $\prod_i M(\sigma(i), i)$. For our matrix $M$, this product is $\prod_i B(\sigma(i), \text{edge}(i))$.

If $\sigma$ is not the identity, by the contrapositive of `perm_eq_id_of_endpoint_condition`, there exists an $i$ such that $\sigma(i)$ is *neither* $i$ *nor* the parent of $i$. For that $i$, the entry $B(\sigma(i), \text{edge}(i))$ is $0$ (by `submatrix_entry_eq_zero_of_not_endpoint`: $\sigma(i)$ is not an endpoint of edge $i$). Hence the whole product is $0$.

### Diagonal entries are ±1

```
lemma submatrix_diag_pm_one (T : SpanningTree G) (q : V) (i : {v : V // v ≠ q}) :
    signedIncMatrix G i.val ((edgeEmbedding T q) i) = 1 ∨
    signedIncMatrix G i.val ((edgeEmbedding T q) i) = -1 := ...
```

The diagonal entry $M(i,i) = B(i, \{i, \text{parent}(i)\})$ is either $+1$ or $-1$, depending on whether $i$ is the smaller or larger endpoint of its parent edge. Both cases are covered.

### Product of ±1 values is ±1

```
lemma prod_pm_one {ι : Type*} [Fintype ι] (f : ι → ℤ) (hf : ∀ i, f i = 1 ∨ f i = -1) :
    (∏ i, f i) = 1 ∨ (∏ i, f i) = -1 := ...
```

A product where every factor is $\pm 1$ is itself $\pm 1$. The proof uses the absolute value: $|\prod f_i| = \prod |f_i| = \prod 1 = 1$.

### The main theorem of this file

```
theorem signedInc_det_tree (T : SpanningTree G) (q : V) :
    ((reducedSignedIncMatrix G q).submatrix id (edgeEmbedding T q)).det = 1 ∨
    ((reducedSignedIncMatrix G q).submatrix id (edgeEmbedding T q)).det = -1 := ...
```

Let $M$ be the matrix obtained from $B[q]$ by selecting columns according to the edge embedding (edges of the spanning tree). Then $\det(M) = \pm 1$.

**Proof:**
1. Expand $\det(M)$ via the Leibniz formula: $\det(M) = \sum_\sigma \text{sign}(\sigma) \cdot \prod_i M(\sigma(i), i)$.
2. For $\sigma \neq \text{id}$: by `prod_eq_zero_of_perm_ne_one`, the product is $0$. So the term contributes $0$.
3. For $\sigma = \text{id}$: the term is $\text{sign}(\text{id}) \cdot \prod_i M(i,i) = \prod_i M(i,i)$.
4. Each $M(i,i)$ is $\pm 1$ (by `submatrix_diag_pm_one`), so their product is $\pm 1$ (by `prod_pm_one`).

Thus the entire sum equals $\pm 1$.

This is exactly the $\det = \pm 1$ case of the Lemma in the LaTeX proof — the "spanning tree" arm.

---

## Chapter 6 — Determinant = 0 for Non-Tree Edge Selections

The file `NonTreeDet.lean` proves that when the selected $n-1$ edges do **not** form a spanning tree, the determinant is $0$. This is the "not a spanning tree" arm of the LaTeX Lemma.

The LaTeX proof uses a cycle argument: if the edges aren't a tree, they contain a cycle, so the corresponding columns are linearly dependent, making the determinant $0$. Our Lean proof uses a different (but equivalent) argument: if the edges don't form a tree, the graph they induce is disconnected, and the rows corresponding to the component unreachable from $q$ sum to zero.

### The edge graph

```
def edgeGraph (q : V) (S : {v : V // v ≠ q} ↪ Sym2 V) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (Set.range S)
```

Given an injection $S$ from non-root vertices to edges (the edge selection), `edgeGraph q S` is the simple graph on $V$ whose edges are exactly the image of $S$. This graph has exactly $|V|-1$ edges.

### A linear algebra tool: zero row-sum ⇒ zero determinant

```
lemma det_zero_of_sum_rows_eq_zero {n : Type*} [DecidableEq n] [Fintype n]
    {R : Type*} [CommRing R] (A : Matrix n n R)
    (S : Finset n) (hne : S.Nonempty)
    (hsum : ∀ j : n, ∑ i ∈ S, A i j = 0) : A.det = 0 := ...
```

If a non-empty set of rows of a square matrix sums to zero (meaning for each column $j$, the sum of entries in those rows at column $j$ is $0$), then the determinant is $0$.

**Why?** Pick any row $v_0$ in $S$. Repeatedly add each other row $i \in S$, $i \neq v_0$, to row $v_0$. Each addition preserves the determinant (by `Matrix.det_updateRow_add_self`). After adding all rows, row $v_0$ becomes $\sum_{i \in S} A_i$, which is the zero vector by hypothesis. A matrix with a zero row has determinant $0$. The lemma uses induction on $S$ to add rows one by one.

### Graph theory: not a tree ⇒ not connected

```
lemma edgeGraph_not_tree_not_connected (hNotTree : ¬ (edgeGraph q S).IsTree) :
    ¬ (edgeGraph q S).Connected := ...
```

If the edge graph $H$ is not a tree, it cannot be connected. **Why?** $H$ has $|V|-1$ edges (because $S$ is an injection into `Sym2 V` from a set of size $|V|-1$). If $H$ were connected, by graph theory a connected graph on $|V|$ vertices with $|V|-1$ edges *must* be a tree (Mathlib's `isTree_iff_connected_and_card`). So $H$ being connected would force it to be a tree — contradiction.

The proof computes cardinalities:
- $H$'s edge set is contained in $\text{range}(S)$, so $|E(H)| \leq |\text{range}(S)| = |V|-1$.
- A connected spanning subgraph $T$ (obtained via `Connected.exists_isTree_le`) has $|E(T)| = |V|-1$.
- So $|E(H)| = |V|-1$ and, with connectivity, $H$ is a tree.

### Getting an unreachable vertex

```
lemma exists_unreachable_from_root (H : SimpleGraph V) (q : V) (hNotConn : ¬ H.Connected) :
    ∃ u : V, ¬ H.Reachable q u := ...
```

In a disconnected graph, there exists a vertex not reachable from $q$. This is the contrapositive of the characterisation `connected_iff_exists_forall_reachable`.

### Column sum over the component unreachable from q

The key computational lemma:

```
lemma signedIncMatrix_sum_over_reachable_component_eq_zero
    (q : V) (S : {v : V // v ≠ q} ↪ Sym2 V) (u : V) (j : {v : V // v ≠ q}) :
    ∑ v ∈ (Finset.univ.filter (fun w => (edgeGraph q S).Reachable u w)),
      signedIncMatrix G v (S j) = 0 := ...
```

Let $C$ be the set of vertices reachable from $u$ in the edge graph $H$. For any edge $e = S(j)$ (coming from the selection $S$), the sum of $B(v, e)$ over $v \in C$ is $0$.

**Why?** Write $e = \{a, b\}$.
- If $a = b$: impossible (no loops in $G$).
- If $a \neq b$: Because $e$ is an edge of $H$, $a$ and $b$ are adjacent in $H$. Hence they are either both reachable from $u$ or both not. 
  - **Both reachable:** The sum over $C$ includes both $a$ and $b$, where $B(a,e) = \pm 1$ and $B(b,e) = \mp 1$ (opposite signs). They cancel, and all other terms are $0$.
  - **Neither reachable:** All $B(v,e) = 0$ for $v \in C$, so the sum is $0$.

### The main theorem of this file

```
theorem signedInc_det_nontree (q : V) (S : {v : V // v ≠ q} ↪ Sym2 V)
    (hNotTree : ¬ (edgeGraph q S).IsTree) :
    ((reducedSignedIncMatrix G q).submatrix id S).det = 0 := ...
```

**Proof (five steps):**

1. **Not a tree ⇒ not connected.** Use `edgeGraph_not_tree_not_connected`.

2. **Get an unreachable vertex $u$.** Use `exists_unreachable_from_root`. This $u$ cannot be reached from $q$ in $H$. In particular, $u \neq q$ and $q \notin C$ where $C$ is the reachability component of $u$.

3. **Define $T = \{v \neq q \mid \text{reachable from } u \text{ in } H\}$.** This is a non-empty set of row indices for $B[q]$, and it does not contain $q$.

4. **The rows indexed by $T$ sum to zero.** For each column $j$, the sum $\sum_{v \in T} B[q](v, S(j)) = \sum_{v \in T} B(v, S(j))$. But $T$ is in one-to-one correspondence with $C$ (the reachability set in $V$) since $q \notin C$. And `signedIncMatrix_sum_over_reachable_component_eq_zero` says $\sum_{v \in C} B(v, S(j)) = 0$.

5. **Apply `det_zero_of_sum_rows_eq_zero`.** The non-empty set $T$ of rows sums to zero, so the determinant is $0$.

---

## Chapter 7 — The Main Theorem

The file `MatrixTreeThm.lean` puts everything together to prove:

```
theorem matrix_tree_theorem [LinearOrder (Sym2 V)]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj] :
    ∀ q : V, (redLapMatrix G q).det = Fintype.card (SpanningTree G) := ...
```

### The reduced Laplacian

```
noncomputable def redLapMatrix (q : V) : Matrix {v : V // v ≠ q} {v : V // v ≠ q} ℤ :=
  (G.lapMatrix ℤ).submatrix Subtype.val Subtype.val
```

This is $L_G[q]$ — the Laplacian with row $q$ and column $q$ removed. The domain and codomain are both `{v : V // v ≠ q}`, the $n-1$ remaining vertices.

### Collating the determinant value

Two wrapper lemmas package the results from earlier files:

```
lemma signedInc_submatrix_det_sq_tree (f : {v : V // v ≠ q} ↪ Sym2 V)
    (hf_edges : ∀ i, f i ∈ G.edgeSet) (htree : (edgeGraph q f).IsTree) :
    ((reducedSignedIncMatrix G q).submatrix id f).det ^ 2 = 1 := ...
```

If $f$ maps non-root vertices to $G$-edges that form a spanning tree, then $\det(B[q]_f)^2 = 1$. This wraps `signedInc_det_tree` but first reconciles the two possible column selections: `edgeEmbedding T q` (from `TreeDet`) and `f` (from the Cauchy-Binet sum). The key lemma `exists_perm_of_image_eq` shows two injections with the same range differ by a permutation, and `det_submatrix_sq_eq_of_comp_perm` shows that post-composing with a permutation doesn't change $\det^2$.

```
lemma signedInc_submatrix_det_sq_nontree (f : {v : V // v ≠ q} ↪ Sym2 V)
    (hntree : ¬(edgeGraph q f).IsTree) :
    ((reducedSignedIncMatrix G q).submatrix id f).det ^ 2 = 0 := ...
```

If the edges don't form a spanning tree, $\det^2 = 0$. This wraps `signedInc_det_nontree`.

### Handling degenerate edge selections

```
lemma det_zero_of_non_edge (q : V) (f : {v : V // v ≠ q} → Sym2 V)
    (i : {v : V // v ≠ q}) (hi : f i ∉ G.edgeSet) : ...det = 0 := ...
```

If some column selected by $f$ is not even an edge of $G$ (e.g., from a subset $T \subseteq$ all unordered pairs, not just $G$'s edges), the matrix has a zero column and the determinant is $0$.

### The Cauchy-Binet sum classification

Two lemmas classify each term in the Cauchy-Binet sum:

```
lemma cauchyBinet_term_tree ... : ...det ^ 2 = 1 := ...
lemma cauchyBinet_term_nontree ... : ...det ^ 2 = 0 := ...
```

Given a subset $T$ of `Sym2 V` of size $|V|-1$:
- If $T$ consists of $G$-edges and forms a tree, the term contributes $1$.
- Otherwise, the term contributes $0$.

### Counting spanning trees

The spanning tree type `SpanningTree G` is in bijection with its edge set (`spanningTree_equiv_edgeFinset`). This lets us rewrite a sum over $n-1$-subsets of edges to a sum over spanning trees:

```
lemma cauchyBinet_sum_eq_spanningTree_card ... :
    (Cauchy-Binet sum) = (Fintype.card (SpanningTree G) : ℤ) := ...
```

**Proof:** Partition the sum into two parts: terms corresponding to spanning-tree edge sets, and all others.
- For spanning-tree terms: each contributes $1$ (by `cauchyBinet_term_tree`). There are `Fintype.card (SpanningTree G)` such terms (the bijection).
- For non-tree terms: each contributes $0$ (by `cauchyBinet_term_nontree`).

### The final proof

```
theorem matrix_tree_theorem ... : ∀ q : V, (redLapMatrix G q).det = Fintype.card (SpanningTree G) := by
  intro q
  rw [show redLapMatrix G q = reducedSignedIncMatrix G q * (reducedSignedIncMatrix G q)ᵀ from
    redLapMatrix_eq_reducedSignedInc_mul_transpose G q]
  rw [det_mul_transpose_cauchyBinet]
  exact cauchyBinet_sum_eq_spanningTree_card G q
```

For any vertex $q$:
1. Rewrite the reduced Laplacian as $B[q] \cdot B[q]^T$ (factorisation from Chapter 2).
2. Apply Cauchy-Binet (from Chapter 4): $\det(B[q] \cdot B[q]^T) = \sum_{|T|=|V|-1} \det(B[q]_T)^2$.
3. The sum equals the number of spanning trees (by the classification above).

This is a direct formalisation of the second proof in `matrix-tree-theorem.tex`.

---

## Appendix A — Mapping to the LaTeX Proof

| LaTeX (`matrix-tree-theorem.tex`) | Lean declaration |
|---|---|
| $L_G = B \cdot B^T$ | `lapMatrix_eq_signedInc_mul_transpose` (SignIncMatrix.lean) |
| $L_G[q] = B[q] \cdot B[q]^T$ | `redLapMatrix_eq_reducedSignedInc_mul_transpose` (SignIncMatrix.lean) |
| Cauchy-Binet formula | `cauchyBinet` (CauchyBinet.lean), `det_mul_transpose_cauchyBinet` (MatrixTreeThm.lean) |
| Lemma: $\lvert\det(B_S[q])\rvert = 1$ if $S$ is spanning tree | `signedInc_submatrix_det_sq_tree` (wrapping `signedInc_det_tree` from TreeDet.lean) |
| Lemma: $\det(B_S[q]) = 0$ if $S$ is not spanning tree | `signedInc_submatrix_det_sq_nontree` (wrapping `signedInc_det_nontree` from NonTreeDet.lean) |
| "Direct the edges around the cycle; summing the columns yields the zero vector" | Connectivity argument via `signedIncMatrix_sum_over_reachable_component_eq_zero` + `det_zero_of_sum_rows_eq_zero` (NonTreeDet.lean) |
| "Induction on $n$: pick a leaf, expand along last row" | `perm_eq_id_of_endpoint_condition` + Leibniz expansion via `signedInc_det_tree` (TreeDet.lean) |
| $\det(L_G[q]) = \tau(G)$ | `matrix_tree_theorem` (MatrixTreeThm.lean) |

---

## Appendix B — Full Dependency Graph

```
                                ┌──────────────────────┐
                                │   SpanningTree.lean   │
                                │ (SpanningTree type,   │
                                │  Finite/Fintype inst) │
                                └──────────┬───────────┘
                                           │
              ┌────────────────────────────┤
              │                            │
┌─────────────┴──────────────┐  ┌─────────┴────────────┐
│    SignIncMatrix.lean      │  │    TreeDet.lean       │
│ (signedIncMatrix,          │  │ (treeParent,          │
│  factor L_G = B·B^T,       │  │  edgeEmbedding,       │
│  reducedSignedIncMatrix)   │  │  perm_eq_id_of_...,   │
└─────────────┬──────────────┘  │  signedInc_det_tree)  │
              │                 └─────────┬────────────┘
              │                           │
              │              ┌────────────┤
              │              │            │
┌─────────────┴──────────────┤  ┌─────────┴────────────┐
│   CauchyBinet.lean         │  │  NonTreeDet.lean      │
│ (cauchyBinet theorem,      │  │ (det_zero_of_sum_rows │
│  det_mul_aux_nonsquare,    │  │  _eq_zero,            │
│  sum_injective_eq_...)     │  │  signedInc_det_       │
└─────────────┬──────────────┘  │  nontree)             │
              │                 └─────────┬────────────┘
              │                           │
              └───────────┬───────────────┘
                          │
              ┌───────────┴───────────────┐
              │   MatrixTreeThm.lean      │
              │                           │
              │ cauchyBinet_det_sq        │
              │ cauchyBinet_reindex_sq    │
              │ det_mul_transpose_        │
              │   cauchyBinet             │
              │ exists_perm_of_image_eq   │
              │ det_submatrix_sq_eq_of_   │
              │   comp_perm               │
              │ spanningTree_equiv_       │
              │   edgeFinset              │
              │ cauchyBinet_term_tree /   │
              │   nontree                 │
              │ cauchyBinet_sum_eq_       │
              │   spanningTree_card       │
              │                           │
              │ ★ matrix_tree_theorem ★   │
              └───────────────────────────┘
```

---

## Appendix C — Build Status

- **Warnings:** 0
- **Sorries (proof modules):** 0
- **Unused declarations:** 0
- **Build:** `lake build` succeeds
- **Lean version:** `leanprover/lean4:v4.28.0`

