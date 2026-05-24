# Matrix Tree Theorem (Kirchhoff's Theorem) for Simple Graphs

**Statement:** For any finite simple graph $G$ and any vertex $q$:

$$\det(L_0(G, q)) = \text{number of spanning trees of } G$$

where $L_0(G,q)$ is the reduced Laplacian — the Laplacian matrix with the $q$-th row and column removed.

---

## File Map

| File | Purpose |
|---|---|
| `PermFinset.lean` | Permutation/set utilities (dependency for Cauchy-Binet) |
| `CauchyBinet.lean` | Cauchy-Binet formula for determinants (vendored from [faabian/algebraic-combinatorics](https://github.com/faabian/algebraic-combinatorics), CC BY-NC 4.0) |
| `SignIncMatrix.lean` | Signed incidence matrix $B$, reduced signed incidence matrix $B_0$, and the factorization $L_0 = B_0 \cdot B_0^T$ |
| `SpanningTree.lean` | `SpanningTree G` type, `Fintype` instance, `exists_leaf` lemma |
| `TreeDet.lean` | **Lemma:** for a spanning tree $T$, $\det(B_0[T]) = \pm 1$ (so $\det^2 = 1$) |
| `NonTreeDet.lean` | **Lemma:** for a selection of edges that does *not* form a spanning tree, $\det(B_0[S]) = 0$ |
| `MatrixTreeThm.lean` | **Main theorem** — chains the above lemmas plus Cauchy-Binet to count spanning trees |
| `Basic.lean` | Minimal imports (root dependencies) |

---

## Proof Blueprint

### Step 1 — Laplacian Factorization

Define the **signed incidence matrix** $B$: rows indexed by vertices, columns by edges. Entry $(v, e)$ is $+1$ if $v$ is the min endpoint of $e$, $-1$ if max, $0$ otherwise.

Remove the row for root $q$ to get $B_0$ (the **reduced** signed incidence matrix, $(|V|-1) \times |E|$).

Prove: $L = B \cdot B^T$, and consequently $L_0 = B_0 \cdot B_0^T$.

→ **File:** `SignIncMatrix.lean`

### Step 2 — Cauchy-Binet

Apply Cauchy-Binet to $B_0 \cdot B_0^T$ (an $(|V|-1) \times |E|$ matrix times its transpose):

$$\det(L_0) = \det(B_0 \cdot B_0^T) = \sum_{\substack{S \subseteq E \\ |S| = |V|-1}} \det(B_0[S])^2$$

where $B_0[S]$ is the square submatrix formed by taking all rows of $B_0$ and the columns indexed by $S$.

→ **File:** `CauchyBinet.lean` (vendored)

### Step 3 — Determinant Classification

**If $S$ is the edge set of a spanning tree $T$:**  
The columns of $B_0[S]$ are the parent edges of $T$ rooted at $q$. A sign-permutation argument shows $\det(B_0[S]) = \pm 1$, so $\det^2 = 1$.

→ **File:** `TreeDet.lean`

**If $S$ is *not* the edge set of any spanning tree:**  
Either $S$ contains an edge not in $G$ (giving a zero column, so $\det = 0$), or the graph formed by $S$ is disconnected or cyclic. In either case, $\det(B_0[S]) = 0$.

→ **File:** `NonTreeDet.lean`

### Step 4 — Counting

The sum $\sum_S \det(B_0[S])^2$ counts exactly those $S$ that are spanning tree edge sets — each contributes 1, all others contribute 0. Moreover, the map $T \mapsto \text{edgeFinset}(T)$ is a bijection between `SpanningTree G` and such $S$.

Therefore the sum equals `Fintype.card (SpanningTree G)`.

→ **File:** `MatrixTreeThm.lean`

### Step 5 — Assembly

```
matrix_tree_theorem (G : SimpleGraph V) (q : V) :
    det(reduced Laplacian at q) = (Fintype.card (SpanningTree G) : ℤ)
```

Proved by chaining Steps 1–4 via `rw`:

```lean
rw [redLapMatrix_eq_reducedSignedInc_mul_transpose G q]     -- Step 1: L₀ = B₀·B₀ᵀ
rw [cauchyBinet_fintype_symmetric (reducedSignedIncMatrix G q)]  -- Step 2: det = Σ det²
rw [sum_det_squares_eq_spanningTree_card G q]               -- Steps 3-4: Σ det² = #trees
```

---

## Zero Sorries

All proof files have 0 `sorry`s. The project builds with `lake build` (8035 jobs, 0 errors).

```
grep -r "sorry" LeanGraphMatrices/   # returns exit code 1 (no matches)
```

## Acknowledgments

This formalization was completed with assistance from [Aristotle](https://aristotle.harmonic.fun) (Harmonic), an automated theorem prover for Lean 4, which filled the final assembly lemmas in `MatrixTreeThm.lean` and the determinant-zero lemma for non-tree subsets.

The Cauchy-Binet proof is vendored from [faabian/algebraic-combinatorics](https://github.com/faabian/algebraic-combinatorics) ([facebookresearch/algebraic-combinatorics](https://github.com/facebookresearch/algebraic-combinatorics)), licensed under [CC BY-NC 4.0](https://creativecommons.org/licenses/by-nc/4.0/).
