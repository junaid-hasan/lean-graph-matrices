import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.IncMatrix
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import LeanGraphMatrices.CauchyBinet

universe u v

variable {V : Type} [Fintype V] [LinearOrder V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- placeholder for set of spanning trees of a graph -/
-- here we take all edge-subsets of size N - 1, where N = number of vertices
def spanningTreeFinset (G : SimpleGraph V) [Fintype G.edgeSet]: Finset (Finset (Sym2 V)) :=
  Finset.powersetCard ((Fintype.card V) - 1) G.edgeFinset

/-- placeholder for reduced Laplacian matrix of a graph -/
def redLapMatrix [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] [AddGroupWithOne ℤ] (q : V) : Matrix {v : V // v ≠ q} {v : V // v ≠ q} ℤ :=
  let inc : {v : V // v ≠ q} → V := fun x => x
  (G.lapMatrix ℤ).submatrix inc inc

/-- placeholder for signed incidence matrix of a graph -/
-- TODO: define signed incidence matrix
noncomputable def signIncMatrix (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V (Sym2 V) ℤ :=
  G.incMatrix ℤ

noncomputable def redSignIncMatrix (G : SimpleGraph V) [DecidableRel G.Adj] (q : V) : Matrix {v : V // v ≠ q} (Sym2 V) ℤ :=
  let inc : {v : V // v ≠ q} → V := fun x => x
  (signIncMatrix G).submatrix inc id


/-- Laplacian matrix is equal to self-product of (signed) incidence matrix -/
lemma lapMatrix_incMatrix_prod (G : SimpleGraph V) [DecidableRel G.Adj] :
  G.lapMatrix ℤ = (signIncMatrix G) * ((signIncMatrix G).transpose) := by
  sorry

lemma redLapMatrix_incMatrix_prod (G : SimpleGraph V) [DecidableRel G.Adj] (q : V) :
  (redLapMatrix G q) = (redSignIncMatrix G q) * ((redSignIncMatrix G q).transpose) := by
  unfold redLapMatrix
  unfold redSignIncMatrix
  simp only [ne_eq, Matrix.transpose_submatrix]
  -- apply lapMatrix_incMatrix_prod
  let A := signIncMatrix G
  rw [← Matrix.submatrix_mul A A.transpose _ id _]
  · rw [lapMatrix_incMatrix_prod G]
  -- prove that id map is bijective
  · simp only [Multiset.bijective_iff_map_univ_eq_univ, id_eq, Multiset.map_id']


/-- determinant of spanning-tree minor of incidence matrix: if S ⊆ E(G), then
      - B₀[S].det is equal to ±1 if S forms a spanning tree
      - B₀[S].det is equal to 0 otherwise -/
def edgeChoiceGraph {q : V} (S : {v : V // v ≠ q} → (Sym2 V)) := SimpleGraph.fromEdgeSet (Set.image S Set.univ)

-- TODO: similar to above
lemma redIncMatrix_submatrix_det_hasCycle (G : SimpleGraph V) (q : V) [Fintype G.edgeSet] (S : {v : V // v ≠ q} ↪ Sym2 V) : ¬(SimpleGraph.IsAcyclic (edgeChoiceGraph S)) → ((redSignIncMatrix G q).submatrix id S).det = 0 :=
  sorry

-- TODO: similar to above
lemma redIncMatrix_submatrix_det_tree (G : SimpleGraph V) (q : V) [Fintype G.edgeSet] (S : {v : V // v ≠ q} ↪ Sym2 V) : SimpleGraph.IsTree (edgeChoiceGraph S) → ((redSignIncMatrix G q).submatrix id S).det ∈ ({1, -1} : Finset ℤ) := by
  sorry

lemma isTree_iff_acyclic_and_card {V : Type} {G : SimpleGraph V} [Finite V] : G.IsTree ↔ G.IsAcyclic ∧ Nat.card ↑G.edgeSet + 1 = Nat.card V := by
  sorry

-- TODO: image of S should contain edges of G;
lemma redIncMatrix_submatrix_det (G : SimpleGraph V) (q : V) [Fintype G.edgeSet] (S : {v : V // v ≠ q} ↪ Sym2 V) : ((redSignIncMatrix G q).submatrix id S).det ∈ ({1, -1, 0} : Finset ℤ) := by
  let H := edgeChoiceGraph S
  simp only [Int.reduceNeg, ne_eq, Finset.mem_insert, Finset.mem_singleton]
  by_cases htree : H.IsTree
  · -- assume H is a tree
    have h_det1 := redIncMatrix_submatrix_det_tree G q S htree
    simp only [Finset.mem_insert, Finset.mem_singleton] at h_det1
    rcases h_det1
    all_goals
      tauto
  · -- assume H is not a tree
    suffices ((redSignIncMatrix G q).submatrix id S).det = 0 from (by tauto)
    rw [isTree_iff_acyclic_and_card] at htree
    simp only [not_and'] at htree
    by_cases h_numEdges : Nat.card ↑H.edgeSet + 1 = Nat.card V
    · --
      apply redIncMatrix_submatrix_det_hasCycle
      exact htree h_numEdges
    · --
      unfold H at h_numEdges
      unfold edgeChoiceGraph at h_numEdges
      simp only [ne_eq, Set.image_univ, SimpleGraph.edgeSet_fromEdgeSet, Nat.card_eq_fintype_card,
        Set.mem_compl_iff, Set.mem_setOf_eq, Set.toFinset_range, Finset.mem_filter,
        Finset.mem_image, Finset.mem_univ, true_and, Subtype.exists, Set.mem_diff, Set.mem_range,
        implies_true, Fintype.card_ofFinset] at h_numEdges
      have h_boundS := Fintype.card_range_le S
      simp only [ne_eq, Fintype.card_ofFinset, Fintype.card_subtype_compl,
        Fintype.card_unique] at h_boundS
      have : Nat.card ↑H.edgeSet + 1 < Nat.card V := by
        simp only [Nat.card_eq_fintype_card]
        sorry
      sorry



/-- statement of Matrix-Tree Theorem -/
theorem matrix_tree_theorem [LinearOrder (Sym2 V)] (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj] : ∀ q : V, (redLapMatrix G q).det = (spanningTreeFinset G).card := by
  intro q
  -- expand reduced Laplacian matrix as self-product of reduced incidence matrix
  rw [redLapMatrix_incMatrix_prod]
  -- apply Cauchy-Binet (use AlgebraicCombinatorics.CauchyBinet.cauchyBinet via transport lemma)
  -- NOTE: need to write a transport lemma bridging Fin n to arbitrary fintypes
  sorry



/-- the number of spanning trees satsifies the deletion-contraction relation;
      #(spanning trees of G) = #(spanning trees of G\e) + #(spanning trees of G/e)  -/
example : Prop := ⊤

/-- the determinant of the reduced Laplacian L₀ satisifies the deletion-contraction relation:
      L₀(G).det = L₀(G\e).det + L₀(G/e)
    if edge e is not a bridge -/
example : Prop := ⊤
