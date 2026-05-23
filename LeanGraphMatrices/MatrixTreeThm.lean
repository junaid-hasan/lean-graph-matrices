import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.IncMatrix
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.EquivFin

import LeanGraphMatrices.CauchyBinet
import LeanGraphMatrices.SignIncMatrix
import LeanGraphMatrices.SpanningTree
import LeanGraphMatrices.TreeDet
import LeanGraphMatrices.NonTreeDet

open Matrix Finset

universe u

/-! ### Column permutation lemma (vendored from algebraic-combinatorics DesnanotJacobi.lean:425) -/

lemma det_submatrix_col_perm' {m : ℕ} {S : Type*} [CommRing S]
    (A : Matrix (Fin m) (Fin m) S) (σ : Equiv.Perm (Fin m)) :
    (A.submatrix id σ).det = Equiv.Perm.sign σ * A.det := by
  have h1 : (A.submatrix id σ).det = (Matrix.transpose (A.submatrix id σ)).det :=
    (Matrix.det_transpose _).symm
  have h2 : Matrix.transpose (A.submatrix id σ) = (Matrix.transpose A).submatrix σ id := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.submatrix_apply, id_eq]
  have h3 : ((Matrix.transpose A).submatrix σ id).det = Equiv.Perm.sign σ * (Matrix.transpose A).det :=
    Matrix.det_permute σ (Matrix.transpose A)
  have h4 : (Matrix.transpose A).det = A.det := Matrix.det_transpose A
  rw [h1, h2, h3, h4]

lemma det_sq_submatrix_col_perm {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ) (σ : Equiv.Perm (Fin m)) :
    (A.submatrix id σ).det ^ 2 = A.det ^ 2 := by
  rw [det_submatrix_col_perm' A σ]
  have h_sq : ((Equiv.Perm.sign σ : ℤ) ^ 2) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with (h | h)
    · simp [h]
    · simp [h]
  rw [mul_pow]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

variable {V : Type} [Fintype V] [LinearOrder V] [DecidableEq V]

/-!
# Matrix Tree Theorem — Main Assembly

**IMPORTANT**: `AlgebraicCombinatorics.CauchyBinet.cauchyBinet` is ALREADY PROVED in
the vendored `LeanGraphMatrices/CauchyBinet.lean`. Do NOT re-prove it. We only need:
1. A transport lemma that applies it to fintype matrices (≈30 lines)
2. A counting lemma linking the sum to `Fintype.card (SpanningTree G)`.

The existing lemmas (all 0 sorries):
* `LeanGraphMatrices.SignIncMatrix.redLapMatrix_eq_reducedSignedInc_mul_transpose`
* `LeanGraphMatrices.TreeDet.signedInc_det_tree`  (det = ±1 for tree subsets)
* `LeanGraphMatrices.NonTreeDet.signedInc_det_nontree`  (det = 0 for non-tree subsets)
* `LeanGraphMatrices.TreeDet.edgeEmbedding`  (injective embedding of vertices into edges)
* `LeanGraphMatrices.SpanningTree` has `Fintype (SpanningTree G)` and `exists_leaf`
-/

section cauchyBinetSymmetric

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [LinearOrder J]

noncomputable def colsSquareSubmatrix (A : Matrix I J ℤ) (S : Finset J)
    (hS : S.card = Fintype.card I) : Matrix (Fin (Fintype.card I)) (Fin (Fintype.card I)) ℤ :=
  A.submatrix (Fintype.equivFin I).symm (S.orderEmbOfFin hS)

set_option maxHeartbeats 800000 in
theorem cauchyBinet_fintype_symmetric (A : Matrix I J ℤ) :
    (A * Aᵀ).det =
    ∑ S ∈ (univ : Finset J).powersetCard (Fintype.card I),
      if hS : S.card = Fintype.card I then
        (colsSquareSubmatrix A S hS).det ^ 2
      else 0 := by
  set n := Fintype.card I
  set m := Fintype.card J
  let eI : I ≃ Fin n := Fintype.equivFin I
  let eJ : J ≃ Fin m := Fintype.equivFin J
  set A' : Matrix (Fin n) (Fin m) ℤ := A.submatrix eI.symm eJ.symm with hA'
  -- Step 1: det(A Aᵀ) = det(A' (A')ᵀ) via reindexing
  have h_det : (A * Aᵀ).det = (A' * (A')ᵀ).det := by
    calc
      (A * Aᵀ).det = ((A * Aᵀ).submatrix eI.symm eI.symm).det := by
        rw [Matrix.det_submatrix_equiv_self eI.symm]
      _ = (A.submatrix eI.symm eJ.symm * Aᵀ.submatrix eJ.symm eI.symm).det := by
        rw [Matrix.submatrix_mul A Aᵀ eI.symm eJ.symm eI.symm eJ.symm.bijective]
      _ = (A' * (A.submatrix eI.symm eJ.symm)ᵀ).det := by
        rw [Matrix.transpose_submatrix]
      _ = (A' * (A')ᵀ).det := by rw [hA']
  rw [h_det]
  -- Step 2: apply Cauchy-Binet (ALREADY PROVED)
  rw [AlgebraicCombinatorics.CauchyBinet.cauchyBinet A' (A')ᵀ]
  -- Step 3: simplify each term: det(cols) * det(rows) = det(cols)²
  have h_term_sq : ∀ (T : Finset (Fin m)) (hT : T.card = n),
      (AlgebraicCombinatorics.CauchyBinet.colsSubmatrix A' T hT).det *
      (AlgebraicCombinatorics.CauchyBinet.rowsSubmatrix (A')ᵀ T hT).det =
      (AlgebraicCombinatorics.CauchyBinet.colsSubmatrix A' T hT).det ^ 2 := by
    intro T hT
    have h_rows_eq : AlgebraicCombinatorics.CauchyBinet.rowsSubmatrix (A')ᵀ T hT =
        (AlgebraicCombinatorics.CauchyBinet.colsSubmatrix A' T hT)ᵀ := by
      ext i j
      simp [AlgebraicCombinatorics.CauchyBinet.rowsSubmatrix,
        AlgebraicCombinatorics.CauchyBinet.colsSubmatrix,
        Matrix.transpose_apply, Matrix.submatrix_apply]
    simp [h_rows_eq, Matrix.det_transpose, pow_two]
  have h_sum_sq : (∑ T ∈ (univ : Finset (Fin m)).powersetCard n,
      if hT : T.card = n then
        (AlgebraicCombinatorics.CauchyBinet.colsSubmatrix A' T hT).det *
        (AlgebraicCombinatorics.CauchyBinet.rowsSubmatrix (A')ᵀ T hT).det
      else 0) =
    (∑ T ∈ (univ : Finset (Fin m)).powersetCard n,
      if hT : T.card = n then
        (AlgebraicCombinatorics.CauchyBinet.colsSubmatrix A' T hT).det ^ 2
      else 0) := by
    refine sum_congr rfl (fun T hT => ?_)
    split_ifs with hcard
    · rw [h_term_sq T hcard]
    · rfl
  rw [h_sum_sq]
  -- Step 4: Transport the sum from Fin m subsets to J subsets via f T := map eJ.symm T.
  let f : Finset (Fin m) → Finset J := fun T => map eJ.symm.toEmbedding T
  apply Finset.sum_nbij f
  · -- f maps powersetCard n univ to powersetCard n univ
    intro T hT
    simp only [Finset.mem_coe, mem_powersetCard] at hT ⊢
    exact ⟨subset_univ _, by rw [card_map, hT.2]⟩
  · -- f is injective on the domain
    intro T₁ _ T₂ _ h_eq
    exact map_injective eJ.symm.toEmbedding h_eq
  · -- f is surjective
    intro S hS
    simp only [Set.mem_image, Finset.mem_coe, mem_powersetCard] at hS ⊢
    exact ⟨map eJ.toEmbedding S,
           ⟨subset_univ _, by rw [card_map, hS.2]⟩,
           by dsimp [f]; ext x; simp⟩
  · -- terms agree
    intro T hT
    have h_card_fT : (f T).card = T.card := card_map _
    have h_card : T.card = n := (mem_powersetCard.mp hT).2
    have h_card' : (f T).card = Fintype.card I := by rw [h_card_fT, h_card]
    rw [dif_pos h_card, dif_pos h_card']
    have hL : (AlgebraicCombinatorics.CauchyBinet.colsSubmatrix A' T h_card) =
        A.submatrix eI.symm (eJ.symm ∘ T.orderEmbOfFin h_card) := by
      ext i j
      simp [AlgebraicCombinatorics.CauchyBinet.colsSubmatrix, hA', Matrix.submatrix_apply]
    have hR : colsSquareSubmatrix A (f T) h_card' =
        A.submatrix eI.symm ((f T).orderEmbOfFin h_card') := by
      dsimp [colsSquareSubmatrix]
    rw [hL, hR]; dsimp [f]
    have h_perm : ∃ σ : Equiv.Perm (Fin n), (Finset.orderEmbOfFin (f T) h_card') = (eJ.symm ∘ T.orderEmbOfFin h_card) ∘ σ := by
      have h_perm : ∀ x : Fin n, ∃ y : Fin n, (f T).orderEmbOfFin h_card' x = eJ.symm (T.orderEmbOfFin h_card y) := by
        intro x
        have h_mem : (f T).orderEmbOfFin h_card' x ∈ f T := by
          exact Finset.orderEmbOfFin_mem _ _ _;
        rw [ Finset.mem_map ] at h_mem;
        obtain ⟨ y, hy, hy' ⟩ := h_mem;
        obtain ⟨ z, hz ⟩ := Finset.mem_image.mp ( show y ∈ Finset.image ( fun z => T.orderEmbOfFin h_card z ) ( Finset.univ : Finset ( Fin n ) ) from by
                                                    grind +suggestions );
        exact ⟨ z, by aesop ⟩;
      choose σ hσ using h_perm;
      exact ⟨ Equiv.ofBijective σ ( Finite.injective_iff_bijective.mp ( fun x y hxy => by simpa [ hσ ] using StrictMono.injective ( show StrictMono ( fun x => ( f T ).orderEmbOfFin h_card' x ) from by simp +decide [ StrictMono ] ) <| by aesop ) ), funext hσ ⟩;
    obtain ⟨ σ, hσ ⟩ := h_perm;
    have := det_submatrix_col_perm' ( A.submatrix ( ⇑eI.symm ) ( ⇑eJ.symm ∘ ⇑( T.orderEmbOfFin h_card ) ) ) σ;
    convert congr_arg ( · ^ 2 ) this.symm using 1;
    · cases' Int.units_eq_one_or ( Equiv.Perm.sign σ : ℤˣ ) with h h <;> simp +decide [ h ];
    · exact hσ.symm ▸ rfl

end cauchyBinetSymmetric


/-! ## Counting lemma

The sum Σ_S det(B₀[S])² over subsets S of edges of size |V|-1
equals the number of spanning trees of G.

PROOF SKETCH:
- By TreeDet.signedInc_det_tree, if S comes from a spanning tree, det(B₀[S]) = ±1, so det² = 1.
- By NonTreeDet.signedInc_det_nontree, if S does NOT come from a spanning tree, det = 0, so det² = 0.
- Thus the sum counts exactly those S that correspond to spanning trees.
- The map T ↦ image(edgeEmbedding T q) is a bijection between SpanningTree G and such S.
- Therefore the sum equals Fintype.card (SpanningTree G).

Use these existing lemmas:
  TreeDet.signedInc_det_tree (T : SpanningTree G) (q : V) : det = 1 ∨ det = -1
  NonTreeDet.signedInc_det_nontree (q : V) (S : {v // v ≠ q} ↪ Sym2 V) (hNotTree : ¬ IsTree ...) : det = 0
  TreeDet.edgeEmbedding (T : SpanningTree G) (q : V) : ({v // v ≠ q}) ↪ Sym2 V
-/

variable (G : SimpleGraph V) [DecidableRel G.Adj]

section CountingHelpers
variable [LinearOrder (Sym2 V)] [DecidableEq (Sym2 V)] (q : V)

/-- Embedding from finset: given S with |S| = n, construct an embedding {v ≠ q} → Sym2 V. -/
noncomputable def embeddingFromFinset
    (S : Finset (Sym2 V)) (hS : S.card = Fintype.card {v : V // v ≠ q}) :
    {v : V // v ≠ q} ↪ Sym2 V :=
  ⟨(S.orderEmbOfFin hS) ∘ (Fintype.equivFin {v : V // v ≠ q}),
   (S.orderEmbOfFin hS).injective.comp (Fintype.equivFin _).injective⟩

/-
colsSquareSubmatrix det = submatrix id (embeddingFromFinset) det.
    Row reindexing by equivFin.symm is absorbed by det_submatrix_equiv_self.
-/
lemma colsSquareSubmatrix_det_eq
    (S : Finset (Sym2 V)) (hS : S.card = Fintype.card {v : V // v ≠ q}) :
    (colsSquareSubmatrix (reducedSignedIncMatrix G q) S hS).det =
    ((reducedSignedIncMatrix G q).submatrix id (embeddingFromFinset q S hS)).det := by
  unfold colsSquareSubmatrix embeddingFromFinset;
  rw [ ← Matrix.det_reindex_self ( Fintype.equivFin { v : V // v ≠ q } ).symm ] ; aesop;

/-- The finset of tree edges, via the edgeEmbedding. -/
noncomputable def treeEdgeFinset (T : SpanningTree G) : Finset (Sym2 V) :=
  Finset.image (edgeEmbedding T q) Finset.univ

lemma treeEdgeFinset_card (T : SpanningTree G) :
    (treeEdgeFinset G q T).card = Fintype.card {v : V // v ≠ q} := by
  simp [treeEdgeFinset, Finset.card_image_of_injective _ (edgeEmbedding T q).injective]

lemma treeEdgeFinset_mem_powersetCard (T : SpanningTree G) :
    treeEdgeFinset G q T ∈ (Finset.univ : Finset (Sym2 V)).powersetCard
      (Fintype.card {v : V // v ≠ q}) := by
  rw [Finset.mem_powersetCard]
  exact ⟨Finset.subset_univ _, treeEdgeFinset_card G q T⟩

lemma treeEdgeFinset_injective :
    Function.Injective (fun T : SpanningTree G => treeEdgeFinset G q T) := by
  intro T₁ T₂ h_eq;
  -- By definition of treeEdgeFinset, we know that T₁.Tree.edgeSet = T₂.Tree.edgeSet.
  have h_edgeSet_eq : T₁.Tree.edgeSet = T₂.Tree.edgeSet := by
    have h_edgeSet_eq : ∀ T : SpanningTree G, T.Tree.edgeSet = Set.range (edgeEmbedding T q) := by
      intro T
      have h_card : Finset.card (Finset.image (edgeEmbedding T q) Finset.univ) = Finset.card (T.Tree.edgeFinset) := by
        have := T.isTree.card_edgeFinset; simp_all +decide [ Fintype.card_subtype ] ;
        rw [ Finset.card_image_of_injective _ ( edgeEmbedding T q |>.injective ), Finset.card_univ ] ; simp +decide [ this.symm ] ;
      have h_edgeSet_eq : Finset.image (edgeEmbedding T q) Finset.univ = T.Tree.edgeFinset := by
        exact Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr fun v _ => by simpa using treeParent_edge_mem T q v ) ( by aesop );
      simp_all +decide [ Finset.ext_iff, Set.ext_iff ];
    simp_all +decide [ Finset.ext_iff, Set.ext_iff ];
    ext v w; simp_all +decide [ treeEdgeFinset ] ;
    convert h_edgeSet_eq T₁ s(v, w) using 1 ; convert h_edgeSet_eq T₂ s(v, w) using 1 ; aesop;
  cases T₁ ; cases T₂ ; aesop

/-
det² of the tree finset = 1.
-/
lemma det_sq_tree_eq_one (T : SpanningTree G) :
    (colsSquareSubmatrix (reducedSignedIncMatrix G q)
      (treeEdgeFinset G q T) (treeEdgeFinset_card G q T)).det ^ 2 = 1 := by
  -- The embeddings have the same range (.range = .range).
  -- So they differ by a permutation: embeddingFromFinset q (treeEdgeFinset G q T) hS = (edgeEmbedding T q) ∘ σ.
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm {v : V // v ≠ q},
    embeddingFromFinset q (treeEdgeFinset G q T) (treeEdgeFinset_card G q T) = (edgeEmbedding T q) ∘ σ := by
      have h_perm : ∀ v : {v : V // v ≠ q}, ∃ w : {v : V // v ≠ q}, edgeEmbedding T q w = embeddingFromFinset q (treeEdgeFinset G q T) (treeEdgeFinset_card G q T) v := by
        intro v
        simp [embeddingFromFinset];
        have := Finset.mem_image.mp ( Finset.orderEmbOfFin_mem ( treeEdgeFinset G q T ) ( treeEdgeFinset_card G q T ) ( Fintype.equivFin { v // ¬v = q } v ) ) ; aesop;
      choose σ hσ using h_perm;
      have hσ_inj : Function.Injective σ := by
        intro v w hvw; have := hσ v; have := hσ w; aesop;
      exact ⟨ Equiv.ofBijective σ ⟨ hσ_inj, Finite.injective_iff_surjective.mp hσ_inj ⟩, funext fun x => hσ x ▸ rfl ⟩;
  -- By colsSquareSubmatrix_det_eq, det(colsSquareSubmatrix B₀ (treeEdgeFinset G q T) _) = det(B₀.submatrix id (embeddingFromFinset q (treeEdgeFinset G q T) _)).
  have h_det_eq : (colsSquareSubmatrix (reducedSignedIncMatrix G q) (treeEdgeFinset G q T) (treeEdgeFinset_card G q T)).det =
    ((reducedSignedIncMatrix G q).submatrix id (edgeEmbedding T q ∘ σ)).det := by
      rw [colsSquareSubmatrix_det_eq];
      grind;
  -- By det_submatrix_col_perm, det(B₀.submatrix id ((edgeEmbedding T q) ∘ σ)) = sign(σ) * det(B₀.submatrix id (edgeEmbedding T q)).
  have h_det_perm : ((reducedSignedIncMatrix G q).submatrix id (edgeEmbedding T q ∘ σ)).det =
    (Equiv.Perm.sign σ) * ((reducedSignedIncMatrix G q).submatrix id (edgeEmbedding T q)).det := by
      convert det_submatrix_col_perm' _ _ using 1;
      rotate_left;
      convert rfl;
      rotate_left;
      convert Matrix.det_reindex_self ( Fintype.equivFin { v : V // v ≠ q } ) _;
      exact Equiv.permCongr ( Fintype.equivFin { v // v ≠ q } ) σ;
      · simp +decide [ Matrix.submatrix, Matrix.det_apply' ];
        refine' Finset.sum_bij ( fun x _ => Equiv.permCongr ( Fintype.equivFin { v // ¬v = q } ) x ) _ _ _ _ <;> simp +decide [ Equiv.Perm.sign_permCongr ];
        · exact fun b => ⟨ ( Fintype.equivFin { v // ¬v = q } ).symm.permCongr b, by ext; simp +decide ⟩;
        · exact fun a => by rw [ ← Equiv.prod_comp ( Fintype.equivFin { v // ¬v = q } |> Equiv.symm ) ] ;
      · simp +decide [ Equiv.Perm.sign_permCongr ];
  have h_det_tree : ((reducedSignedIncMatrix G q).submatrix id (edgeEmbedding T q)).det = 1 ∨ ((reducedSignedIncMatrix G q).submatrix id (edgeEmbedding T q)).det = -1 := by
    grind +suggestions;
  cases h_det_tree <;> simp_all +decide [ sq ]

/-
For S not corresponding to any spanning tree, det² = 0.
-/
lemma det_sq_nontree_eq_zero
    (S : Finset (Sym2 V)) (hS : S.card = Fintype.card {v : V // v ≠ q})
    (hNot : ∀ T : SpanningTree G, treeEdgeFinset G q T ≠ S) :
    (colsSquareSubmatrix (reducedSignedIncMatrix G q) S hS).det ^ 2 = 0 := by
  have h_embedding : ((reducedSignedIncMatrix G q).submatrix id (embeddingFromFinset q S hS)).det = 0 := by
    apply Classical.byContradiction
    intro h_nonzero;
    -- If the determinant is non-zero, then the submatrix must correspond to a spanning tree.
    obtain ⟨T, hT⟩ : ∃ T : SpanningTree G, edgeGraph q (embeddingFromFinset q S hS) = T.Tree := by
      have h_tree : ∀ v : {v : V // v ≠ q}, (embeddingFromFinset q S hS v) ∈ G.edgeSet := by
        intro v
        by_contra h_not_in_G;
        have h_col_zero : ∀ w : {v : V // v ≠ q}, signedIncMatrix G w.val (embeddingFromFinset q S hS v) = 0 := by
          intro w
          simp [signedIncMatrix, h_not_in_G];
          cases h : ( embeddingFromFinset q S hS ) v ; aesop;
        exact h_nonzero <| Matrix.det_eq_zero_of_column_eq_zero v fun w => h_col_zero w;
      have h_tree : edgeGraph q (embeddingFromFinset q S hS) ≤ G := by
        intro v w hvw; simp_all +decide [ edgeGraph ] ;
        grind +suggestions;
      exact ⟨ ⟨ _, h_tree, by
        grind +suggestions ⟩, rfl ⟩;
    apply hNot T;
    refine' Finset.eq_of_subset_of_card_le ( fun x hx => _ ) _ <;> simp_all +decide [ Finset.card_image_of_injective, Function.Injective ];
    · replace hT := congr_arg ( fun g => g.edgeSet ) hT ; simp_all +decide [ Set.ext_iff, edgeGraph ] ;
      obtain ⟨ a, ha ⟩ := Finset.mem_image.mp hx; specialize hT x; simp_all +decide [ embeddingFromFinset ] ;
      obtain ⟨ ⟨ a, ha, ha' ⟩, hx ⟩ := hT.mpr ( by
        exact ha ▸ treeParent_edge_mem T q a ) ; exact ha' ▸ Finset.orderEmbOfFin_mem _ _ _;
    · have := T.isTree.card_edgeFinset; simp_all +decide [ Fintype.card_subtype ] ;
      rw [ ← this, treeEdgeFinset_card ];
      simp +decide [ Fintype.card_subtype_compl ];
      exact Nat.le_sub_one_of_lt ( by linarith );
  grind +suggestions

end CountingHelpers

theorem sum_det_squares_eq_spanningTree_card [LinearOrder (Sym2 V)]
    [DecidableEq (Sym2 V)] (q : V) :
    (∑ S ∈ (univ : Finset (Sym2 V)).powersetCard (Fintype.card {v : V // v ≠ q}),
      if hS : S.card = Fintype.card {v : V // v ≠ q} then
        (colsSquareSubmatrix (reducedSignedIncMatrix G q) S hS).det ^ 2
      else (0 : ℤ))
    = (Fintype.card (SpanningTree G) : ℤ) := by
  norm_num [ Finset.sum_ite ] at *;
  rw [ ← Finset.sum_subset ( show Finset.image ( fun T : SpanningTree G => treeEdgeFinset G q T ) Finset.univ ⊆ Finset.powersetCard ( Fintype.card V - 1 ) Finset.univ from ?_ ) ];
  · rw [ Finset.sum_image ] <;> norm_num [ treeEdgeFinset_card, treeEdgeFinset_injective ];
    rw [ Finset.sum_congr rfl fun x hx => det_sq_tree_eq_one G q x ] ; norm_num;
  · intro S hS hS';
    split_ifs <;> simp_all +decide [ Finset.mem_powersetCard ];
    have := det_sq_nontree_eq_zero G q S ( by aesop ) hS'; aesop;
  · simp +decide [ Finset.subset_iff ];
    intro T; rw [ treeEdgeFinset_card ] ; simp +decide [ Fintype.card_subtype_compl ] ;

/-! ### Matrix Tree Theorem -/

theorem matrix_tree_theorem [LinearOrder (Sym2 V)] [DecidableEq (Sym2 V)]
    (G : SimpleGraph V) [DecidableRel G.Adj] (q : V) :
    ((G.lapMatrix ℤ).submatrix (fun (x : {v : V // v ≠ q}) => x.val)
                                (fun (x : {v : V // v ≠ q}) => x.val)).det
    = (Fintype.card (SpanningTree G) : ℤ) := by
  rw [redLapMatrix_eq_reducedSignedInc_mul_transpose G q]
  rw [cauchyBinet_fintype_symmetric (reducedSignedIncMatrix G q)]
  rw [sum_det_squares_eq_spanningTree_card G q]