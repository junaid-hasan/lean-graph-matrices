import Mathlib
import LeanGraphMatrices.CauchyBinet
import LeanGraphMatrices.SignIncMatrix
import LeanGraphMatrices.SpanningTree
import LeanGraphMatrices.TreeDet
import LeanGraphMatrices.NonTreeDet

open Matrix
open AlgebraicCombinatorics.CauchyBinet

universe u v

variable {V : Type} [Fintype V] [LinearOrder V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## Reduced Laplacian -/

noncomputable def redLapMatrix (q : V) : Matrix {v : V // v ≠ q} {v : V // v ≠ q} ℤ :=
  (G.lapMatrix ℤ).submatrix Subtype.val Subtype.val

/-!
## Cauchy-Binet bridge: helper lemmas
-/

section CauchyBinetBridge

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [LinearOrder J]

/-- Apply cauchyBinet on Fin types and simplify transpose to get det². -/
lemma cauchyBinet_det_sq {n m : ℕ} (A' : Matrix (Fin n) (Fin m) ℤ) :
    (A' * A'ᵀ).det =
    ∑ S ∈ (Finset.univ : Finset (Fin m)).powersetCard n,
      if h : S.card = n then
        ((A'.submatrix id (S.orderEmbOfFin h)).det) ^ 2
      else 0 := by
  convert cauchyBinet A' A'ᵀ using 1
  refine' Finset.sum_congr rfl _
  intro S hS; split_ifs <;> simp_all +decide [ sq, colsSubmatrix, rowsSubmatrix ]
  exact Or.inl ( by rw [ ← Matrix.det_transpose ] ; rfl )

/-- Reindex the Cauchy-Binet sum from Fin m subsets to J subsets via an equiv. -/
lemma cauchyBinet_reindex_sq {n : ℕ} (M : Matrix (Fin n) J ℤ)
    (eJ : J ≃ Fin (Fintype.card J)) :
    (∑ S ∈ (Finset.univ : Finset (Fin (Fintype.card J))).powersetCard n,
      if h : S.card = n then
        ((M.submatrix id (eJ.symm ∘ S.orderEmbOfFin h)).det) ^ 2
      else 0) =
    (∑ T ∈ (Finset.univ : Finset J).powersetCard n,
      if h : T.card = n then
        ((M.submatrix id (T.orderEmbOfFin h)).det) ^ 2
      else 0) := by
  apply Finset.sum_bij (fun S hS => S.map eJ.symm.toEmbedding)
  · simp +contextual [ Finset.mem_powersetCard, Finset.card_map ]
  · simp +decide [ Finset.ext_iff ]
    exact fun a₁ ha₁ a₂ ha₂ h a => by simpa using h ( eJ.symm a )
  · intro b hb
    use Finset.image eJ.toEmbedding b
    simp_all +decide [ Finset.mem_powersetCard, Finset.card_image_of_injective _ eJ.injective ]
    ext x; aesop
  · intro S hS
    obtain ⟨T, hT⟩ : ∃ T : Finset J, T = S.map eJ.symm.toEmbedding ∧ T.card = n := by
      grind
    have h_perm : ∃ τ : Equiv.Perm (Fin n), ∀ i : Fin n, (T.orderEmbOfFin hT.2) i = eJ.symm (S.orderEmbOfFin (by simpa using Finset.mem_powersetCard.mp hS |>.2) (τ i)) := by
      have h_perm : ∃ τ : Equiv.Perm (Fin n), ∀ i, (T.orderEmbOfFin hT.2) i ∈ Finset.image (fun i => eJ.symm (S.orderEmbOfFin (Finset.mem_powersetCard.mp hS).2 i)) Finset.univ := by
        have h_perm : ∀ i : Fin n, ∃ j : Fin n, (T.orderEmbOfFin hT.2) i = eJ.symm (S.orderEmbOfFin (Finset.mem_powersetCard.mp hS).2 j) := by
          intro i
          have h_mem : (T.orderEmbOfFin hT.2) i ∈ Finset.image (fun j => eJ.symm (S.orderEmbOfFin (Finset.mem_powersetCard.mp hS).2 j)) Finset.univ := by
            have h_perm : ∀ x ∈ T, ∃ j : Fin n, x = eJ.symm (S.orderEmbOfFin (Finset.mem_powersetCard.mp hS).2 j) := by
              intro x hx
              rw [hT.left] at hx
              have h_mem : x ∈ Finset.image (fun j => eJ.symm j) S := by
                grind +extAll
              rw [ Finset.mem_image ] at h_mem; obtain ⟨ j, hj, rfl ⟩ := h_mem; exact ⟨ Finset.mem_image.mp ( show j ∈ Finset.image ( fun k : Fin n => S.orderEmbOfFin ( Finset.mem_powersetCard.mp hS |>.2 ) k ) Finset.univ from by aesop ) |> Classical.choose, by have := Finset.mem_image.mp ( show j ∈ Finset.image ( fun k : Fin n => S.orderEmbOfFin ( Finset.mem_powersetCard.mp hS |>.2 ) k ) Finset.univ from by aesop ) |> Classical.choose_spec; aesop ⟩
            exact Finset.mem_image.mpr ( by obtain ⟨ j, hj ⟩ := h_perm _ ( Finset.orderEmbOfFin_mem T hT.2 i ) ; exact ⟨ j, Finset.mem_univ _, hj.symm ⟩ )
          rw [ Finset.mem_image ] at h_mem; obtain ⟨ j, _, hj ⟩ := h_mem; exact ⟨ j, hj.symm ⟩
        exact ⟨ Equiv.refl _, fun i => by obtain ⟨ j, hj ⟩ := h_perm i; exact Finset.mem_image.mpr ⟨ j, Finset.mem_univ _, hj ▸ rfl ⟩ ⟩
      choose τ hτ using fun i => Finset.mem_image.mp ( h_perm.choose_spec i )
      have h_inj : Function.Injective τ := by
        intro i j hij; have := hτ i; have := hτ j; aesop
      exact ⟨ Equiv.ofBijective τ ⟨ h_inj, Finite.injective_iff_surjective.mp h_inj ⟩, fun i => hτ i |>.2.symm ⟩
    obtain ⟨τ, hτ⟩ := h_perm
    have h_det_eq : (M.submatrix id (T.orderEmbOfFin hT.2)).det = (M.submatrix id (eJ.symm ∘ S.orderEmbOfFin (by simpa using Finset.mem_powersetCard.mp hS |>.2))).det * Equiv.Perm.sign τ := by
      rw [ Matrix.det_apply', Matrix.det_apply' ]
      rw [ Finset.sum_mul ]
      rw [ ← Equiv.sum_comp ( Equiv.mulRight τ ) ] ; simp +decide [hτ, mul_assoc]
      exact Finset.sum_congr rfl fun σ _ => by rw [ ← Equiv.prod_comp ( Equiv.symm τ ) ] ; simp [mul_comm]
    cases' Int.units_eq_one_or ( Equiv.Perm.sign τ ) with h h <;> simp_all +decide [sq]
    · rfl
    · rfl

/-- Cauchy-Binet for `det(A * Aᵀ)` over arbitrary fintypes. -/
lemma det_mul_transpose_cauchyBinet (A : Matrix I J ℤ) :
    (A * Aᵀ).det = ∑ T ∈ (Finset.univ : Finset J).powersetCard (Fintype.card I),
      if h : T.card = Fintype.card I then
        ((A.submatrix (Fintype.equivFin I).symm (T.orderEmbOfFin h)).det) ^ 2
      else 0 := by
  set n := Fintype.card I
  set m := Fintype.card J
  set eI := Fintype.equivFin I
  set eJ := Fintype.equivFin J
  set A' := A.submatrix eI.symm eJ.symm with hA'_def
  have h_prod : A.submatrix eI.symm eJ.symm * (Aᵀ).submatrix eJ.symm eI.symm =
      (A * Aᵀ).submatrix eI.symm eI.symm := by
    rw [submatrix_mul_equiv]
  have h_transpose : (Aᵀ).submatrix eJ.symm eI.symm = A'ᵀ := by
    ext i j; simp [A', Matrix.submatrix, Matrix.transpose]
  have h_det_eq : (A * Aᵀ).det = (A' * A'ᵀ).det := by
    rw [← det_submatrix_equiv_self eI.symm (A * Aᵀ)]
    congr 1; rw [← h_prod, h_transpose]
  rw [h_det_eq, cauchyBinet_det_sq A']
  simp_rw [hA'_def, Matrix.submatrix_submatrix, Function.comp_id]
  exact cauchyBinet_reindex_sq (A.submatrix eI.symm id) eJ

end CauchyBinetBridge

/-!
## Helper lemmas for submatrix determinants
-/

section SubmatrixHelpers

variable {I' J' : Type*} [Fintype I'] [DecidableEq I'] [DecidableEq J']

omit [DecidableEq I'] [DecidableEq J'] in
/-- Two injections with the same image differ by a permutation. -/
lemma exists_perm_of_image_eq
    (f g : I' ↪ J') (h_img : Set.range f = Set.range g) :
    ∃ τ : Equiv.Perm I', ∀ i, g i = f (τ i) := by
  have h_exists_tau : ∀ i : I', ∃! j : I', f j = g i := by
    exact fun i => by rcases h_img.symm.subset ( Set.mem_range_self i ) with ⟨ j, hj ⟩ ; exact ⟨ j, hj, fun k hk => f.injective ( hk.trans hj.symm ) ⟩
  choose τ hτ₁ hτ₂ using h_exists_tau
  have hτ_inj : Function.Injective τ := by
    intro i j hij; have := hτ₁ i; have := hτ₁ j; aesop
  exact ⟨ Equiv.ofBijective τ ⟨ hτ_inj, Finite.injective_iff_surjective.mp hτ_inj ⟩, fun i => Eq.symm ( hτ₁ i ) ⟩

omit [DecidableEq J'] in
/-- Reindexing columns by a permutation changes det by sign; squaring cancels. -/
lemma det_submatrix_sq_eq_of_comp_perm {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R]
    (M : Matrix n J' R) (f : n ↪ J') (τ : Equiv.Perm n) :
    ((M.submatrix id (f ∘ τ)).det) ^ 2 = ((M.submatrix id f).det) ^ 2 := by
  convert congr_arg ( · ^ 2 ) ( Matrix.det_permute' τ ( M.submatrix id f ) ) using 1
  cases' Int.units_eq_one_or ( Equiv.Perm.sign τ ) with h h <;> simp +decide [ h ]

end SubmatrixHelpers

/-!
## Submatrix determinant value: tree (±1) vs non-tree (0)
-/

section SubmatrixDetValue

variable [Fintype G.edgeSet] [LinearOrder (Sym2 V)] (q : V)

omit [Fintype ↑G.edgeSet] [LinearOrder (Sym2 V)] in
/-- If the edges form a spanning tree, det² = 1. -/
lemma signedInc_submatrix_det_sq_tree (f : {v : V // v ≠ q} ↪ Sym2 V)
    (hf_edges : ∀ i, f i ∈ G.edgeSet) (htree : (edgeGraph q f).IsTree) :
    ((reducedSignedIncMatrix G q).submatrix id f).det ^ 2 = 1 := by
  obtain ⟨T, hT⟩ : ∃ T : SpanningTree G, T.Tree = edgeGraph q f := by
    refine' ⟨ ⟨ edgeGraph q f, _, _ ⟩, rfl ⟩;
    · intro v w hvw; simp_all +decide [ edgeGraph ] ;
      grind +suggestions;
    · exact htree;
  have h_det_sq : ((reducedSignedIncMatrix G q).submatrix id (edgeEmbedding T q)).det ^ 2 = 1 := by
    exact sq_eq_one_iff.mpr ( signedInc_det_tree T q )
  obtain ⟨τ, hτ⟩ : ∃ τ : Equiv.Perm {v : V // v ≠ q}, f = edgeEmbedding T q ∘ τ := by
    have h_image_eq : Set.range f = Set.range (edgeEmbedding T q) := by
      have h_card : (edgeGraph q f).edgeFinset.card = Fintype.card {v : V // v ≠ q} := by
        have := htree.card_edgeFinset
        simp_all +decide [ Fintype.card_subtype_compl ]
        exact eq_tsub_of_add_eq this
      have h_card : (edgeGraph q f).edgeFinset = Finset.image f Finset.univ := by
        refine' Finset.eq_of_subset_of_card_le ( fun x hx => _ ) _
        · unfold edgeGraph at hx; aesop
        · rw [ Finset.card_image_of_injective _ f.injective, Finset.card_univ, h_card ]
      have h_card : Finset.image (edgeEmbedding T q) Finset.univ = (edgeGraph q f).edgeFinset := by
        refine' Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr _ ) _
        · intro x hx; exact (by
          convert treeParent_edge_mem T q x using 1
          ext; simp [hT])
        · rw [ Finset.card_image_of_injective _ ( edgeEmbedding T q ).injective ] ; aesop
      simp_all +decide [ Finset.ext_iff, Set.ext_iff ]
    have := exists_perm_of_image_eq f ( edgeEmbedding T q ) h_image_eq
    obtain ⟨ τ, hτ ⟩ := this; use τ.symm; ext i; simp +decide [ hτ ]
  grind +suggestions

omit [Fintype ↑G.edgeSet] [LinearOrder (Sym2 V)] in
/-- If the edges don't form a spanning tree, det² = 0. -/
lemma signedInc_submatrix_det_sq_nontree (f : {v : V // v ≠ q} ↪ Sym2 V)
    (hntree : ¬(edgeGraph q f).IsTree) :
    ((reducedSignedIncMatrix G q).submatrix id f).det ^ 2 = 0 := by
  rw [ sq, signedInc_det_nontree G q f hntree, MulZeroClass.zero_mul ]

end SubmatrixDetValue

/-!
## Main theorem helpers
-/

section MainTheoremHelpers

variable [LinearOrder (Sym2 V)] [Fintype G.edgeSet]

/-
If f sends some index to a non-edge of G, then the column of the reduced signed
    incidence matrix is zero, hence the submatrix has a zero column and det = 0.
-/
omit [LinearOrder (Sym2 V)] [Fintype ↑G.edgeSet] in
lemma det_zero_of_non_edge (q : V) (f : {v : V // v ≠ q} → Sym2 V)
    (i : {v : V // v ≠ q}) (hi : f i ∉ G.edgeSet) :
    ((reducedSignedIncMatrix G q).submatrix id f).det = 0 := by
  rw [ Matrix.det_eq_zero_of_column_eq_zero ];
  exact i;
  intro j; unfold reducedSignedIncMatrix; simp +decide;
  convert signedIncMatrix_entry_not_incident _ _;
  exact fun h => hi <| by simpa using h.1;

/-
`det(M.submatrix eI.symm g)² = det(M.submatrix id (g ∘ eI))²`
-/
omit [Fintype V] [LinearOrder V] [DecidableEq V] [LinearOrder (Sym2 V)] in
lemma det_sq_transport {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I (Sym2 V) ℤ)
    (g : Fin (Fintype.card I) → Sym2 V) :
    ((M.submatrix (Fintype.equivFin I).symm g).det) ^ 2 =
    ((M.submatrix id (g ∘ (Fintype.equivFin I))).det) ^ 2 := by
  convert rfl using 2;
  convert Matrix.det_reindex_self ( Fintype.equivFin I |> Equiv.symm ) _;
  ext i j; simp +decide [ Matrix.submatrix, Matrix.reindex ] ;

/-
Bijection between spanning trees and their edge finsets.
    A spanning tree is uniquely determined by its edge set.

The forward map: spanning tree → its edge finset with proofs.
-/
noncomputable def spanningTreeToEdgeFinset
    (T : SpanningTree G) :
    {S : Finset (Sym2 V) // S.card = Fintype.card V - 1 ∧
      (∀ e ∈ S, e ∈ G.edgeFinset) ∧
      (SimpleGraph.fromEdgeSet (S : Set (Sym2 V))).IsTree} := by
  refine ⟨T.Tree.edgeFinset, ?_, ?_, ?_⟩
  · have := T.isTree.card_edgeFinset; omega
  · intro e he
    simp only [SimpleGraph.mem_edgeFinset] at he ⊢
    exact SimpleGraph.edgeSet_mono T.subG he
  · rw [SimpleGraph.coe_edgeFinset, SimpleGraph.fromEdgeSet_edgeSet]
    exact T.isTree

/-
The forward map is injective: spanning trees with the same edge finset are equal.
-/
omit [LinearOrder V] [DecidableEq V] [DecidableRel G.Adj] [LinearOrder (Sym2 V)] in
lemma spanningTreeToEdgeFinset_injective :
    Function.Injective (spanningTreeToEdgeFinset G) := by
  intro T₁ T₂ h;
  -- Since the edgeFinset is the same, the trees must be the same.
  have h_eq : T₁.Tree.edgeFinset = T₂.Tree.edgeFinset := by
    injection h;
  cases T₁ ; cases T₂ ; aesop

/-
The forward map is surjective.
-/
omit [LinearOrder V] [DecidableRel G.Adj] [LinearOrder (Sym2 V)] in
lemma spanningTreeToEdgeFinset_surjective :
    Function.Surjective (spanningTreeToEdgeFinset G) := by
  intro ⟨ S, hS₁, hS₂, hS₃ ⟩;
  use ⟨ SimpleGraph.fromEdgeSet S, by
    intro v w hvw; specialize hS₂ ( s(v, w) ) ; aesop;, hS₃ ⟩
  generalize_proofs at *;
  simp +decide [ spanningTreeToEdgeFinset, SimpleGraph.edgeFinset ];
  simp +decide [ Finset.disjoint_left, Sym2.diagSet ];
  grind +suggestions

noncomputable def spanningTree_equiv_edgeFinset :
    SpanningTree G ≃ {T : Finset (Sym2 V) // T.card = Fintype.card V - 1 ∧
      (∀ e ∈ T, e ∈ G.edgeFinset) ∧
      (SimpleGraph.fromEdgeSet (T : Set (Sym2 V))).IsTree} :=
  Equiv.ofBijective (spanningTreeToEdgeFinset G)
    ⟨spanningTreeToEdgeFinset_injective G, spanningTreeToEdgeFinset_surjective G⟩

end MainTheoremHelpers

/-! ## Main Theorem -/

/-
Each term in the Cauchy-Binet sum: if T ⊆ G.edgeFinset and fromEdgeSet T is a tree,
    then det² = 1; otherwise det² = 0.
-/
lemma cauchyBinet_term_tree [LinearOrder (Sym2 V)]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (q : V) (T : Finset (Sym2 V)) (h : T.card = Fintype.card {v : V // v ≠ q})
    (hsubset : ∀ e ∈ T, e ∈ G.edgeFinset)
    (htree : (SimpleGraph.fromEdgeSet (T : Set (Sym2 V))).IsTree) :
    ((reducedSignedIncMatrix G q).submatrix
      (Fintype.equivFin {v : V // v ≠ q}).symm (T.orderEmbOfFin h)).det ^ 2 = 1 := by
  -- Define f : {v≠q} ↪ Sym2 V as an embedding whose underlying function is T.orderEmbOfFin h ∘ Fintype.equivFin {v≠q}.
  set f : {v : V // v ≠ q} ↪ Sym2 V := ⟨T.orderEmbOfFin h ∘ Fintype.equivFin {v : V // v ≠ q}, by
    exact Function.Injective.comp ( by aesop_cat ) ( by aesop_cat )⟩
  generalize_proofs at *;
  convert signedInc_submatrix_det_sq_tree G q f _ _ using 1;
  · convert det_sq_transport _ _ using 2;
  · aesop;
  · convert htree using 1;
    have h_range : Set.range f = T := by
      aesop;
    exact h_range ▸ rfl

lemma cauchyBinet_term_nontree [LinearOrder (Sym2 V)]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (q : V) (T : Finset (Sym2 V)) (h : T.card = Fintype.card {v : V // v ≠ q})
    (hntree : ¬((∀ e ∈ T, e ∈ G.edgeFinset) ∧
        (SimpleGraph.fromEdgeSet (T : Set (Sym2 V))).IsTree)) :
    ((reducedSignedIncMatrix G q).submatrix
      (Fintype.equivFin {v : V // v ≠ q}).symm (T.orderEmbOfFin h)).det ^ 2 = 0 := by
  convert det_sq_transport ( reducedSignedIncMatrix G q ) ( T.orderEmbOfFin h ) using 1;
  by_cases hT : ∀ e ∈ T, e ∈ G.edgeFinset <;> simp_all +decide;
  · convert signedInc_submatrix_det_sq_nontree G q ( ⟨ T.orderEmbOfFin h ∘ ( Fintype.equivFin { v // ¬v = q } ), ?_ ⟩ ) ?_ |> Eq.symm using 1
    all_goals generalize_proofs at *;
    · exact Function.Injective.comp ( T.orderEmbOfFin h |>.injective ) ( Fintype.equivFin _ |>.injective );
    · convert hntree using 1;
      congr! 1;
      ext; simp [edgeGraph];
  · obtain ⟨ e, heT, heG ⟩ := hT;
    -- Since $e \in T$ but $e \notin G.edgeSet$, there exists some $i$ such that $T.orderEmbOfFin h i = e$.
    obtain ⟨ i, hi ⟩ : ∃ i : Fin (Fintype.card {v : V // v ≠ q}), T.orderEmbOfFin h i = e := by
      have h_image : Finset.image (fun i : Fin (Fintype.card {v : V // v ≠ q}) => T.orderEmbOfFin h i) Finset.univ = T := by
        exact Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr fun i _ => Finset.orderEmbOfFin_mem _ _ _ ) ( by rw [ Finset.card_image_of_injective _ fun i j hij => by simpa [ Fin.ext_iff ] using hij, Finset.card_fin, h ] );
      exact Finset.mem_image.mp ( h_image.symm ▸ heT ) |> Exists.imp fun i => And.right;
    rw [ det_zero_of_non_edge ];
    lia;
    exact ( Fintype.equivFin { v // v ≠ q } ).symm i;
    aesop

/-
The edgeFinset of a spanning tree lies in the appropriate powersetCard.
-/
omit [LinearOrder V] in
lemma spanningTree_edgeFinset_mem_powersetCard
    [LinearOrder (Sym2 V)] (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (q : V) (T : SpanningTree G) :
    T.Tree.edgeFinset ∈ (Finset.univ : Finset (Sym2 V)).powersetCard
      (Fintype.card {v : V // v ≠ q}) := by
  have := T.isTree.card_edgeFinset; simp_all +decide [ Fintype.card_subtype_compl ] ;
  exact eq_tsub_of_add_eq this

/-
The summand at a spanning tree's edgeFinset equals 1.
-/
lemma summand_at_spanningTree
    [LinearOrder (Sym2 V)] (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (q : V) (T : SpanningTree G)
    (h : T.Tree.edgeFinset.card = Fintype.card {v : V // v ≠ q}) :
    ((reducedSignedIncMatrix G q).submatrix
      (Fintype.equivFin {v : V // v ≠ q}).symm
      (T.Tree.edgeFinset.orderEmbOfFin h)).det ^ 2 = 1 := by
  convert cauchyBinet_term_tree G q ( T.Tree.edgeFinset ) h _ _;
  · simp +decide;
    exact SimpleGraph.edgeSet_mono T.subG;
  · simp +decide [ SimpleGraph.coe_edgeFinset, T.isTree ]

/-
If a finset T in powersetCard is not the edgeFinset of any spanning tree,
    then the summand is 0.
-/
lemma summand_zero_of_not_spanningTree
    [LinearOrder (Sym2 V)] (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (q : V) (T : Finset (Sym2 V))
    (_hT : T ∈ (Finset.univ : Finset (Sym2 V)).powersetCard (Fintype.card {v : V // v ≠ q}))
    (hT_not : T ∉ Finset.image (fun S : SpanningTree G => S.Tree.edgeFinset) Finset.univ)
    (h : T.card = Fintype.card {v : V // v ≠ q}) :
    ((reducedSignedIncMatrix G q).submatrix
      (Fintype.equivFin {v : V // v ≠ q}).symm (T.orderEmbOfFin h)).det ^ 2 = 0 := by
  apply cauchyBinet_term_nontree G q T h;
  contrapose! hT_not;
  refine' Finset.mem_image.mpr ⟨ ⟨ SimpleGraph.fromEdgeSet T, _, _ ⟩, Finset.mem_univ _, _ ⟩ <;> simp_all +decide;
  all_goals simp_all +decide [ Set.subset_def, SimpleGraph.edgeFinset ];
  simp_all +decide [ Finset.disjoint_left, Sym2.diagSet ];
  intro e he; specialize hT_not; have := hT_not.1 e he; simp_all +decide;
  exact fun h => by have := hT_not.1 e he; exact absurd this ( by simp +decide [h] ) ;

lemma cauchyBinet_sum_eq_spanningTree_card [LinearOrder (Sym2 V)]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj] (q : V) :
    (∑ T ∈ (Finset.univ : Finset (Sym2 V)).powersetCard (Fintype.card {v : V // v ≠ q}),
      if h : T.card = Fintype.card {v : V // v ≠ q} then
        ((reducedSignedIncMatrix G q).submatrix
          (Fintype.equivFin {v : V // v ≠ q}).symm (T.orderEmbOfFin h)).det ^ 2
      else 0) =
    Fintype.card (SpanningTree G) := by
  -- Split the sum into two parts: one over spanning trees and one over non-spanning trees.
  have h_split : (∑ T ∈ Finset.powersetCard (Fintype.card {v : V // v ≠ q}) Finset.univ, if h : T.card = Fintype.card {v : V // v ≠ q} then ((reducedSignedIncMatrix G q).submatrix (Fintype.equivFin {v : V // v ≠ q}).symm (T.orderEmbOfFin h)).det ^ 2 else 0) = (∑ T ∈ Finset.image (fun S : SpanningTree G => S.Tree.edgeFinset) Finset.univ, if h : T.card = Fintype.card {v : V // v ≠ q} then ((reducedSignedIncMatrix G q).submatrix (Fintype.equivFin {v : V // v ≠ q}).symm (T.orderEmbOfFin h)).det ^ 2 else 0) := by
    rw [ ← Finset.sum_subset ( show Finset.image ( fun S : SpanningTree G => S.Tree.edgeFinset ) Finset.univ ⊆ Finset.powersetCard ( Fintype.card { v : V // v ≠ q } ) Finset.univ from ?_ ) ];
    · intro T hT hT_not
      have h_det_zero : ((reducedSignedIncMatrix G q).submatrix (Fintype.equivFin {v : V // v ≠ q}).symm (T.orderEmbOfFin (by
      exact Finset.mem_powersetCard.mp hT |>.2))).det ^ 2 = 0 := by
        all_goals generalize_proofs at *;
        apply summand_zero_of_not_spanningTree G q T hT hT_not ‹_›
      generalize_proofs at *; (
      grind +qlia);
    · intro T hT; obtain ⟨ S, _, rfl ⟩ := Finset.mem_image.mp hT; exact spanningTree_edgeFinset_mem_powersetCard G q S;
  generalize_proofs at *; (
  rw [ h_split, Finset.sum_image ];
  · rw [ Finset.sum_congr rfl fun x hx => ?_ ];
    convert Finset.sum_const ( 1 : ℤ );
    · norm_num [ Finset.card_univ ];
    · convert summand_at_spanningTree G q x _ using 1
      generalize_proofs at *; (
      grind +revert);
      convert spanningTree_edgeFinset_mem_powersetCard G q x |> Finset.mem_powersetCard.mp |> And.right using 1;
  · intro S hS T hT h_eq; exact (by
    exact spanningTreeToEdgeFinset_injective G ( Subtype.ext h_eq ));)

theorem matrix_tree_theorem [LinearOrder (Sym2 V)]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj] :
    ∀ q : V, (redLapMatrix G q).det = Fintype.card (SpanningTree G) := by
  intro q
  rw [show redLapMatrix G q = reducedSignedIncMatrix G q * (reducedSignedIncMatrix G q)ᵀ from
    redLapMatrix_eq_reducedSignedInc_mul_transpose G q]
  rw [det_mul_transpose_cauchyBinet]
  exact cauchyBinet_sum_eq_spanningTree_card G q