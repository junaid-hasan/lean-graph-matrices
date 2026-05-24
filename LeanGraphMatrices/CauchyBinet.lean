/-
Adapted from algebraic-combinatorics
(https://github.com/faabian/algebraic-combinatorics)
(https://github.com/facebookresearch/algebraic-combinatorics)
Original licensed under CC BY-NC 4.0
-/
import Mathlib

/-!
# Cauchy-Binet Formula

This file provides the general Cauchy-Binet formula for det(AB) where A is n×m and B is m×n.
-/

open scoped Matrix BigOperators
open Finset Matrix

namespace AlgebraicCombinatorics

namespace CauchyBinet

variable {R : Type*} [CommRing R]

/-- Submatrix obtained by selecting specific columns of A.
    `cols_S A` selects columns indexed by S. -/
noncomputable def colsSubmatrix {n m : ℕ} (A : Matrix (Fin n) (Fin m) R)
    (S : Finset (Fin m)) (hcard : S.card = n) : Matrix (Fin n) (Fin n) R :=
  A.submatrix id (S.orderEmbOfFin hcard)

/-- Submatrix obtained by selecting specific rows of B.
    `rows_S B` selects rows indexed by S. -/
noncomputable def rowsSubmatrix {n m : ℕ} (B : Matrix (Fin m) (Fin n) R)
    (S : Finset (Fin m)) (hcard : S.card = n) : Matrix (Fin n) (Fin n) R :=
  B.submatrix (S.orderEmbOfFin hcard) id

/-- Helper lemma: when f is not injective, the alternating sum over permutations is 0. -/
lemma det_mul_aux_nonsquare {n m : ℕ} {A : Matrix (Fin n) (Fin m) R} {B : Matrix (Fin m) (Fin n) R}
    {f : Fin n → Fin m} (hf : ¬Function.Injective f) :
    (∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : R) * ∏ i, A (σ i) (f i) * B (f i) i) = 0 := by
  obtain ⟨i, j, hfij, hij⟩ : ∃ i j, f i = f j ∧ i ≠ j := by
    rw [Function.Injective] at hf; push_neg at hf; exact hf
  exact Finset.sum_involution (fun σ _ => σ * Equiv.swap i j)
    (fun σ _ => by
      have h1 : (∏ k, A (σ k) (f k)) = ∏ k, A ((σ * Equiv.swap i j) k) (f k) := by
        refine Fintype.prod_equiv (Equiv.swap i j) _ _ (fun k => ?_)
        simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_self, 
          Equiv.apply_swap_eq_self hfij]
      have h2 : (Equiv.Perm.sign (σ * Equiv.swap i j) : R) = -(Equiv.Perm.sign σ : R) := by 
        simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij]
      simp only [h2, neg_mul, h1, Finset.prod_mul_distrib]; ring)
    (fun σ _ _ => (not_congr Equiv.mul_swap_eq_iff).mpr hij)
    (fun _ _ => Finset.mem_univ _) (fun σ _ => Equiv.mul_swap_involutive i j σ)

/-- Key identity: for a fixed subset S, the sum over permutations gives det(cols_S A) * det(rows_S B). -/
lemma sum_over_subset_eq_det_mul {n m : ℕ} (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin m) (Fin n) R)
    (S : Finset (Fin m)) (hcard : S.card = n) :
    ∑ τ : Equiv.Perm (Fin n), ∑ σ : Equiv.Perm (Fin n), 
      (Equiv.Perm.sign σ : R) * ∏ i, A (σ i) (S.orderEmbOfFin hcard (τ i)) * 
        B (S.orderEmbOfFin hcard (τ i)) i =
    (colsSubmatrix A S hcard).det * (rowsSubmatrix B S hcard).det := by
  let e := S.orderEmbOfFin hcard
  have split_prod : ∀ σ τ : Equiv.Perm (Fin n), 
      (Equiv.Perm.sign σ : R) * ∏ i, A (σ i) (e (τ i)) * B (e (τ i)) i = 
      (Equiv.Perm.sign σ : R) * (∏ i, A (σ i) (e (τ i))) * (∏ i, B (e (τ i)) i) := by
    intro σ τ
    calc (Equiv.Perm.sign σ : R) * ∏ i, A (σ i) (e (τ i)) * B (e (τ i)) i 
        = (Equiv.Perm.sign σ : R) * (∏ i, A (σ i) (e (τ i)) * B (e (τ i)) i) := by ring
      _ = (Equiv.Perm.sign σ : R) * ((∏ i, A (σ i) (e (τ i))) * (∏ i, B (e (τ i)) i)) := by 
          rw [← Finset.prod_mul_distrib]
      _ = (Equiv.Perm.sign σ : R) * (∏ i, A (σ i) (e (τ i))) * (∏ i, B (e (τ i)) i) := by ring
  conv_lhs => arg 2; ext τ; arg 2; ext σ; rw [split_prod σ τ]
  have factor_B : ∀ τ : Equiv.Perm (Fin n),
      ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : R) * (∏ i, A (σ i) (e (τ i))) * 
        (∏ i, B (e (τ i)) i) =
      (∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : R) * ∏ i, A (σ i) (e (τ i))) * 
        (∏ i, B (e (τ i)) i) := by
    intro τ
    have h : ∀ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : R) * (∏ i, A (σ i) (e (τ i))) * 
        (∏ i, B (e (τ i)) i) =
        ((Equiv.Perm.sign σ : R) * ∏ i, A (σ i) (e (τ i))) * (∏ i, B (e (τ i)) i) := fun σ => by ring
    conv_lhs => arg 2; ext σ; rw [h σ]
    rw [← Finset.sum_mul]
  conv_lhs => arg 2; ext τ; rw [factor_B τ]
  have A_sum : ∀ τ : Equiv.Perm (Fin n), 
      ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : R) * ∏ i, A (σ i) (e (τ i)) = 
      (Equiv.Perm.sign τ : R) * (A.submatrix id e).det := by
    intro τ
    have eq1 : ∀ σ : Equiv.Perm (Fin n), ∀ i : Fin n, 
        A (σ i) (e (τ i)) = (A.submatrix id e).submatrix id τ (σ i) i := by
      intro σ i; simp [Matrix.submatrix]
    conv_lhs => arg 2; ext σ; arg 2; arg 2; ext i; rw [eq1 σ i]
    rw [← Matrix.det_apply', Matrix.det_permute' τ]
  conv_lhs => arg 2; ext τ; arg 1; rw [A_sum τ]
  have h4 : ∀ τ : Equiv.Perm (Fin n), 
      (Equiv.Perm.sign τ : R) * (A.submatrix id e).det * ∏ i, B (e (τ i)) i =
      (A.submatrix id e).det * ((Equiv.Perm.sign τ : R) * ∏ i, B (e (τ i)) i) := fun τ => by ring
  conv_lhs => arg 2; ext τ; rw [h4 τ]
  rw [← Finset.mul_sum]
  have B_sum : ∑ τ : Equiv.Perm (Fin n), (Equiv.Perm.sign τ : R) * ∏ i, B (e (τ i)) i = 
      (B.submatrix e id).det := by
    have eq1 : ∀ τ : Equiv.Perm (Fin n), ∀ i : Fin n, B (e (τ i)) i = (B.submatrix e id) (τ i) i := by
      intro τ i; simp [Matrix.submatrix]
    conv_lhs => arg 2; ext τ; arg 2; arg 2; ext i; rw [eq1 τ i]
    rw [← Matrix.det_apply']
  rw [B_sum]; rfl

/-- Helper: orderEmbOfFin applied to the inverse of orderIsoOfFin recovers the original element. -/
private lemma orderEmbOfFin_symm {n m : ℕ} (S : Finset (Fin m)) (hcard : S.card = n) 
    (x : Fin m) (hx : x ∈ S) :
    S.orderEmbOfFin hcard ((S.orderIsoOfFin hcard).symm ⟨x, hx⟩) = x := by
  have h := (S.orderIsoOfFin hcard).apply_symm_apply ⟨x, hx⟩
  have h' : ((S.orderIsoOfFin hcard) ((S.orderIsoOfFin hcard).symm ⟨x, hx⟩)).val = x := by rw [h]
  simp only [Finset.orderEmbOfFin]; convert h'

/-- Helper: orderIsoOfFin.symm applied to orderEmbOfFin gives back the original index. -/
private lemma orderIsoOfFin_symm_orderEmbOfFin {n m : ℕ} (S : Finset (Fin m)) (hcard : S.card = n) 
    (i : Fin n) :
    (S.orderIsoOfFin hcard).symm ⟨S.orderEmbOfFin hcard i, Finset.orderEmbOfFin_mem S hcard i⟩ = i := by
  apply (S.orderIsoOfFin hcard).injective
  simp only [OrderIso.apply_symm_apply]
  ext; rfl

/-- For a fixed S with |S| = n, injective functions with image S correspond bijectively 
    to permutations of Fin n. This allows us to transform the sum over such functions 
    into a sum over permutations. -/
private lemma sum_over_image_eq_sum_perm {n m : ℕ} (S : Finset (Fin m)) (hS : S.card = n) 
    (F : (Fin n → Fin m) → R) :
    ∑ f ∈ ((Finset.univ : Finset (Fin n → Fin m)).filter Function.Injective).filter 
        (fun f => Finset.univ.image f = S), F f =
    ∑ τ : Equiv.Perm (Fin n), F (fun k => S.orderEmbOfFin hS (τ k)) := by
  -- Forward map: τ ↦ (fun k => S.orderEmbOfFin hS (τ k))
  let toFun : Equiv.Perm (Fin n) → (Fin n → Fin m) := fun τ k => S.orderEmbOfFin hS (τ k)
  have htoFun : ∀ τ, toFun τ ∈ ((Finset.univ : Finset (Fin n → Fin m)).filter Function.Injective).filter 
      (fun f => Finset.univ.image f = S) := by
    intro τ; simp only [Finset.mem_filter, Finset.mem_univ, true_and, toFun]
    constructor
    · intro a b h; exact τ.injective ((S.orderEmbOfFin hS).injective h)
    · ext x; simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · intro ⟨k, hk⟩; rw [← hk]; exact Finset.orderEmbOfFin_mem S hS (τ k)
      · intro hx; use τ.symm ((S.orderIsoOfFin hS).symm ⟨x, hx⟩)
        simp only [Equiv.apply_symm_apply]; exact orderEmbOfFin_symm S hS x hx
  -- Inverse map: for f in the filtered set, construct the permutation
  let invFun : (f : Fin n → Fin m) → (hf : Function.Injective f ∧ Finset.univ.image f = S) → 
      Equiv.Perm (Fin n) := fun f hf => Equiv.ofBijective 
    (fun k => (S.orderIsoOfFin hS).symm ⟨f k, by rw [← hf.2]; simp⟩)
    ⟨by intro a b h; have h' := congr_arg (S.orderIsoOfFin hS) h; simp at h'; exact hf.1 h', 
     Finite.injective_iff_surjective.mp (by 
       intro a b h; have h' := congr_arg (S.orderIsoOfFin hS) h; simp at h'; exact hf.1 h')⟩
  symm
  refine Finset.sum_bij' (fun τ _ => toFun τ) 
    (fun f hf => invFun f (by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf; exact hf)) 
    ?_ ?_ ?_ ?_ ?_
  · intro τ _; exact htoFun τ
  · intro f hf; exact Finset.mem_univ _
  · intro τ _; simp only [toFun, invFun]; ext k; simp only [Equiv.ofBijective_apply]; 
    have := orderIsoOfFin_symm_orderEmbOfFin S hS (τ k); simp only [this]
  · intro f hf; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf; funext k
    simp only [toFun, invFun, Equiv.ofBijective_apply]
    exact orderEmbOfFin_symm S hS (f k) (by rw [← hf.2]; simp)
  · intro τ _; rfl

/-- Partition the sum over injective functions by their image. Each fiber over a subset S
    corresponds to a sum over permutations. -/
private lemma sum_injective_eq_sum_over_subsets {n m : ℕ} (F : (Fin n → Fin m) → R) :
    ∑ f ∈ (Finset.univ : Finset (Fin n → Fin m)).filter Function.Injective, F f =
    ∑ S ∈ (Finset.univ : Finset (Fin m)).powersetCard n,
      if h : S.card = n then ∑ τ : Equiv.Perm (Fin n), F (fun i => S.orderEmbOfFin h (τ i)) else 0 := by
  let g : (Fin n → Fin m) → Finset (Fin m) := fun f => Finset.univ.image f
  have hg : ∀ f ∈ (Finset.univ : Finset (Fin n → Fin m)).filter Function.Injective,
      g f ∈ (Finset.univ : Finset (Fin m)).powersetCard n := by
    intro f hf; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    simp only [g, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    rw [Finset.card_image_of_injective _ hf]; simp
  rw [← Finset.sum_fiberwise_of_maps_to hg F]; apply Finset.sum_congr rfl; intro S hS
  simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and] at hS; rw [dif_pos hS]
  have h_fiber : (Finset.filter Function.Injective Finset.univ).filter (fun f => g f = S) =
      ((Finset.univ : Finset (Fin n → Fin m)).filter Function.Injective).filter 
        (fun f => Finset.univ.image f = S) := by ext f; simp [g]
  rw [h_fiber]; exact sum_over_image_eq_sum_perm S hS F

/-- The general Cauchy-Binet formula.
    For an n×m matrix A and an m×n matrix B:
      det(AB) = Σ_{S ⊆ [m], |S|=n} det(cols_S A) · det(rows_S B)
    
    The sum ranges over all n-element subsets S of [m], where cols_S A is the
    n×n matrix formed by selecting columns of A indexed by S (in increasing order),
    and rows_S B is the n×n matrix formed by selecting rows of B indexed by S. -/
theorem cauchyBinet {n m : ℕ} (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin m) (Fin n) R) :
    (A * B).det = ∑ S ∈ (Finset.univ : Finset (Fin m)).powersetCard n,
      if h : S.card = n then
        (colsSubmatrix A S h).det * (rowsSubmatrix B S h).det
      else 0 := by
  -- Expand det(AB) using Leibniz formula
  calc (A * B).det 
      = ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : R) * ∏ i, (A * B) (σ i) i := by 
          rw [Matrix.det_apply']
    _ = ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : R) * 
          ∏ i, ∑ k : Fin m, A (σ i) k * B k i := by rfl
    _ = ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : R) * 
          ∑ f : Fin n → Fin m, ∏ i, A (σ i) (f i) * B (f i) i := by
        congr 1; ext σ; congr 1
        rw [Finset.prod_univ_sum]; simp only [Fintype.piFinset_univ]
    _ = ∑ σ : Equiv.Perm (Fin n), ∑ f : Fin n → Fin m, 
          (Equiv.Perm.sign σ : R) * ∏ i, A (σ i) (f i) * B (f i) i := by
        congr 1; ext σ; rw [mul_sum]
    _ = ∑ f : Fin n → Fin m, ∑ σ : Equiv.Perm (Fin n), 
          (Equiv.Perm.sign σ : R) * ∏ i, A (σ i) (f i) * B (f i) i := by
        rw [Finset.sum_comm]
    _ = ∑ f ∈ (Finset.univ : Finset (Fin n → Fin m)).filter Function.Injective, 
          ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : R) * ∏ i, A (σ i) (f i) * B (f i) i := by
        refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
        intro f _ hf
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
        exact det_mul_aux_nonsquare hf
    _ = _ := by
        -- Use the bijection between injective functions and (subset, permutation) pairs
        rw [sum_injective_eq_sum_over_subsets]
        apply Finset.sum_congr rfl; intro S hS
        split_ifs with h
        · exact sum_over_subset_eq_det_mul A B S h
        · rfl

end CauchyBinet

end AlgebraicCombinatorics
