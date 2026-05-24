import Mathlib.Combinatorics.SimpleGraph.IncMatrix
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Data.Sym.Sym2

open Matrix SimpleGraph Sym2

variable {V : Type} [LinearOrder V] [DecidableEq V] (G : SimpleGraph V)
variable [DecidableRel G.Adj]

/-- The signed incidence matrix of a simple graph, with canonical orientation
    determined by the `LinearOrder` on vertices.

    For each vertex `v` and unordered pair `e`:
    - `+1` if `v` is the smaller endpoint of `e` (per the linear order)
    - `-1` if `v` is the larger endpoint of `e`
    - `0` if `v` is not incident to `e`

    Uses `Sym2.lift` to ensure well-definedness independent of the
    particular `s(a,b)` representation. -/
def signedIncMatrix : Matrix V (Sym2 V) ℤ :=
  fun v e =>
    Sym2.lift ⟨(fun a b =>
      if G.Adj a b then
        if v = min a b then 1 else if v = max a b then -1 else 0
      else 0),
    -- Proof of symmetry: swapping a and b doesn't change the result
    -- because min/max commute and G.Adj is symmetric.
    by
      intro a₁ a₂
      by_cases h : G.Adj a₁ a₂
      · have h' : G.Adj a₂ a₁ := h.symm
        simp [h, h', min_comm a₁ a₂, max_comm a₁ a₂]
      · have h' : ¬ G.Adj a₂ a₁ := by
          intro hba; apply h; exact hba.symm
        simp [h, h']
    ⟩ e

lemma signedIncMatrix_entry_fst {x y : V} (h : G.Adj x y) (hle : x ≤ y) :
    signedIncMatrix G x s(x,y) = 1 := by
  simp [signedIncMatrix, h, hle]

lemma signedIncMatrix_entry_snd {x y : V} (h : G.Adj x y) (hle : x ≤ y) :
    signedIncMatrix G y s(x,y) = -1 := by
  have hne : x ≠ y := G.ne_of_adj h
  calc
    signedIncMatrix G y s(x,y)
        = (if G.Adj x y then (if y = min x y then 1 else if y = max x y then -1 else 0) else 0) := by
      simp [signedIncMatrix]
    _ = (if y = min x y then 1 else if y = max x y then -1 else 0) := by simp [h]
    _ = (if y = x then 1 else if y = y then -1 else 0) := by simp [hle]
    _ = -1 := by simp [hne.symm]

lemma signedIncMatrix_entry_not_incident {v : V} {e : Sym2 V} (h : e ∉ G.incidenceSet v) :
    signedIncMatrix G v e = 0 := by
  revert h
  refine Sym2.ind ?_ e
  intro a b h
  rw [mk'_mem_incidenceSet_iff] at h
  simp only [not_and_or, not_or] at h
  rcases h with (hno_adj | ⟨hne_a, hne_b⟩)
  · simp [signedIncMatrix, hno_adj]
  · by_cases hadj : G.Adj a b
    · by_cases hle : a ≤ b
      · simp [signedIncMatrix, hadj, min_eq_left hle, max_eq_right hle, hne_a, hne_b]
      · have hle' : b ≤ a := (not_le.mp hle).le
        simp [signedIncMatrix, hadj, min_eq_right hle', max_eq_left hle', hne_a, hne_b]
    · simp [signedIncMatrix, hadj]

/-- The reduced signed incidence matrix: drop the row for vertex `q`. -/
def reducedSignedIncMatrix (q : V) : Matrix ({v : V // v ≠ q}) (Sym2 V) ℤ :=
  (signedIncMatrix G).submatrix (fun x => x.val) id

/-- Smoke test: verify entry values on the house graph edge s(0,1). -/
private def houseEdge : (Fin 5) → (Fin 5) → Bool
  | 0, 1 => true
  | 1, 2 => true
  | 2, 3 => true
  | 3, 4 => true
  | 4, 0 => true
  | 1, 4 => true
  | _, _ => false

example : True := by
  let hG : SimpleGraph (Fin 5) := {
    Adj v w := houseEdge v w || houseEdge w v
    symm := by dsimp [Symmetric]; decide
    loopless := ⟨fun v h => by
      simp [houseEdge] at h⟩
  }
  haveI : DecidableRel hG.Adj :=
    fun a b => inferInstanceAs <| Decidable (houseEdge a b || houseEdge b a)

  have h_adj01 : hG.Adj 0 1 := by
    unfold hG; simp [houseEdge]
  have h01le : (0 : Fin 5) ≤ 1 := by decide

  have hfst := signedIncMatrix_entry_fst hG h_adj01 h01le
  have hsnd := signedIncMatrix_entry_snd hG h_adj01 h01le
  guard_hyp hfst : signedIncMatrix hG (0 : Fin 5) s((0 : Fin 5), (1 : Fin 5)) = 1
  guard_hyp hsnd : signedIncMatrix hG (1 : Fin 5) s((0 : Fin 5), (1 : Fin 5)) = -1
  trivial

-- #eval smoke test
def houseGraph : SimpleGraph (Fin 5) := {
  Adj v w := houseEdge v w || houseEdge w v
  symm := by dsimp [Symmetric]; decide
  loopless := ⟨fun v h => by
    simp [houseEdge] at h⟩
}
instance : DecidableRel houseGraph.Adj :=
  fun a b => inferInstanceAs <| Decidable (houseEdge a b || houseEdge b a)

#eval! signedIncMatrix houseGraph (0 : Fin 5) s((0 : Fin 5), (1 : Fin 5))
-- expected: 1

#eval! signedIncMatrix houseGraph (1 : Fin 5) s((0 : Fin 5), (1 : Fin 5))
-- expected: -1

#eval! signedIncMatrix houseGraph (3 : Fin 5) s((0 : Fin 5), (1 : Fin 5))
-- expected: 0


section LaplacianProduct

variable [Fintype V]

omit [Fintype V] in
/-- For any vertex `i` and edge `e`, the signed incidence matrix entry squared
    equals the (unoriented) incidence matrix entry. Both are `1` if `e` is incident
    to `i` and `0` otherwise — the sign (±1) squares away. -/
lemma signedIncMatrix_sq_eq_incMatrix (i : V) (e : Sym2 V) :
    (signedIncMatrix G i e)^2 = (G.incMatrix ℤ) i e := by
  by_cases h : e ∈ G.incidenceSet i
  · rw [G.incMatrix_of_mem_incidenceSet h]
    -- Decompose e into s(a,b) and use the entry lemmas
    rcases Quot.exists_rep e with ⟨p, he⟩
    -- p : V × V, he : Quot.mk (Sym2.Rel V) p = e
    have he_s : s(p.1, p.2) = e := by
      simpa using he
    rw [← he_s]
    rw [← he_s] at h
    rw [mk'_mem_incidenceSet_iff] at h
    rcases h with ⟨hadj, hi⟩
    rcases hi with (hi_eq_a | hi_eq_b)
    · -- hi_eq_a: i = p.1
      subst hi_eq_a
      by_cases hle : p.1 ≤ p.2
      · rw [signedIncMatrix_entry_fst G hadj hle]; norm_num
      · have hle' : p.2 ≤ p.1 := le_of_not_ge hle
        rw [Sym2.eq_swap (a := p.1) (b := p.2), signedIncMatrix_entry_snd G hadj.symm hle']; norm_num
    · -- hi_eq_b: i = p.2
      subst hi_eq_b
      by_cases hle : p.1 ≤ p.2
      · rw [signedIncMatrix_entry_snd G hadj hle]; norm_num
      · have hle' : p.2 ≤ p.1 := le_of_not_ge hle
        rw [Sym2.eq_swap (a := p.1) (b := p.2), signedIncMatrix_entry_fst G hadj.symm hle']; norm_num
  · rw [G.incMatrix_of_notMem_incidenceSet h, signedIncMatrix_entry_not_incident G h]
    norm_num

omit [Fintype V] in
/-- For distinct vertices `i ≠ j` with `G.Adj i j`, the product of signed incidence
    entries for edge `e` is `-1` if `e = s(i,j)` and `0` otherwise. This captures
    that the two endpoints of an edge have opposite signs. -/
lemma signedIncMatrix_mul_of_adj {i j : V} (_hij : i ≠ j) (hadj : G.Adj i j) (e : Sym2 V) :
    signedIncMatrix G i e * signedIncMatrix G j e =
    if e = s(i, j) then (-1 : ℤ) else 0 := by
  by_cases he : e = s(i, j)
  · subst he
    by_cases hle : i ≤ j
    · rw [signedIncMatrix_entry_fst G hadj hle, signedIncMatrix_entry_snd G hadj hle]
      norm_num
    · have hle' : j ≤ i := le_of_not_ge hle
      rw [Sym2.eq_swap (a := i) (b := j)]
      rw [signedIncMatrix_entry_snd G hadj.symm hle', signedIncMatrix_entry_fst G hadj.symm hle']
      norm_num
  · -- e ≠ s(i,j): at least one endpoint is not incident
    by_cases hinc_i : e ∈ G.incidenceSet i
    · have h_not_inc_j : e ∉ G.incidenceSet j := by
        intro hinc_j
        apply he
        have mem_inter : e ∈ G.incidenceSet i ∩ G.incidenceSet j := ⟨hinc_i, hinc_j⟩
        rw [G.incidenceSet_inter_incidenceSet_of_adj hadj, Set.mem_singleton_iff] at mem_inter
        exact mem_inter
      rw [signedIncMatrix_entry_not_incident G h_not_inc_j, mul_zero]
      simp [he]
    · rw [signedIncMatrix_entry_not_incident G hinc_i, zero_mul]
      simp [he]

omit [Fintype V] in
/-- For distinct, non-adjacent vertices `i ≠ j`, the product of signed incidence
    entries for any edge `e` is always `0`, since no edge is incident to both. -/
lemma signedIncMatrix_mul_of_not_adj {i j : V} (hij : i ≠ j) (hnadj : ¬ G.Adj i j) (e : Sym2 V) :
    signedIncMatrix G i e * signedIncMatrix G j e = 0 := by
  -- The intersection of incidence sets is empty
  have h_inter_empty : G.incidenceSet i ∩ G.incidenceSet j = ∅ :=
    G.incidenceSet_inter_incidenceSet_of_not_adj hnadj hij
  by_cases hinc_i : e ∈ G.incidenceSet i
  · have h_not_inc_j : e ∉ G.incidenceSet j := by
      intro hinc_j
      have : e ∈ (∅ : Set (Sym2 V)) := by
        rw [← h_inter_empty]
        exact ⟨hinc_i, hinc_j⟩
      simp at this
    rw [signedIncMatrix_entry_not_incident G h_not_inc_j, mul_zero]
  · rw [signedIncMatrix_entry_not_incident G hinc_i, zero_mul]

/-- The Laplacian matrix equals the signed incidence matrix times its transpose. -/
lemma lapMatrix_eq_signedInc_mul_transpose :
    G.lapMatrix ℤ = signedIncMatrix G * (signedIncMatrix G)ᵀ := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    lapMatrix, degMatrix, adjMatrix, Matrix.diagonal, Matrix.sub_apply, Matrix.of_apply]
  by_cases hij : i = j
  · subst j
    -- LHS: (G.degree i : ℤ) = sum of incident indicator
    -- RHS: ∑ e, (signedIncMatrix G i e)^2
    rw [if_pos rfl, if_neg (G.loopless.irrefl i), sub_zero]
    have hsum : (∑ e : Sym2 V, (signedIncMatrix G i e)^2) = (G.degree i : ℤ) := by
      calc
        (∑ e : Sym2 V, (signedIncMatrix G i e)^2) = (∑ e : Sym2 V, (G.incMatrix ℤ) i e) :=
          Finset.sum_congr rfl (fun e _ => signedIncMatrix_sq_eq_incMatrix G i e)
        _ = (G.degree i : ℤ) := by simp [G.sum_incMatrix_apply]
    simpa [sq] using hsum.symm
  · simp [hij]
    by_cases hadj : G.Adj i j
    · -- LHS: 0 - 1 = -1
      -- RHS: ∑ e, signedIncMatrix G i e * signedIncMatrix G j e
      simp [hadj]
      rw [Finset.sum_congr rfl (fun e _ => signedIncMatrix_mul_of_adj G hij hadj e)]
      simp
    · -- LHS: 0 - 0 = 0
      simp [hadj]
      rw [Finset.sum_congr rfl (fun e _ => signedIncMatrix_mul_of_not_adj G hij hadj e)]
      simp

/-- The reduced Laplacian matrix equals the reduced signed incidence matrix times its transpose.
    This follows directly from the full version by restricting rows and columns. -/
lemma redLapMatrix_eq_reducedSignedInc_mul_transpose (q : V) :
    (G.lapMatrix ℤ).submatrix (fun x : {v // v ≠ q} => x.val) (fun x : {v // v ≠ q} => x.val) =
    reducedSignedIncMatrix G q * (reducedSignedIncMatrix G q)ᵀ := by
  ext i j
  simp [reducedSignedIncMatrix, Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply,
    lapMatrix_eq_signedInc_mul_transpose G]

end LaplacianProduct

/-- Smoke test: verify `lapMatrix = B * Bᵀ` on the house graph. -/
example : (houseGraph.lapMatrix ℤ) = (signedIncMatrix houseGraph * (signedIncMatrix houseGraph)ᵀ) := by
  decide
