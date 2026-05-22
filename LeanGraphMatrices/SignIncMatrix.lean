import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.IncMatrix
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
