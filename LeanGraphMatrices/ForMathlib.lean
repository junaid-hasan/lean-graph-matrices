import Mathlib

namespace MultilinearMap

variable {R ι M} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- If two `R`-multilinear maps from `R` are equal on 1, then they are equal.

This is the multilinear version of `LinearMap.ext_ring`. -/
@[ext]
theorem ext_ring [Finite ι] ⦃f g : MultilinearMap R (fun _ : ι => R) M⦄ (h : f 1 = g 1) : f = g := by
  ext x
  obtain ⟨_⟩ := nonempty_fintype ι
  have hf := f.map_smul_univ x 1
  have hg := g.map_smul_univ x 1
  simp_all [h, hf, hg]

end MultilinearMap
