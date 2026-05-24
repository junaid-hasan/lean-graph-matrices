-- import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.IncMatrix
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic


def hello := "world"

#check 2 + 2

def my_set : Finset ℕ := {1, 2, 3}
#check {1, 2}
#check s(1, 3)
#check ⟦1⟧

#eval Finset.powersetCard 2 {"hello", "wo", "rld"}

#eval !![1, 2, 3; 4, 5, 6].submatrix id (Fin.succ)

-- theorem foo (x : ℕ) : x + x = x := by
--   plausible

#synth Ring ℤ


-- Matrix calculation

def calculateDeterminant :=
  let M : Matrix (Fin 4) (Fin 4) ℚ := !![
    2, 0, -1, -1;
    0, 3, -1, -1;
    -1, -1, 3, 0;
    -1, -1, 0, 2
  ]
  Matrix.det M

#eval calculateDeterminant


-- edge set of house graph
def hge : (Fin 5) → (Fin 5) → Bool
  | 0, 1 => true
  | 1, 2 => true
  | 2, 3 => true
  | 3, 4 => true
  | 4, 0 => true
  | 1, 4 => true
  | _, _ => false

def hG : SimpleGraph (Fin 5) where
  Adj v w := hge v w || hge w v
  symm := by
    dsimp [Symmetric]; decide
  loopless := ⟨fun v h => by
    simp [hge] at h⟩

-- seems to be required to `#eval` number of edges
instance : DecidableRel hG.Adj :=
  fun a b => inferInstanceAs <| Decidable (hge a b || hge b a)

#eval hG.lapMatrix ℤ
