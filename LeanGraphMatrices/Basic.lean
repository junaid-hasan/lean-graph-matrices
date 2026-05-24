-- import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.IncMatrix
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

open SimpleGraph


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


/-- set inclusions -/

def answer : (Fin 4) := Fin.succ (2 : Fin 3)
#check answer
#eval answer

-- #check {i : Fin 2 ↪o Fin 4}
#check Fin 2

def set2 : Finset (Fin 2) := Finset.univ
noncomputable def set_inj24 : Finset (Fin 2 ↪o Fin 4) := Finset.univ

#check set2
#check set_inj24

#eval set2.card
-- #eval set_inj24.card


/-- operations of Finsets and Fintypes -/

-- Define the subtype that excludes a specific element
def delElement {S : Type} [Fintype S] [DecidableEq S] (s : S) : Type :=
  {x : S // x ≠ s}

-- show that excludeElement s is a Fintype when S is a Fintype
instance {S : Type} [Fintype S] [DecidableEq S] (s : S) : Fintype (delElement s) := by
  apply Fintype.subtype {x : S | x ≠ s}
  intro x
  simp_all only [Finset.mem_filter, Finset.mem_univ, true_and]

-- show that excludeElement s has DeciableEq
instance {S : Type} [Fintype S] [dec : DecidableEq S] (s : S) : DecidableEq (delElement s) := by
  unfold delElement
  -- unfold DecidableEq
  intro a b
  obtain ⟨val, property⟩ := a
  obtain ⟨val_1, property_1⟩ := b
  simp_all only [Subtype.mk.injEq]
  apply dec

def Fin5no3 := {x : Fin 5 // x ≠ 3}

instance : Fintype Fin5no3 :=
  Fintype.subtype {n : Fin 5 | n ≠ 3} (by decide)

variable {S : Type} {s : S} [Fintype S] [DecidableEq S]

#check ({x : S | x ≠ s} : Finset S)
#check Fin 5
#check Fin5no3
#check delElement (3 : Fin 5)

#check {x : Fin 5 // x ≠ 3}
#check {x : Fin 5 | x ≠ 3}

#eval (Finset.univ : Finset (Fin 5))
#eval (Finset.univ : Finset Fin5no3)
#eval (Finset.univ : Finset (delElement (3 : Fin 5)))
#eval (Finset.univ : Finset {x : Fin 5 // x ≠ 3})
#eval (Finset.univ : Finset {x : Fin 5 | x ≠ 3})


variable {V : Type} [Fintype V] [DecidableEq V
]
-- alternative def of reduced laplacian matrix
def redLapMatrix' (G : SimpleGraph V) [DecidableRel G.Adj] (q : V) : Matrix ({v : V // v ≠ q}) ({v : V // v ≠ q}) ℤ :=
  let inc : (delElement q) → V := fun x => x.val
  (G.lapMatrix ℤ).submatrix inc inc

noncomputable def redSignIncMatrix' (G : SimpleGraph V) [DecidableRel G.Adj] (q : V) : Matrix ({v : V // v ≠ q}) (Sym2 V) ℤ :=
  let inc := fun x => x.val
  (G.incMatrix ℤ).submatrix inc id

def G := completeGraph (Fin 4)
#check G.Adj 1 1
#check completeGraph

instance : DecidableRel G.Adj := by
  intro a b
  dsimp [G, completeGraph]
  apply inferInstance

#eval G.Adj 1 5

#eval G.lapMatrix ℤ
#eval (redLapMatrix' G 3).det -- 16

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
  loopless := ⟨fun v h => by simp [hge] at h⟩

-- seems to be required to `#eval` number of edges
instance : DecidableRel hG.Adj :=
  fun a b => inferInstanceAs <| Decidable (hge a b || hge b a)

#eval! hG.lapMatrix ℤ
-- #eval redLapMatrix' hG 1
#eval! (redLapMatrix' hG 1).det -- 11
