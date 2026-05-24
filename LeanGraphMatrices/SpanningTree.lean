import Mathlib.Combinatorics.SimpleGraph.Acyclic

open SimpleGraph

set_option diagnostics true

universe u

variable {V : Type} [Fintype V] [DecidableEq V]

structure SpanningTree (G : SimpleGraph V) where
  Tree : SimpleGraph V
  subG : Tree ≤ G
  isTree : Tree.IsTree

/-! ## Decidable `IsTree` -/

-- Mathlib provides a `Decidable` instance for `IsTree` via `isTree_iff_connected_and_card`,
-- so we do not need to define our own.

/-! ## Fintype instance -/

instance finiteSpanningTree (G : SimpleGraph V) : Finite (SpanningTree G) := by
  refine Finite.of_injective (fun (t : SpanningTree G) => t.Tree) ?_
  intro t1 t2 h
  cases t1; cases t2; congr

noncomputable instance fintypeSpanningTree (G : SimpleGraph V) :
    Fintype (SpanningTree G) :=
  Fintype.ofFinite _

/-! ## Leaf existence lemma -/

-- Mathlib provides `IsTree.exists_vert_degree_one_of_nontrivial` which
-- gives a vertex of degree 1 in any nontrivial tree.
-- No need for our own version.
