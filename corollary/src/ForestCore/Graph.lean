import ForestStatements
import Mathlib.Combinatorics.SimpleGraph.Basic

namespace Erdos993.ForestCore

/-- Exact conversion of the finite Boolean adjacency representation. -/
def toSimpleGraph {n : Nat} (G : Erdos993.Graph n) : SimpleGraph (Fin n) where
  Adj u v := G.adj u v = true
  symm := by
    intro u v h
    simpa only [G.symm v u] using h
  loopless := ⟨by
    intro u h
    simp only [G.loopless u, Bool.false_eq_true] at h⟩

@[simp] theorem toSimpleGraph_adj {n : Nat} (G : Erdos993.Graph n) (u v : Fin n) :
    (toSimpleGraph G).Adj u v ↔ G.adj u v = true := Iff.rfl

instance {n : Nat} (G : Erdos993.Graph n) : DecidableRel (toSimpleGraph G).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ = true))

end Erdos993.ForestCore
