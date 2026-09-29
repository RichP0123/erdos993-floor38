import ForestCore.Graph
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Circulant

/-!
The project's injective finite-cycle definition and Mathlib's cyclic-walk
definition describe the same forests. This semantic bridge imports no finite
catalogue or certificate data.
-/

namespace Erdos993.ForestCore

private theorem cycleNext_eq_add_one {k : Nat} (i : Fin (k + 3)) :
    Erdos993.cycleNext i = i + 1 := by
  apply Fin.ext
  simp [Erdos993.cycleNext, Fin.val_add]

/-- A Mathlib cycle supplies an injective cyclic list of vertices. -/
theorem isAcyclic_of_isForest {n : Nat} (G : Erdos993.Graph n)
    (hforest : Erdos993.IsForest G) : (toSimpleGraph G).IsAcyclic := by
  intro v p hp
  let k := p.length - 3
  have hlength : k + 3 = p.length := by
    have hthree := hp.three_le_length
    dsimp [k]
    omega
  apply hforest k (fun i => p.getVert i.val)
  · intro i j hij
    apply Fin.ext
    have hi : i.val ≤ p.length - 1 := by have := i.isLt; omega
    have hj : j.val ≤ p.length - 1 := by have := j.isLt; omega
    exact hp.getVert_injOn' hi hj hij
  · intro i
    change G.adj (p.getVert i.val)
      (p.getVert ((i.val + 1) % (k + 3))) = true
    have hadj := p.adj_getVert_succ (i := i.val) (by have := i.isLt; omega)
    change G.adj (p.getVert i.val) (p.getVert (i.val + 1)) = true at hadj
    by_cases hnext : i.val + 1 < k + 3
    · simpa only [Nat.mod_eq_of_lt hnext] using hadj
    · have hlast : i.val + 1 = p.length := by have := i.isLt; omega
      have hmod : (i.val + 1) % (k + 3) = 0 := by
        rw [hlast, ← hlength, Nat.mod_self]
      rw [hmod]
      simpa only [hlast, SimpleGraph.Walk.getVert_length,
        SimpleGraph.Walk.getVert_zero] using hadj

/-- An injected finite cycle maps Mathlib's canonical cycle into the graph. -/
theorem isForest_of_isAcyclic {n : Nat} (G : Erdos993.Graph n)
    (hacyclic : (toSimpleGraph G).IsAcyclic) : Erdos993.IsForest G := by
  intro k vertices hinjective hcycle
  let hom : SimpleGraph.cycleGraph (k + 3) →g toSimpleGraph G := {
    toFun := vertices
    map_rel' := by
      intro i j hij
      change i - j = 1 ∨ j - i = 1 at hij
      change G.adj (vertices i) (vertices j) = true
      rcases hij with hij | hji
      · have heq : i = j + 1 := (sub_eq_iff_eq_add').mp hij
        rw [heq, ← cycleNext_eq_add_one, G.symm]
        exact hcycle j
      · have heq : j = i + 1 := (sub_eq_iff_eq_add').mp hji
        rw [heq, ← cycleNext_eq_add_one]
        exact hcycle i
  }
  have hsource : (SimpleGraph.cycleGraph (k + 3)).IsAcyclic :=
    SimpleGraph.IsAcyclic.comap hom (fun i j h => hinjective i j h) hacyclic
  exact hsource (SimpleGraph.cycleGraph.cycle k) SimpleGraph.cycleGraph.isCycle_cycle

/-- Exact equivalence of the project's forest predicate and Mathlib acyclicity. -/
theorem isForest_iff_isAcyclic {n : Nat} (G : Erdos993.Graph n) :
    Erdos993.IsForest G ↔ (toSimpleGraph G).IsAcyclic :=
  ⟨isAcyclic_of_isForest G, isForest_of_isAcyclic G⟩

#print axioms isForest_iff_isAcyclic

end Erdos993.ForestCore
