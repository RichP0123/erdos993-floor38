import ForestCore.AcyclicBridge
import ForestCore.CountingBridge
import Mathlib.Data.Fintype.EquivFin

namespace Erdos993.ForestCore

noncomputable section

/-- Encode a graph on `Fin n` in the original finite Boolean representation. -/
def ofSimpleGraph {n : Nat} (G : SimpleGraph (Fin n)) : Erdos993.Graph n := by
  classical
  exact {
    adj := fun u v => decide (G.Adj u v)
    symm := by
      intro u v
      exact congrArg (fun p : Prop => decide p) (propext (G.adj_comm u v))
    loopless := by intro u; simp
  }

@[simp] theorem toSimpleGraph_ofSimpleGraph {n : Nat} (G : SimpleGraph (Fin n)) :
    toSimpleGraph (ofSimpleGraph G) = G := by
  classical
  ext u v
  simp [toSimpleGraph, ofSimpleGraph]

/-- The ordinary independent-set coefficient in Mathlib's graph representation. -/
def independentCoefficient {V : Type*} [Fintype V] (G : SimpleGraph V) (k : Nat) : Nat := by
  classical
  exact (G.indepSetFinset k).card

/-- Counting is independent of the chosen decidability instances. Comparing
membership avoids reducing the finite-set enumeration to prove this equality. -/
theorem independentCoefficient_eq_card_indepSetFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : Nat) :
    independentCoefficient G k = (G.indepSetFinset k).card := by
  unfold independentCoefficient
  apply congrArg Finset.card
  ext S
  simp only [SimpleGraph.mem_indepSetFinset_iff]

/-- The original count equals the representation-independent Mathlib count. -/
theorem coefficient_eq_independentCoefficient {n : Nat} (G : Erdos993.Graph n) (k : Nat) :
    Erdos993.coefficient G k = independentCoefficient (toSimpleGraph G) k := by
  exact (coefficient_eq_card_indepSetFinset G k).trans
    (independentCoefficient_eq_card_indepSetFinset (toSimpleGraph G) k).symm

@[simp] theorem coefficient_ofSimpleGraph {n : Nat} (G : SimpleGraph (Fin n)) (k : Nat) :
    Erdos993.coefficient (ofSimpleGraph G) k = independentCoefficient G k := by
  classical
  calc
    _ = independentCoefficient (toSimpleGraph (ofSimpleGraph G)) k :=
      coefficient_eq_independentCoefficient (ofSimpleGraph G) k
    _ = independentCoefficient G k :=
      congrArg (fun H => independentCoefficient H k) (toSimpleGraph_ofSimpleGraph G)

theorem independentCoefficient_iso {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (k : Nat) :
    independentCoefficient G k = independentCoefficient H k := by
  classical
  unfold independentCoefficient
  refine Finset.card_bij (fun S _ => S.map e.toEquiv.toEmbedding) ?_ ?_ ?_
  · intro S hS
    obtain ⟨hI, hcard⟩ := SimpleGraph.mem_indepSetFinset_iff.mp hS
    apply SimpleGraph.mem_indepSetFinset_iff.mpr
    refine ⟨?_, by simpa using hcard⟩
    rw [SimpleGraph.isIndepSet_iff] at hI ⊢
    intro u hu v hv huv
    obtain ⟨a, ha, heqa⟩ := Finset.mem_map.mp hu
    obtain ⟨b, hb, heqb⟩ := Finset.mem_map.mp hv
    change e a = u at heqa
    change e b = v at heqb
    have hne : a ≠ b := by
      intro hab
      apply huv
      exact heqa.symm.trans ((congrArg e hab).trans heqb)
    intro hadj
    have hh : H.Adj (e a) (e b) := by rw [heqa, heqb]; exact hadj
    exact hI ha hb hne (e.map_rel_iff.mp hh)
  · intro S _ T _ he
    exact Finset.map_injective e.toEquiv.toEmbedding he
  · intro T hT
    refine ⟨T.map e.symm.toEquiv.toEmbedding, ?_, ?_⟩
    · obtain ⟨hI, hcard⟩ := SimpleGraph.mem_indepSetFinset_iff.mp hT
      apply SimpleGraph.mem_indepSetFinset_iff.mpr
      refine ⟨?_, by simpa using hcard⟩
      rw [SimpleGraph.isIndepSet_iff] at hI ⊢
      intro u hu v hv huv
      obtain ⟨a, ha, heqa⟩ := Finset.mem_map.mp hu
      obtain ⟨b, hb, heqb⟩ := Finset.mem_map.mp hv
      change e.symm a = u at heqa
      change e.symm b = v at heqb
      have hne : a ≠ b := by
        intro hab
        apply huv
        exact heqa.symm.trans ((congrArg e.symm hab).trans heqb)
      intro hadj
      have hh : G.Adj (e.symm a) (e.symm b) := by rw [heqa, heqb]; exact hadj
      exact hI ha hb hne (e.symm.map_rel_iff.mp hh)
    · ext v
      simp only [Finset.mem_map]
      constructor
      · rintro ⟨a, ⟨b, hb, rfl⟩, he⟩
        have he' : b = v := by simpa using he
        simpa [he'] using hb
      · intro hv
        exact ⟨e.symm v, ⟨v, hv, rfl⟩, e.apply_symm_apply v⟩

/-- A general transport theorem, with its input theorem explicit.
This bridge is not itself a proof of any finite bound. -/
theorem transfer_forest_bound (N : Nat)
    (h : ∀ n ≤ N, ∀ G : Erdos993.Graph n,
      Erdos993.IsForest G → Erdos993.Unimodal (Erdos993.coefficient G))
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hcard : Fintype.card V ≤ N) (hforest : G.IsAcyclic) :
    Erdos993.Unimodal (independentCoefficient G) := by
  classical
  let e : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  let H : SimpleGraph (Fin (Fintype.card V)) := G.comap e
  have hH : H.IsAcyclic :=
    SimpleGraph.IsAcyclic.comap (SimpleGraph.Hom.comap e G) e.injective hforest
  have hcustom : Erdos993.IsForest (ofSimpleGraph H) :=
    (isForest_iff_isAcyclic _).mpr (by simpa using hH)
  have result := h _ hcard (ofSimpleGraph H) hcustom
  have heq : Erdos993.coefficient (ofSimpleGraph H) = independentCoefficient G := by
    funext k
    rw [coefficient_ofSimpleGraph]
    exact independentCoefficient_iso (SimpleGraph.Iso.comap e G) k
  rwa [heq] at result

#print axioms coefficient_ofSimpleGraph
#print axioms independentCoefficient_eq_card_indepSetFinset
#print axioms coefficient_eq_independentCoefficient
#print axioms independentCoefficient_iso
#print axioms transfer_forest_bound

end
end Erdos993.ForestCore
