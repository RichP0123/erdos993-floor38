import ForestCore.Transfer

namespace Erdos993.ForestCore

universe u

/-- Independently written target for the compiled Mathlib corollary.
This definition asserts nothing: its value is only the proposition to check. -/
def mathlibFloor38Target : Prop := by
  classical
  exact ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
    Fintype.card V ≤ 37 → G.IsAcyclic →
      Erdos993.Unimodal (fun k => (G.indepSetFinset k).card)

/-- Ordinary checked specialization of the general transport theorem.
The original finite graph theorem is still an explicit premise here. The final
kernel application must supply the already audited unconditional theorem. -/
theorem mathlibFloor38FromOriginal
    (h : ∀ n ≤ 37, ∀ G : Erdos993.Graph n,
      Erdos993.IsForest G → Erdos993.Unimodal (Erdos993.coefficient G)) :
    mathlibFloor38Target.{u} := by
  classical
  intro V inst G hcard hforest
  have result := transfer_forest_bound 37 h G hcard hforest
  have counts : independentCoefficient G = (fun k => (G.indepSetFinset k).card) := by
    funext k
    exact independentCoefficient_eq_card_indepSetFinset G k
  rwa [counts] at result

#print axioms mathlibFloor38FromOriginal

end Erdos993.ForestCore
