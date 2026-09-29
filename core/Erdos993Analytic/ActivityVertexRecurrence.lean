import Erdos993Analytic.GeneralActivityLaw
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! Vertex-deletion partition identity for actual configurations with arbitrary
vertex activities. This is the recurrence required for leaf/root elimination.
-/

namespace Erdos993.Analytic.GeneralActivity
open scoped BigOperators
open ResidualSupport
open Classical

theorem partition_as_powerset {n : ℕ} (G : Graph n) (U : Finset (Fin n))
    (a : Fin n → ℝ) :
    partition G U a = ∑ S ∈ U.powerset, if independentSet G S then weight a S else 0 := by
  classical
  exact Finset.sum_filter _ _

theorem filtered_configs {n : ℕ} (G : Graph n) (U : Finset (Fin n)) (v : Fin n) :
    configs G (U.filter (fun u => G.adj v u = false)) =
      U.powerset.filter (fun S => independentSet G S ∧ ∀ u ∈ S, G.adj v u = false) := by
  classical
  ext S
  simp only [mem_configs, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨hsub, hind⟩
    refine ⟨fun u hu => (Finset.mem_filter.mp (hsub hu)).1, hind, ?_⟩
    intro u hu
    exact (Finset.mem_filter.mp (hsub hu)).2
  · rintro ⟨hsub, hind, hne⟩
    exact ⟨fun u hu => Finset.mem_filter.mpr ⟨hsub hu, hne u hu⟩, hind⟩

theorem partition_insert {n : ℕ} (G : Graph n) (U : Finset (Fin n))
    (a : Fin n → ℝ) (v : Fin n) (hv : v ∉ U) :
    partition G (insert v U) a = partition G U a +
      a v * partition G (U.filter (fun u => G.adj v u = false)) a := by
  classical
  rw [partition_as_powerset, Finset.sum_powerset_insert hv, ← partition_as_powerset]
  congr 1
  unfold partition
  rw [filtered_configs, Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  have hvS : v ∉ S := fun h => hv ((Finset.mem_powerset.mp hS) h)
  rw [independent_insert, weight_insert a S v hvS]
  split <;> simp_all

#print axioms partition_insert

end Erdos993.Analytic.GeneralActivity
