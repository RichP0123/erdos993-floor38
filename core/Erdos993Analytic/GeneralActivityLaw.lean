import Erdos993Analytic.ResidualGraphLaw
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Vertex-dependent activities on actual independent vertex subsets.
Active subsets keep original labels, and rank counts are proved equal to
the legacy induced graph coefficients. No abstract tree grammar is used. -/

namespace Erdos993.Analytic.GeneralActivity
open scoped BigOperators
open ResidualSupport Counting Structure

noncomputable def configs {n : ℕ} (G : Graph n) (U : Finset (Fin n)) :
    Finset (Finset (Fin n)) := by
  classical
  exact U.powerset.filter (independentSet G)

theorem mem_configs {n : ℕ} (G : Graph n) (U S : Finset (Fin n)) :
    S ∈ configs G U ↔ S ⊆ U ∧ independentSet G S := by
  classical
  simp [configs]

theorem empty_mem_configs {n : ℕ} (G : Graph n) (U : Finset (Fin n)) :
    ∅ ∈ configs G U := by
  rw [mem_configs]
  simp [independentSet]

noncomputable def weight {n : ℕ} (a : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  ∏ v ∈ S, a v

noncomputable def partition {n : ℕ} (G : Graph n) (U : Finset (Fin n))
    (a : Fin n → ℝ) : ℝ := ∑ S ∈ configs G U, weight a S

theorem weight_nonneg {n : ℕ} (a : Fin n → ℝ) (S : Finset (Fin n))
    (ha : ∀ v ∈ S, 0 ≤ a v) : 0 ≤ weight a S := Finset.prod_nonneg ha

theorem partition_pos {n : ℕ} (G : Graph n) (U : Finset (Fin n))
    (a : Fin n → ℝ) (ha : ∀ v ∈ U, 0 ≤ a v) : 0 < partition G U a := by
  unfold partition
  apply Finset.sum_pos'
  · intro S hS
    apply weight_nonneg
    intro v hv
    exact ha v (((mem_configs G U S).mp hS).1 hv)
  · refine ⟨∅, empty_mem_configs G U, ?_⟩
    simp [weight]

noncomputable def law {n : ℕ} (G : Graph n) (U : Finset (Fin n))
    (a : Fin n → ℝ) (ha : ∀ v ∈ U, 0 ≤ a v) : FiniteLaw (Finset (Fin n)) where
  support := configs G U
  weight S := weight a S / partition G U a
  nonneg S hS := div_nonneg
    (weight_nonneg a S (fun v hv => ha v (((mem_configs G U S).mp hS).1 hv)))
    (partition_pos G U a ha).le
  normalized := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (partition_pos G U a ha))

theorem eligible_compl_empty {n : ℕ} (G : Graph n) (U : Finset (Fin n)) :
    eligible G Uᶜ ∅ = U := by
  ext v
  simp [mem_eligible]

theorem configs_eq_residual {n : ℕ} (G : Graph n) (U : Finset (Fin n)) :
    configs G U = residualConfigs G Uᶜ ∅ := by
  unfold configs residualConfigs
  rw [eligible_compl_empty]

/-- Exact correspondence with the existing actual induced-graph coefficients. -/
theorem configs_rank_card {n : ℕ} (G : Graph n) (U : Finset (Fin n)) (r : ℕ) :
    ((configs G U).filter (fun S => S.card = r)).card =
      coefficient (inducedOn G (canonical U)) r := by
  rw [configs_eq_residual]
  have h := residual_rank_card G Uᶜ ∅ r
  exact h.trans (congrArg
    (fun E : Finset (Fin n) => coefficient (inducedOn G (canonical E)) r)
    (eligible_compl_empty G U))

theorem weight_insert {n : ℕ} (a : Fin n → ℝ) (S : Finset (Fin n))
    (v : Fin n) (hv : v ∉ S) : weight a (insert v S) = a v * weight a S := by
  exact Finset.prod_insert hv

theorem independent_insert {n : ℕ} (G : Graph n) (S : Finset (Fin n)) (v : Fin n) :
    independentSet G (insert v S) ↔
      independentSet G S ∧ ∀ u ∈ S, G.adj v u = false := by
  constructor
  · intro h
    exact ⟨fun u hu w hw => h u (Finset.mem_insert_of_mem hu) w (Finset.mem_insert_of_mem hw),
      fun u hu => h v (Finset.mem_insert_self v S) u (Finset.mem_insert_of_mem hu)⟩
  · rintro ⟨hS, hv⟩ u hu w hw
    rcases Finset.mem_insert.mp hu with he | hu
    · subst u
      rcases Finset.mem_insert.mp hw with he | hw
      · subst w
        exact G.loopless v
      · exact hv w hw
    · rcases Finset.mem_insert.mp hw with he | hw
      · subst w
        rw [G.symm]
        exact hv u hu
      · exact hS u hu w hw

#print axioms configs_rank_card
#print axioms partition_pos
#print axioms independent_insert

end Erdos993.Analytic.GeneralActivity
