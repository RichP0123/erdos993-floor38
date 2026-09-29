import Erdos993Analytic.JointLaw
import Erdos993Analytic.FinitePartition

/-! Actual occupation observations and total expectation/variance.
All components remain in jointSupport. USER compilation required. -/

namespace Erdos993.Analytic
open scoped BigOperators

theorem joint_weight_pos {n : ℕ} (G : Graph n) (s : List (Fin n)) :
    0 < (jointLaw G).weight s := by
  change 0 < 1 / ((jointSupport G).card : ℝ)
  exact one_div_pos.mpr (by exact_mod_cast jointSupport_card_pos G)

theorem occupation_sum {n : ℕ} (G : Graph n) (s : List (Fin n))
    (hs : s ∈ jointSupport G) :
    (∑ v : Fin n, occupation v s) = (s.length : ℝ) := by
  classical
  have he : (Finset.univ.filter (fun v : Fin n => v ∈ s)) = s.toFinset := by
    ext v
    simp
  simp only [occupation, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    mul_one, he, List.toFinset_card_of_nodup (supported_nodup G s hs)]

theorem sum_marginals {n : ℕ} (G : Graph n) :
    (∑ v : Fin n, marginal G v) = mean G := by
  unfold marginal FiniteLaw.expectation
  rw [Finset.sum_comm]
  calc
    _ = (jointLaw G).expectation (fun s => (s.length : ℝ)) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [← Finset.mul_sum, occupation_sum G s hs]
    _ = mean G := joint_mean G

/-- The observed occupied vertices of B, as a canonical finite set. -/
def exposure {n : ℕ} (B : Finset (Fin n)) (s : List (Fin n)) : Finset (Fin n) :=
  B.filter (fun v => v ∈ s)

theorem mem_exposure {n : ℕ} (B : Finset (Fin n)) (s : List (Fin n)) (v : Fin n) :
    v ∈ exposure B s ↔ v ∈ B ∧ v ∈ s := by
  simp [exposure]

theorem exposure_agrees {n : ℕ} (B : Finset (Fin n)) (s t : List (Fin n)) :
    exposure B s = exposure B t ↔ ∀ v ∈ B, (v ∈ s ↔ v ∈ t) := by
  constructor
  · intro h v hv
    have hm : v ∈ exposure B s ↔ v ∈ exposure B t := by rw [h]
    simpa [mem_exposure, hv] using hm
  · intro h
    ext v
    by_cases hv : v ∈ B
    · simp only [mem_exposure, hv, true_and]
      exact h v hv
    · simp [mem_exposure, hv]

theorem graph_total_expectation {n : ℕ} (G : Graph n) (B : Finset (Fin n))
    (f : List (Fin n) → ℝ) :
    ((jointLaw G).labelLaw (exposure B)).expectation
      ((jointLaw G).fiberMean (exposure B) f) = (jointLaw G).expectation f :=
  (jointLaw G).total_expectation (exposure B) (fun s _ => joint_weight_pos G s) f

theorem graph_total_variance {n : ℕ} (G : Graph n) (B : Finset (Fin n)) :
    cardinalityVariance G =
      ((jointLaw G).labelLaw (exposure B)).expectation
        ((jointLaw G).fiberVariance (exposure B) (fun s => (s.length : ℝ))) +
      ((jointLaw G).labelLaw (exposure B)).variance
        ((jointLaw G).fiberMean (exposure B) (fun s => (s.length : ℝ))) := by
  rw [← joint_variance G]
  exact (jointLaw G).total_variance (exposure B)
    (fun s _ => joint_weight_pos G s) (fun s => (s.length : ℝ))

theorem exposed_variance_le {n : ℕ} (G : Graph n) (B : Finset (Fin n)) :
    ((jointLaw G).labelLaw (exposure B)).variance
      ((jointLaw G).fiberMean (exposure B) (fun s => (s.length : ℝ))) ≤
      cardinalityVariance G := by
  rw [graph_total_variance G B]
  have hn : 0 ≤ ((jointLaw G).labelLaw (exposure B)).expectation
      ((jointLaw G).fiberVariance (exposure B) (fun s => (s.length : ℝ))) := by
    apply FiniteLaw.expectation_nonneg
    intro a ha
    have hp := (jointLaw G).fiberMass_pos (exposure B)
      (fun s _ => joint_weight_pos G s) a ha
    rw [FiniteLaw.fiberVariance_eq_condition _ _ _ _ hp]
    exact FiniteLaw.variance_nonneg _ _
  linarith

#print axioms occupation_sum
#print axioms sum_marginals
#print axioms graph_total_variance
#print axioms exposed_variance_le

end Erdos993.Analytic
