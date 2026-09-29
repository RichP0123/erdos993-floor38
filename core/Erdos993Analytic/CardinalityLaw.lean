import Erdos993Analytic.GraphMean

/-! The actual coefficient distribution, with mass and first moment normalized.
This does not yet construct the joint occupation law or its conditional laws.
DRAFT: not compiled in this session. -/

namespace Erdos993.Analytic

open scoped BigOperators

theorem massThrough_eq_sum (a : ℕ → ℕ) (b : ℕ) :
    CardinalityMoments.massThrough a b = ∑ r ∈ Finset.range (b+1), a r := by
  induction b with
  | zero => simp [CardinalityMoments.massThrough]
  | succ b ih =>
    simpa [CardinalityMoments.massThrough, Finset.sum_range_succ] using
      congrArg (fun x => x + a (b+1)) ih

theorem momentThrough_eq_sum (a : ℕ → ℕ) (b : ℕ) :
    CardinalityMoments.momentThrough a b = ∑ r ∈ Finset.range (b+1), r * a r := by
  induction b with
  | zero => simp [CardinalityMoments.momentThrough]
  | succ b ih =>
    simpa [CardinalityMoments.momentThrough, Finset.sum_range_succ] using
      congrArg (fun x => x + (b+1) * a (b+1)) ih

noncomputable def cardinalityProbability {n : ℕ} (G : Graph n) (r : ℕ) : ℝ :=
  (coefficient G r : ℝ) / mass G

theorem cardinalityProbability_nonneg {n : ℕ} (G : Graph n) (r : ℕ) :
    0 ≤ cardinalityProbability G r := by
  unfold cardinalityProbability
  exact div_nonneg (Nat.cast_nonneg _) (le_of_lt (mass_pos G))

theorem cardinalityProbability_above_order {n r : ℕ} (G : Graph n) (hr : n < r) :
    cardinalityProbability G r = 0 := by
  simp [cardinalityProbability, coefficient_above_order G hr]

theorem cardinalityProbability_sum {n : ℕ} (G : Graph n) :
    ∑ r ∈ Finset.range (n+1), cardinalityProbability G r = 1 := by
  have hmass : (∑ r ∈ Finset.range (n+1), (coefficient G r : ℝ)) = mass G := by
    unfold mass CardinalityMoments.partition
    exact_mod_cast (massThrough_eq_sum (coefficient G) n).symm
  simp only [cardinalityProbability, ← Finset.sum_div, hmass]
  exact div_self (ne_of_gt (mass_pos G))

theorem cardinalityProbability_mean {n : ℕ} (G : Graph n) :
    ∑ r ∈ Finset.range (n+1), (r : ℝ) * cardinalityProbability G r = mean G := by
  have hm : (∑ r ∈ Finset.range (n+1), (r : ℝ) * coefficient G r) = moment G := by
    unfold moment CardinalityMoments.firstMoment
    exact_mod_cast (momentThrough_eq_sum (coefficient G) n).symm
  simp only [cardinalityProbability, ← mul_div_assoc, ← Finset.sum_div, hm, mean]

/-- This is the variance of the actual cardinality coefficient law. -/
noncomputable def cardinalityVariance {n : ℕ} (G : Graph n) : ℝ :=
  ∑ r ∈ Finset.range (n+1), cardinalityProbability G r * ((r : ℝ) - mean G)^2

theorem cardinalityVariance_nonneg {n : ℕ} (G : Graph n) :
    0 ≤ cardinalityVariance G := by
  unfold cardinalityVariance
  exact Finset.sum_nonneg fun r _ =>
    mul_nonneg (cardinalityProbability_nonneg G r) (sq_nonneg _)

#print axioms cardinalityProbability_sum
#print axioms cardinalityProbability_mean

end Erdos993.Analytic
