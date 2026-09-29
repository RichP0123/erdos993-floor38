import Erdos993Analytic.CardinalityLaw

/-! Finite probability with explicit nonnegative normalized weights.
New draft: USER compilation required. No analytic graph bound is assumed here.
The coefficient-law instance below ties this interface to the existing graph. -/

namespace Erdos993.Analytic
open scoped BigOperators

structure FiniteLaw (Ω : Type*) where
  support : Finset Ω
  weight : Ω → ℝ
  nonneg : ∀ x ∈ support, 0 ≤ weight x
  normalized : ∑ x ∈ support, weight x = 1

namespace FiniteLaw

noncomputable def expectation {Ω : Type*} (P : FiniteLaw Ω) (f : Ω → ℝ) : ℝ :=
  ∑ x ∈ P.support, P.weight x * f x

noncomputable def variance {Ω : Type*} (P : FiniteLaw Ω) (f : Ω → ℝ) : ℝ :=
  P.expectation (fun x => (f x - P.expectation f)^2)

theorem expectation_const {Ω : Type*} (P : FiniteLaw Ω) (c : ℝ) :
    P.expectation (fun _ => c) = c := by
  simp only [expectation, ← Finset.sum_mul, P.normalized, one_mul]

theorem expectation_add {Ω : Type*} (P : FiniteLaw Ω) (f g : Ω → ℝ) :
    P.expectation (fun x => f x + g x) = P.expectation f + P.expectation g := by
  simp only [expectation, mul_add, Finset.sum_add_distrib]

theorem expectation_sub {Ω : Type*} (P : FiniteLaw Ω) (f g : Ω → ℝ) :
    P.expectation (fun x => f x - g x) = P.expectation f - P.expectation g := by
  simp only [expectation, mul_sub, Finset.sum_sub_distrib]

theorem expectation_scale {Ω : Type*} (P : FiniteLaw Ω) (c : ℝ) (f : Ω → ℝ) :
    P.expectation (fun x => c*f x) = c*P.expectation f := by
  simp only [expectation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

theorem expectation_mono {Ω : Type*} (P : FiniteLaw Ω) (f g : Ω → ℝ)
    (h : ∀ x ∈ P.support, f x ≤ g x) : P.expectation f ≤ P.expectation g := by
  exact Finset.sum_le_sum fun x hx =>
    mul_le_mul_of_nonneg_left (h x hx) (P.nonneg x hx)

theorem expectation_nonneg {Ω : Type*} (P : FiniteLaw Ω) (f : Ω → ℝ)
    (h : ∀ x ∈ P.support, 0 ≤ f x) : 0 ≤ P.expectation f := by
  exact Finset.sum_nonneg fun x hx => mul_nonneg (P.nonneg x hx) (h x hx)

theorem expectation_centered {Ω : Type*} (P : FiniteLaw Ω) (f : Ω → ℝ) :
    P.expectation (fun x => f x-P.expectation f) = 0 := by
  rw [expectation_sub, expectation_const, sub_self]

theorem variance_nonneg {Ω : Type*} (P : FiniteLaw Ω) (f : Ω → ℝ) :
    0 ≤ P.variance f := P.expectation_nonneg _ (fun _ _ => sq_nonneg _)

theorem variance_eq_second_moment {Ω : Type*} (P : FiniteLaw Ω) (f : Ω → ℝ) :
    P.variance f = P.expectation (fun x => (f x)^2) - (P.expectation f)^2 := by
  have he : (fun x => (f x-P.expectation f)^2) =
      (fun x => (f x)^2 - (2*P.expectation f)*f x + (P.expectation f)^2) := by
    funext x
    ring
  unfold variance
  rw [he, expectation_add, expectation_sub, expectation_scale, expectation_const]
  ring

/-- A genuine finite conditional law; zero-probability events are excluded explicitly. -/
noncomputable def condition {Ω : Type*} (P : FiniteLaw Ω) (event : Ω → Prop)
    [DecidablePred event]
    (hpos : 0 < ∑ x ∈ P.support.filter event, P.weight x) : FiniteLaw Ω where
  support := P.support.filter event
  weight x := P.weight x / ∑ y ∈ P.support.filter event, P.weight y
  nonneg x hx := div_nonneg (P.nonneg x (Finset.mem_filter.mp hx).1) (le_of_lt hpos)
  normalized := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt hpos)

theorem condition_expectation {Ω : Type*} (P : FiniteLaw Ω) (event : Ω → Prop)
    [DecidablePred event]
    (hpos : 0 < ∑ x ∈ P.support.filter event, P.weight x) (f : Ω → ℝ) :
    (P.condition event hpos).expectation f =
      (∑ x ∈ P.support.filter event, P.weight x*f x) /
        (∑ x ∈ P.support.filter event, P.weight x) := by
  simp only [expectation, condition, div_mul_eq_mul_div, Finset.sum_div]

end FiniteLaw

noncomputable def coefficientLaw {n : ℕ} (G : Graph n) : FiniteLaw ℕ where
  support := Finset.range (n+1)
  weight := cardinalityProbability G
  nonneg r _ := cardinalityProbability_nonneg G r
  normalized := cardinalityProbability_sum G

theorem coefficientLaw_mean {n : ℕ} (G : Graph n) :
    (coefficientLaw G).expectation (fun r => (r : ℝ)) = mean G := by
  simpa only [FiniteLaw.expectation, coefficientLaw, mul_comm] using
    cardinalityProbability_mean G

theorem coefficientLaw_variance {n : ℕ} (G : Graph n) :
    (coefficientLaw G).variance (fun r => (r : ℝ)) = cardinalityVariance G := by
  unfold FiniteLaw.variance
  rw [coefficientLaw_mean]
  rfl

#print axioms coefficientLaw_mean
#print axioms coefficientLaw_variance
#print axioms FiniteLaw.variance_eq_second_moment
#print axioms FiniteLaw.condition_expectation

end Erdos993.Analytic
