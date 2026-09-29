import Erdos993Analytic.FiniteLaw

/-! Finite conditioning by an observed label. Every label in the image has
positive mass when all supported atoms have positive weight. No independence
assumption is used. USER compilation required. -/

namespace Erdos993.Analytic.FiniteLaw
open scoped BigOperators

noncomputable def fiberMass {Ω Λ : Type*} [DecidableEq Λ]
    (P : FiniteLaw Ω) (label : Ω → Λ) (a : Λ) : ℝ :=
  ∑ x ∈ P.support.filter (fun x => label x = a), P.weight x

theorem fiberMass_pos {Ω Λ : Type*} [DecidableEq Λ]
    (P : FiniteLaw Ω) (label : Ω → Λ)
    (hpos : ∀ x ∈ P.support, 0 < P.weight x)
    (a : Λ) (ha : a ∈ P.support.image label) : 0 < P.fiberMass label a := by
  classical
  obtain ⟨x, hx, hxa⟩ := Finset.mem_image.mp ha
  apply Finset.sum_pos'
  · intro y hy
    exact P.nonneg y (Finset.mem_filter.mp hy).1
  · exact ⟨x, Finset.mem_filter.mpr ⟨hx, hxa⟩, hpos x hx⟩

theorem sum_fibers {Ω Λ : Type*} [DecidableEq Λ]
    (P : FiniteLaw Ω) (label : Ω → Λ) (f : Ω → ℝ) :
    (∑ a ∈ P.support.image label,
      ∑ x ∈ P.support.filter (fun x => label x = a), P.weight x * f x) =
        P.expectation f := by
  classical
  exact Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩) _

theorem fiberMass_sum {Ω Λ : Type*} [DecidableEq Λ]
    (P : FiniteLaw Ω) (label : Ω → Λ) :
    (∑ a ∈ P.support.image label, P.fiberMass label a) = 1 := by
  have h := P.sum_fibers label (fun _ => 1)
  simpa only [mul_one, fiberMass, expectation_const] using h

noncomputable def labelLaw {Ω Λ : Type*} [DecidableEq Λ]
    (P : FiniteLaw Ω) (label : Ω → Λ) : FiniteLaw Λ where
  support := P.support.image label
  weight := P.fiberMass label
  nonneg a _ := Finset.sum_nonneg (fun x hx => P.nonneg x (Finset.mem_filter.mp hx).1)
  normalized := P.fiberMass_sum label

noncomputable def fiberMean {Ω Λ : Type*} [DecidableEq Λ]
    (P : FiniteLaw Ω) (label : Ω → Λ) (f : Ω → ℝ) (a : Λ) : ℝ :=
  (∑ x ∈ P.support.filter (fun x => label x = a), P.weight x * f x) /
    P.fiberMass label a

theorem fiberMean_eq_condition {Ω Λ : Type*} [DecidableEq Λ]
    (P : FiniteLaw Ω) (label : Ω → Λ) (f : Ω → ℝ) (a : Λ)
    (ha : 0 < P.fiberMass label a) :
    P.fiberMean label f a =
      (P.condition (fun x => label x = a) ha).expectation f := by
  exact (P.condition_expectation (fun x => label x = a) ha f).symm

theorem mass_mul_fiberMean {Ω Λ : Type*} [DecidableEq Λ]
    (P : FiniteLaw Ω) (label : Ω → Λ) (f : Ω → ℝ) (a : Λ)
    (ha : 0 < P.fiberMass label a) :
    P.fiberMass label a * P.fiberMean label f a =
      ∑ x ∈ P.support.filter (fun x => label x = a), P.weight x * f x := by
  unfold fiberMean
  field_simp [ne_of_gt ha]

theorem total_expectation {Ω Λ : Type*} [DecidableEq Λ]
    (P : FiniteLaw Ω) (label : Ω → Λ)
    (hpos : ∀ x ∈ P.support, 0 < P.weight x) (f : Ω → ℝ) :
    (P.labelLaw label).expectation (P.fiberMean label f) = P.expectation f := by
  classical
  unfold expectation labelLaw
  calc
    _ = ∑ a ∈ P.support.image label,
        ∑ x ∈ P.support.filter (fun x => label x = a), P.weight x * f x := by
      apply Finset.sum_congr rfl
      intro a ha
      exact P.mass_mul_fiberMean label f a (P.fiberMass_pos label hpos a ha)
    _ = P.expectation f := P.sum_fibers label f

noncomputable def fiberVariance {Ω Λ : Type*} [DecidableEq Λ]
    (P : FiniteLaw Ω) (label : Ω → Λ) (f : Ω → ℝ) (a : Λ) : ℝ :=
  P.fiberMean label (fun x => (f x - P.fiberMean label f a)^2) a

theorem fiberVariance_eq_condition {Ω Λ : Type*} [DecidableEq Λ]
    (P : FiniteLaw Ω) (label : Ω → Λ) (f : Ω → ℝ) (a : Λ)
    (ha : 0 < P.fiberMass label a) :
    P.fiberVariance label f a =
      (P.condition (fun x => label x = a) ha).variance f := by
  unfold fiberVariance variance
  rw [← P.fiberMean_eq_condition label f a ha]
  exact P.fiberMean_eq_condition label _ a ha

theorem fiberVariance_second_moment {Ω Λ : Type*} [DecidableEq Λ]
    (P : FiniteLaw Ω) (label : Ω → Λ) (f : Ω → ℝ) (a : Λ)
    (ha : 0 < P.fiberMass label a) :
    P.fiberVariance label f a =
      P.fiberMean label (fun x => (f x)^2) a - (P.fiberMean label f a)^2 := by
  rw [P.fiberVariance_eq_condition label f a ha, variance_eq_second_moment,
    ← P.fiberMean_eq_condition label (fun x => (f x)^2) a ha,
    ← P.fiberMean_eq_condition label f a ha]

theorem total_variance {Ω Λ : Type*} [DecidableEq Λ]
    (P : FiniteLaw Ω) (label : Ω → Λ)
    (hpos : ∀ x ∈ P.support, 0 < P.weight x) (f : Ω → ℝ) :
    P.variance f =
      (P.labelLaw label).expectation (P.fiberVariance label f) +
      (P.labelLaw label).variance (P.fiberMean label f) := by
  have hv : (P.labelLaw label).expectation (P.fiberVariance label f) =
      (P.labelLaw label).expectation (fun a =>
        P.fiberMean label (fun x => (f x)^2) a - (P.fiberMean label f a)^2) := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [P.fiberVariance_second_moment label f a (P.fiberMass_pos label hpos a ha)]
  rw [hv, expectation_sub, P.total_expectation label hpos,
    variance_eq_second_moment, variance_eq_second_moment,
    P.total_expectation label hpos]
  ring

#print axioms total_expectation
#print axioms fiberVariance_eq_condition
#print axioms total_variance

end Erdos993.Analytic.FiniteLaw
