import Erdos993Analytic.FinitePartition

/-! Conditional expectations as functions on the original sample space.
Orthogonality is proved from finite fibers. USER compilation required. -/

namespace Erdos993.Analytic.FiniteLaw
open scoped BigOperators

theorem expectation_congr_support {Ω : Type*} (P : FiniteLaw Ω) (f g : Ω → ℝ)
    (h : ∀ x ∈ P.support, f x = g x) : P.expectation f = P.expectation g := by
  apply Finset.sum_congr rfl
  intro x hx
  rw [h x hx]

theorem label_expectation {Ω Λ : Type*} [DecidableEq Λ]
    (P : FiniteLaw Ω) (label : Ω → Λ) (g : Λ → ℝ) :
    P.expectation (fun x => g (label x)) = (P.labelLaw label).expectation g := by
  classical
  rw [← P.sum_fibers label]
  apply Finset.sum_congr rfl
  intro a ha
  calc
    _ = ∑ x ∈ P.support.filter (fun x => label x = a), P.weight x * g a := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ = _ := by rw [← Finset.sum_mul] <;> rfl

theorem weighted_total_expectation {Ω Λ : Type*} [DecidableEq Λ]
    (P : FiniteLaw Ω) (label : Ω → Λ)
    (hpos : ∀ x ∈ P.support, 0 < P.weight x) (f : Ω → ℝ) (g : Λ → ℝ) :
    P.expectation (fun x => f x * g (label x)) =
      (P.labelLaw label).expectation (fun a => P.fiberMean label f a * g a) := by
  classical
  rw [← P.sum_fibers label]
  apply Finset.sum_congr rfl
  intro a ha
  have hp := P.fiberMass_pos label hpos a ha
  calc
    _ = ∑ x ∈ P.support.filter (fun x => label x = a), (P.weight x*f x)*g a := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
      ring
    _ = (P.fiberMass label a * P.fiberMean label f a)*g a := by
      rw [← Finset.sum_mul, P.mass_mul_fiberMean label f a hp]
    _ = _ := by change _ = P.fiberMass label a * (P.fiberMean label f a*g a); ring

noncomputable def projection {Ω Λ : Type*} [DecidableEq Λ]
    (P : FiniteLaw Ω) (label : Ω → Λ) (f : Ω → ℝ) (x : Ω) : ℝ :=
  P.fiberMean label f (label x)

theorem projection_expectation {Ω Λ : Type*} [DecidableEq Λ]
    (P : FiniteLaw Ω) (label : Ω → Λ)
    (hpos : ∀ x ∈ P.support, 0 < P.weight x) (f : Ω → ℝ) :
    P.expectation (P.projection label f) = P.expectation f := by
  unfold projection
  rw [P.label_expectation, P.total_expectation label hpos]

theorem projection_pairing {Ω Λ : Type*} [DecidableEq Λ]
    (P : FiniteLaw Ω) (label : Ω → Λ)
    (hpos : ∀ x ∈ P.support, 0 < P.weight x) (f : Ω → ℝ) (g : Λ → ℝ) :
    P.expectation (fun x => f x*g (label x)) =
      P.expectation (fun x => P.projection label f x*g (label x)) := by
  rw [P.weighted_total_expectation label hpos]
  exact (P.label_expectation label (fun a => P.fiberMean label f a*g a)).symm

theorem residual_orthogonal {Ω Λ : Type*} [DecidableEq Λ]
    (P : FiniteLaw Ω) (label : Ω → Λ)
    (hpos : ∀ x ∈ P.support, 0 < P.weight x) (f : Ω → ℝ) (g : Λ → ℝ) :
    P.expectation (fun x => (f x-P.projection label f x)*g (label x)) = 0 := by
  have he : (fun x => (f x-P.projection label f x)*g (label x)) =
      (fun x => f x*g (label x)-P.projection label f x*g (label x)) := by
    funext x
    ring
  rw [he, expectation_sub, P.projection_pairing label hpos f g, sub_self]

theorem refinement_pairing {Ω Λ Γ : Type*} [DecidableEq Λ] [DecidableEq Γ]
    (P : FiniteLaw Ω) (coarse : Ω → Λ) (fine : Ω → Γ) (forget : Γ → Λ)
    (href : ∀ x ∈ P.support, coarse x = forget (fine x))
    (hpos : ∀ x ∈ P.support, 0 < P.weight x) (f : Ω → ℝ) :
    P.expectation (fun x => P.projection fine f x * P.projection coarse f x) =
      P.expectation (fun x => (P.projection coarse f x)^2) := by
  have hf := P.projection_pairing fine hpos f
    (fun a => P.fiberMean coarse f (forget a))
  have hc := P.projection_pairing coarse hpos f (P.fiberMean coarse f)
  have hleft : P.expectation (fun x => f x * P.fiberMean coarse f (forget (fine x))) =
      P.expectation (fun x => f x * P.projection coarse f x) := by
    apply P.expectation_congr_support
    intro x hx
    simp only [projection, href x hx]
  have hright : P.expectation (fun x => P.projection fine f x *
      P.fiberMean coarse f (forget (fine x))) =
      P.expectation (fun x => P.projection fine f x * P.projection coarse f x) := by
    apply P.expectation_congr_support
    intro x hx
    simp only [projection, href x hx]
  rw [hleft, hright] at hf
  calc
    _ = P.expectation (fun x => f x * P.projection coarse f x) := hf.symm
    _ = P.expectation (fun x => P.projection coarse f x * P.projection coarse f x) := hc
    _ = _ := by simp only [pow_two]

theorem refinement_increment_energy {Ω Λ Γ : Type*} [DecidableEq Λ] [DecidableEq Γ]
    (P : FiniteLaw Ω) (coarse : Ω → Λ) (fine : Ω → Γ) (forget : Γ → Λ)
    (href : ∀ x ∈ P.support, coarse x = forget (fine x))
    (hpos : ∀ x ∈ P.support, 0 < P.weight x) (f : Ω → ℝ) :
    P.expectation (fun x => (P.projection fine f x-P.projection coarse f x)^2) =
      P.expectation (fun x => (P.projection fine f x)^2) -
        P.expectation (fun x => (P.projection coarse f x)^2) := by
  have he : (fun x => (P.projection fine f x-P.projection coarse f x)^2) =
      (fun x => (P.projection fine f x)^2 -
        2*(P.projection fine f x*P.projection coarse f x) +
          (P.projection coarse f x)^2) := by
    funext x
    ring
  rw [he, expectation_add, expectation_sub, expectation_scale,
    P.refinement_pairing coarse fine forget href hpos f]
  ring

theorem projection_eq_of_fiber_constant {Ω Λ : Type*} [DecidableEq Λ]
    (P : FiniteLaw Ω) (label : Ω → Λ)
    (hpos : ∀ x ∈ P.support, 0 < P.weight x) (f : Ω → ℝ)
    (x : Ω) (hx : x ∈ P.support)
    (hf : ∀ y ∈ P.support, label y = label x → f y = f x) :
    P.projection label f x = f x := by
  classical
  have hp := P.fiberMass_pos label hpos (label x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  have he : (∑ y ∈ P.support.filter (fun y => label y = label x), P.weight y*f y) =
      P.fiberMass label (label x)*f x := by
    unfold fiberMass
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y hy
    rw [hf y (Finset.mem_filter.mp hy).1 (Finset.mem_filter.mp hy).2]
  unfold projection fiberMean
  rw [he]
  field_simp [ne_of_gt hp]

theorem projection_eq_mean_of_constant_label {Ω Λ : Type*} [DecidableEq Λ]
    (P : FiniteLaw Ω) (label : Ω → Λ) (f : Ω → ℝ)
    (x : Ω) (hlabel : ∀ y ∈ P.support, label y = label x) :
    P.projection label f x = P.expectation f := by
  classical
  have he : P.support.filter (fun y => label y = label x) = P.support := by
    apply Finset.filter_true_of_mem
    exact hlabel
  unfold projection fiberMean fiberMass
  simp only [he, P.normalized, div_one, expectation]

#print axioms projection_pairing
#print axioms residual_orthogonal
#print axioms refinement_increment_energy

end Erdos993.Analytic.FiniteLaw
