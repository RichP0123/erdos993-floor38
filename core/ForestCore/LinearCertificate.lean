import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Ring

/-!
Rational certificate principle from Tong Zhang and Wei Li,
`Unimodality of Forest Independence Polynomials` (27 September 2026), equation (40).

This is a general checker soundness theorem. It does not assert any forest
inequality, verify any finite certificate, or establish coverage through order 60.
Valid structural rows and the normalized equality remain explicit hypotheses.
The residual decomposition is proved from its coefficient formula, rather than
assumed. Explicit nonnegative residual bounds also cover empty index types.
-/

namespace Erdos993.ForestCore.LinearCertificate

open scoped BigOperators

/-- Evaluation of a coefficient array against the normalized layer variables. -/
def evaluation {J M : Type*} [Fintype J] [Fintype M]
    (x a : J → M → ℚ) : ℚ := ∑ j, ∑ m, a j m * x j m

theorem evaluation_sub {J M : Type*} [Fintype J] [Fintype M]
    (x a b : J → M → ℚ) :
    evaluation x (fun j m => a j m - b j m) = evaluation x a - evaluation x b := by
  simp only [evaluation, sub_mul, Finset.sum_sub_distrib]

theorem evaluation_smul {J M : Type*} [Fintype J] [Fintype M]
    (x a : J → M → ℚ) (c : ℚ) :
    evaluation x (fun j m => c * a j m) = c * evaluation x a := by
  simp only [evaluation, mul_assoc, Finset.mul_sum]

theorem evaluation_weighted_rows {R J M : Type*}
    [Fintype R] [Fintype J] [Fintype M]
    (x : J → M → ℚ) (weight : R → ℚ) (row : R → J → M → ℚ) :
    evaluation x (fun j m => ∑ r, weight r * row r j m) =
      ∑ r, weight r * evaluation x (row r) := by
  unfold evaluation
  simp only [Finset.sum_mul]
  calc
    (∑ j, ∑ m, ∑ r, weight r * row r j m * x j m) =
        ∑ j, ∑ r, ∑ m, weight r * row r j m * x j m := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = ∑ r, ∑ j, ∑ m, weight r * row r j m * x j m := Finset.sum_comm
    _ = ∑ r, weight r * ∑ j, ∑ m, row r j m * x j m := by
      simp only [mul_assoc, Finset.mul_sum]

/-- Residual coefficients after subtracting the weighted inequality rows and
an unrestricted multiple of an equality row. -/
def residual {R J M : Type*} [Fintype R]
    (q : J → M → ℚ) (weight : R → ℚ) (row : R → J → M → ℚ)
    (eta : ℚ) (equalityRow : J → M → ℚ) : J → M → ℚ :=
  fun j m => q j m - (∑ r, weight r * row r j m) - eta * equalityRow j m

theorem residual_evaluation {R J M : Type*}
    [Fintype R] [Fintype J] [Fintype M]
    (x q : J → M → ℚ) (weight : R → ℚ) (row : R → J → M → ℚ)
    (eta : ℚ) (equalityRow : J → M → ℚ) :
    evaluation x (residual q weight row eta equalityRow) =
      evaluation x q - (∑ r, weight r * evaluation x (row r)) -
        eta * evaluation x equalityRow := by
  unfold residual
  rw [evaluation_sub, evaluation_sub, evaluation_weighted_rows, evaluation_smul]

/-- The decomposition follows from coefficient algebra and the equality row.
It does not assume a bound on the objective. -/
theorem residual_decomposition {R J M : Type*}
    [Fintype R] [Fintype J] [Fintype M]
    (x q : J → M → ℚ) (weight : R → ℚ) (row : R → J → M → ℚ)
    (q0 eta : ℚ) (equalityRow : J → M → ℚ)
    (hequality : evaluation x equalityRow = 1) :
    q0 + evaluation x q = q0 + (∑ r, weight r * evaluation x (row r)) + eta +
      evaluation x (residual q weight row eta equalityRow) := by
  rw [residual_evaluation, hequality]
  ring

theorem layer_residual_bound {M : Type*} [Fintype M]
    (x r : M → ℚ) (u : ℚ)
    (hx : ∀ m, 0 ≤ x m) (hmass : ∑ m, x m ≤ 1)
    (hu : 0 ≤ u) (hr : ∀ m, r m ≤ u) :
    ∑ m, r m * x m ≤ u := by
  calc
    _ ≤ ∑ m, u * x m := Finset.sum_le_sum fun m _ =>
      mul_le_mul_of_nonneg_right (hr m) (hx m)
    _ = u * ∑ m, x m := (Finset.mul_sum _ _ _).symm
    _ ≤ u * 1 := mul_le_mul_of_nonneg_left hmass hu
    _ = u := mul_one u

/-- Soundness for explicit valid rows and certified residual upper bounds.
The multiplier of the equality row may have either sign. -/
theorem linear_certificate_sound {R J M : Type*}
    [Fintype R] [Fintype J] [Fintype M]
    (x q : J → M → ℚ) (u : J → ℚ)
    (weight rowBound : R → ℚ) (row : R → J → M → ℚ)
    (q0 eta : ℚ) (equalityRow : J → M → ℚ)
    (hx : ∀ j m, 0 ≤ x j m)
    (hmass : ∀ j, ∑ m, x j m ≤ 1)
    (hu : ∀ j, 0 ≤ u j)
    (hresidual : ∀ j m, residual q weight row eta equalityRow j m ≤ u j)
    (hweight : ∀ r, 0 ≤ weight r)
    (hrow : ∀ r, evaluation x (row r) ≤ rowBound r)
    (hequality : evaluation x equalityRow = 1) :
    q0 + evaluation x q ≤ q0 + (∑ r, weight r * rowBound r) + eta + ∑ j, u j := by
  rw [residual_decomposition x q weight row q0 eta equalityRow hequality]
  apply add_le_add
  · apply add_le_add _ (le_refl eta)
    apply add_le_add (le_refl q0)
    exact Finset.sum_le_sum fun r _ =>
      mul_le_mul_of_nonneg_left (hrow r) (hweight r)
  · exact Finset.sum_le_sum fun j _ =>
      layer_residual_bound (x j) (residual q weight row eta equalityRow j) (u j)
        (hx j) (hmass j) (hu j) (hresidual j)

theorem evaluation_layer_indicator {J M : Type*}
    [Fintype J] [Fintype M] [DecidableEq J]
    (x : J → M → ℚ) (first : J) :
    evaluation x (fun j _ => if j = first then 1 else 0) = ∑ m, x first m := by
  simp [evaluation, ite_mul]

/-- Equation (40) with the equality row furnished by a distinguished layer
of mass exactly one. Choosing each `u j` to bound zero and every residual
coefficient specializes this theorem to the paper's nonnegative maxima. -/
theorem first_layer_certificate_sound {R J M : Type*}
    [Fintype R] [Fintype J] [Fintype M] [DecidableEq J]
    (x q : J → M → ℚ) (u : J → ℚ)
    (weight rowBound : R → ℚ) (row : R → J → M → ℚ)
    (q0 eta : ℚ) (first : J)
    (hx : ∀ j m, 0 ≤ x j m)
    (hmass : ∀ j, ∑ m, x j m ≤ 1)
    (hfirst : ∑ m, x first m = 1)
    (hu : ∀ j, 0 ≤ u j)
    (hresidual : ∀ j m,
      q j m - (∑ r, weight r * row r j m) - eta * (if j = first then 1 else 0) ≤ u j)
    (hweight : ∀ r, 0 ≤ weight r)
    (hrow : ∀ r, evaluation x (row r) ≤ rowBound r) :
    q0 + evaluation x q ≤ q0 + (∑ r, weight r * rowBound r) + eta + ∑ j, u j := by
  apply linear_certificate_sound x q u weight rowBound row q0 eta
    (fun j _ => if j = first then 1 else 0) hx hmass hu hresidual hweight hrow
  rw [evaluation_layer_indicator, hfirst]

#print axioms residual_decomposition
#print axioms linear_certificate_sound
#print axioms first_layer_certificate_sound

end Erdos993.ForestCore.LinearCertificate
