import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! The algebraic formulas (1)--(4) of FLOOR216/PROOF.md.
The inputs here are boundary polynomials. Their actual-graph interpretation
is a separate obligation; no census or graph theorem is assumed or asserted. -/
namespace Erdos993.Floor216
open Polynomial
open scoped BigOperators
noncomputable section

abbrev QPoly := Polynomial ℚ
def rootPair (B C' : QPoly) : QPoly × QPoly := (B + X * C', B)
def center {ι : Type*} (s : Finset ι) (P A : ι → QPoly) : QPoly :=
  (∏ i ∈ s, P i) + X * (∏ i ∈ s, A i)
def difference (d : ℕ) (P : QPoly) : QPoly := (1-X)^d * P

theorem rooted_recurrence {ι : Type*} (s : Finset ι) (P A : ι → QPoly) :
    rootPair (∏ i ∈ s, P i) (∏ i ∈ s, A i) =
      (center s P A, ∏ i ∈ s, P i) := rfl

/-- Equality of boundary pairs is a congruence for attachment, with repetitions
allowed at distinct indices. This is the algebraic step in quotient generation. -/
theorem boundary_congruence {ι : Type*} (s : Finset ι) (P A P' A' : ι → QPoly)
    (hP : ∀ i ∈ s, P i = P' i) (hA : ∀ i ∈ s, A i = A' i) :
    rootPair (∏ i ∈ s, P i) (∏ i ∈ s, A i) =
      rootPair (∏ i ∈ s, P' i) (∏ i ∈ s, A' i) := by
  rw [Finset.prod_congr rfl hP, Finset.prod_congr rfl hA]

theorem root_bundle_identity (B C' : QPoly) :
    (rootPair B C').1 - (rootPair B C').2 = X * C' := by
  simp [rootPair]

theorem root_bundle_injective (B C' D E : QPoly)
    (h : rootPair B C' = rootPair D E) : B = D ∧ C' = E := by
  have hb : B = D := congrArg Prod.snd h
  have hc : B + X*C' = D + X*E := congrArg Prod.fst h
  subst D
  exact ⟨rfl, mul_left_cancel₀ Polynomial.X_ne_zero (add_left_cancel hc)⟩

theorem allocated_product {ι : Type*} (s : Finset ι) (P : ι → QPoly) (d : ι → ℕ) :
    (∏ i ∈ s, difference (d i) (P i)) =
      (1-X)^(∑ i ∈ s, d i) * (∏ i ∈ s, P i) := by
  simp only [difference, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

/-- Formula (4), for any number of factors and any nonnegative allocation. -/
theorem cancellation_allocation {ι : Type*} (s : Finset ι)
    (P A : ι → QPoly) (d : ι → ℕ) :
    difference (∑ i ∈ s, d i) (center s P A) =
      center s (fun i => difference (d i) (P i))
        (fun i => difference (d i) (A i)) := by
  unfold center
  rw [allocated_product, allocated_product]
  unfold difference
  ring

theorem allocations_agree {ι : Type*} (s : Finset ι)
    (P A : ι → QPoly) (d e : ι → ℕ)
    (h : (∑ i ∈ s, d i) = ∑ i ∈ s, e i) :
    center s (fun i => difference (d i) (P i)) (fun i => difference (d i) (A i)) =
    center s (fun i => difference (e i) (P i)) (fun i => difference (e i) (A i)) := by
  rw [← cancellation_allocation, ← cancellation_allocation, h]

theorem difference_iterate (d e : ℕ) (P : QPoly) :
    difference d (difference e P) = difference (d+e) P := by
  simp [difference, pow_add, mul_assoc]

theorem arrival_zero (P : QPoly) : (difference 1 P).coeff 0 = P.coeff 0 := by
  simp [difference, sub_mul]

theorem arrival_succ (P : QPoly) (k : ℕ) :
    (difference 1 P).coeff (k+1) = P.coeff (k+1) - P.coeff k := by
  simp [difference, sub_mul]

theorem second_arrival (P : QPoly) (k : ℕ) :
    (difference 2 P).coeff (k+1) =
      (difference 1 P).coeff (k+1) - (difference 1 P).coeff k := by
  rw [← show 1+1=2 from rfl, ← difference_iterate, arrival_succ]

/-- One common factor for the two channels, exactly as required in section5. -/
theorem common_normalization {ι : Type*} (s : Finset ι)
    (P A : ι → QPoly) (c : ι → ℚ) :
    center s (fun i => C (c i) * P i) (fun i => C (c i) * A i) =
      C (∏ i ∈ s, c i) * center s P A := by
  simp only [center, Finset.prod_mul_distrib, ← map_prod]
  ring

theorem positive_common_scale {ι : Type*} (s : Finset ι) (den : ι → ℚ)
    (hden : ∀ i ∈ s, 0 < den i) : 0 < ∏ i ∈ s, (den i)⁻¹ := by
  exact Finset.prod_pos (fun i hi => inv_pos.mpr (hden i hi))

#print axioms root_bundle_injective
#print axioms cancellation_allocation
#print axioms common_normalization
end
end Erdos993.Floor216
