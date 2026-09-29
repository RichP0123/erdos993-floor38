import Floor216LogConcavity
import Floor216GraphPolynomial

namespace Erdos993.Floor216
open Polynomial
open scoped BigOperators
noncomputable section

def intCoeff (P : QPoly) (k : ℤ) : ℚ := if 0 ≤ k then P.coeff k.toNat else 0

theorem intCoeff_sub_nat (P : QPoly) (k i : ℕ) :
    intCoeff P ((k : ℤ)-i) = if i ≤ k then P.coeff (k-i) else 0 := by
  by_cases h : i ≤ k
  · have hz : (0 : ℤ) ≤ (k : ℤ)-i := by omega
    simp [intCoeff, h]
  · have hz : ¬ (0 : ℤ) ≤ (k : ℤ)-i := by omega
    simp [intCoeff, h]

theorem coeff_mul_support (P Q : QPoly) (k : ℕ) :
    (P*Q).coeff k = ∑ i ∈ P.support, P.coeff i * intCoeff Q ((k : ℤ)-i) := by
  conv_lhs => rw [← sum_monomial_eq P]
  simp only [Polynomial.sum, Finset.sum_mul, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro i hi
  rw [intCoeff_sub_nat]
  by_cases h : i ≤ k
  · rw [if_pos h, ← Nat.sub_add_cancel h]
    simp [coeff_monomial_mul]
  · rw [if_neg h, mul_zero]
    rw [coeff_mul, Finset.sum_eq_zero]
    intro x hx
    have hn : x.1 ≠ i := by
      have hs := Finset.mem_antidiagonal.mp hx
      omega
    simp [coeff_monomial, Ne.symm hn]

theorem signed_convolution_nat_no_recovery (I J : Finset ℕ) (q : ℤ → ℚ)
    (a b : ℕ → ℚ) (hn : NonnegativeSequence q) (hh : NoHoles q) (hlc : LogConcave q)
    (ha : ∀ i ∈ I, 0 ≤ a i) (hb : ∀ j ∈ J, 0 ≤ b j)
    (separated : ∀ i ∈ I, ∀ j ∈ J, i < j) (k l : ℤ) (hkl : k < l)
    (fall : (∑ i ∈ I, a i*q (k-i)) - (∑ j ∈ J, b j*q (k-j)) < 0) :
    (∑ i ∈ I, a i*q (l-i)) - (∑ j ∈ J, b j*q (l-j)) ≤ 0 := by
  have hcross :
      (∑ i ∈ I, a i*q (l-i))*(∑ j ∈ J, b j*q (k-j)) ≤
      (∑ i ∈ I, a i*q (k-i))*(∑ j ∈ J, b j*q (l-j)) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    apply Finset.sum_le_sum
    intro i hi
    have hc := lc_cross_inequality q hn hh hlc i j k l (by exact_mod_cast separated i hi j hj) hkl
    have hc' := mul_le_mul_of_nonneg_left hc (mul_nonneg (ha i hi) (hb j hj))
    nlinarith only [hc']
  apply sub_nonpos.mpr
  apply cross_sum_no_recovery _ _ _ _ _ _ _ _ hcross (sub_neg.mp fall)
  · exact Finset.sum_nonneg (fun i hi => mul_nonneg (ha i hi) (hn _))
  · exact Finset.sum_nonneg (fun j hj => mul_nonneg (hb j hj) (hn _))
  · exact Finset.sum_nonneg (fun i hi => mul_nonneg (ha i hi) (hn _))
  · exact Finset.sum_nonneg (fun j hj => mul_nonneg (hb j hj) (hn _))

theorem difference_signs_of_graph_unimodal {n : ℕ} (G : Graph n)
    (hu : Unimodal (coefficient G)) : ∃ m : ℕ,
      (∀ i, i ≤ m → 0 ≤ (difference 1 (graphPolynomial G)).coeff i) ∧
      (∀ i, m < i → (difference 1 (graphPolynomial G)).coeff i ≤ 0) := by
  obtain ⟨m,up,down⟩ := hu
  refine ⟨m, ?_, ?_⟩
  · intro i hi
    cases i with
    | zero => simp [arrival_zero, graphPolynomial_coeff]
    | succ i =>
      rw [arrival_succ, graphPolynomial_coeff, graphPolynomial_coeff]
      exact sub_nonneg.mpr (by exact_mod_cast up i (by omega))
  · intro i hi
    cases i with
    | zero => omega
    | succ i =>
      rw [arrival_succ, graphPolynomial_coeff, graphPolynomial_coeff]
      exact sub_nonpos.mpr (by exact_mod_cast down i (by omega))

theorem product_difference_no_recovery (D Q : QPoly) (m : ℕ)
    (hpos : ∀ i, i ≤ m → 0 ≤ D.coeff i)
    (hneg : ∀ i, m < i → D.coeff i ≤ 0)
    (hn : NonnegativeSequence (intCoeff Q)) (hh : NoHoles (intCoeff Q))
    (hlc : LogConcave (intCoeff Q)) (k l : ℕ) (hkl : k < l)
    (fall : (D*Q).coeff k < 0) : (D*Q).coeff l ≤ 0 := by
  let I := D.support.filter (fun i => i ≤ m)
  let J := D.support.filter (fun i => ¬ i ≤ m)
  have formula (t : ℕ) : (D*Q).coeff t =
      (∑ i ∈ I, D.coeff i * intCoeff Q ((t : ℤ)-i)) -
      (∑ j ∈ J, (-D.coeff j) * intCoeff Q ((t : ℤ)-j)) := by
    rw [coeff_mul_support]
    simpa [I, J, neg_mul] using
      (Finset.sum_filter_add_sum_filter_not D.support (fun i : ℕ => i ≤ m)
        (fun i => D.coeff i * intCoeff Q ((t : ℤ)-i))).symm
  rw [formula] at fall ⊢
  exact signed_convolution_nat_no_recovery I J (intCoeff Q) (fun i => D.coeff i)
    (fun i => -D.coeff i) hn hh hlc
    (fun i hi => hpos i (Finset.mem_filter.mp hi).2)
    (fun j hj => neg_nonneg.mpr (hneg j (by have h := (Finset.mem_filter.mp hj).2; omega)))
    (fun i hi j hj => by
      have hi' := (Finset.mem_filter.mp hi).2
      have hj' := (Finset.mem_filter.mp hj).2
      omega) k l (by exact_mod_cast hkl) fall

/-- LC convolution preserves unimodality of actual graph coefficients. The
factorization may be supplied by the already proved disjoint-block identity. -/
theorem actual_graph_lc_convolution {n a b : ℕ} (G : Graph n) (H : Graph a) (K : Graph b)
    (identity : graphPolynomial G = graphPolynomial H * graphPolynomial K)
    (hu : Unimodal (coefficient H))
    (hh : NoHoles (intCoeff (graphPolynomial K)))
    (hlc : LogConcave (intCoeff (graphPolynomial K))) : Unimodal (coefficient G) := by
  have hn : NonnegativeSequence (intCoeff (graphPolynomial K)) := by
    intro i
    by_cases h : 0 ≤ i <;> simp [intCoeff, h, graphPolynomial_coeff]
  obtain ⟨m,hpos,hneg⟩ := difference_signs_of_graph_unimodal H hu
  have hid : difference 1 (graphPolynomial G) =
      difference 1 (graphPolynomial H) * graphPolynomial K := by
    rw [identity]
    simp only [difference, mul_assoc]
  apply (Foundation.graph_unimodal_iff_noRecovery G).mpr
  intro k l hkl hfall
  have hf : (difference 1 (graphPolynomial H) * graphPolynomial K).coeff (k+1) < 0 := by
    rw [← hid, arrival_succ, graphPolynomial_coeff, graphPolynomial_coeff]
    exact sub_neg.mpr (by exact_mod_cast hfall)
  have h := product_difference_no_recovery _ _ m hpos hneg hn hh hlc
    (k+1) (l+1) (by omega) hf
  rw [← hid, arrival_succ, graphPolynomial_coeff, graphPolynomial_coeff] at h
  exact_mod_cast sub_nonpos.mp h

#print axioms actual_graph_lc_convolution
end
end Erdos993.Floor216
