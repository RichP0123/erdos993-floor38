import Floor216Algebra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Erdos993.Floor216
open scoped BigOperators

def NonnegativeSequence (q : ℤ → ℚ) : Prop := ∀ i, 0 ≤ q i
def NoHoles (q : ℤ → ℚ) : Prop :=
  ∀ a b c, a ≤ b → b ≤ c → 0 < q a → 0 < q c → 0 < q b
def LogConcave (q : ℤ → ℚ) : Prop := ∀ i, q (i-1) * q (i+1) ≤ q i ^ 2

theorem lc_adjacent_nat (q : ℤ → ℚ) (hn : NonnegativeSequence q)
    (hh : NoHoles q) (hlc : LogConcave q) (a : ℤ) (d : ℕ) :
    q a * q (a+(d:ℤ)+1) ≤ q (a+1) * q (a+(d:ℤ)) := by
  induction d with
  | zero => simp [mul_comm]
  | succ d ih =>
    rw [show a+((d+1:ℕ):ℤ)+1 = a+(d:ℤ)+2 by omega,
      show a+((d+1:ℕ):ℤ) = a+(d:ℤ)+1 by omega]
    by_cases ha : q a = 0
    · rw [ha, zero_mul]
      exact mul_nonneg (hn _) (hn _)
    by_cases hz : q (a+(d:ℤ)+2) = 0
    · rw [hz, mul_zero]
      exact mul_nonneg (hn _) (hn _)
    have hpa : 0 < q a := lt_of_le_of_ne (hn _) (Ne.symm ha)
    have hpz : 0 < q (a+(d:ℤ)+2) := lt_of_le_of_ne (hn _) (Ne.symm hz)
    have hm : 0 < q (a+(d:ℤ)+1) := hh a _ _ (by omega) (by omega) hpa hpz
    have hc := hlc (a+(d:ℤ)+1)
    rw [show a+(d:ℤ)+1-1 = a+(d:ℤ) by omega,
      show a+(d:ℤ)+1+1 = a+(d:ℤ)+2 by omega] at hc
    apply (mul_le_mul_iff_left₀ hm).mp
    calc
      (q a*q (a+(d:ℤ)+2))*q (a+(d:ℤ)+1) =
          (q a*q (a+(d:ℤ)+1))*q (a+(d:ℤ)+2) := by ring
      _ ≤ (q (a+1)*q (a+(d:ℤ)))*q (a+(d:ℤ)+2) :=
        mul_le_mul_of_nonneg_right ih (hn _)
      _ = q (a+1)*(q (a+(d:ℤ))*q (a+(d:ℤ)+2)) := by ring
      _ ≤ q (a+1)*q (a+(d:ℤ)+1)^2 := mul_le_mul_of_nonneg_left hc (hn _)
      _ = (q (a+1)*q (a+(d:ℤ)+1))*q (a+(d:ℤ)+1) := by ring

theorem lc_adjacent (q : ℤ → ℚ) (hn : NonnegativeSequence q)
    (hh : NoHoles q) (hlc : LogConcave q) (a b : ℤ) (hab : a ≤ b) :
    q a*q (b+1) ≤ q (a+1)*q b := by
  obtain ⟨d, hd⟩ := Int.le.dest hab
  rw [← hd]
  exact lc_adjacent_nat q hn hh hlc a d

theorem lc_shift_nat (q : ℤ → ℚ) (hn : NonnegativeSequence q)
    (hh : NoHoles q) (hlc : LogConcave q) (a b : ℤ) (hab : a ≤ b) (d : ℕ) :
    q a*q (b+(d:ℤ)) ≤ q b*q (a+(d:ℤ)) := by
  induction d with
  | zero => simp [mul_comm]
  | succ d ih =>
    rw [show b+((d+1:ℕ):ℤ) = b+(d:ℤ)+1 by omega,
      show a+((d+1:ℕ):ℤ) = a+(d:ℤ)+1 by omega]
    by_cases ha : q a = 0
    · rw [ha, zero_mul]
      exact mul_nonneg (hn _) (hn _)
    by_cases hz : q (b+(d:ℤ)+1) = 0
    · rw [hz, mul_zero]
      exact mul_nonneg (hn _) (hn _)
    have hpa : 0 < q a := lt_of_le_of_ne (hn _) (Ne.symm ha)
    have hpz : 0 < q (b+(d:ℤ)+1) := lt_of_le_of_ne (hn _) (Ne.symm hz)
    have hm : 0 < q (b+(d:ℤ)) := hh a _ _ (by omega) (by omega) hpa hpz
    have hc := lc_adjacent q hn hh hlc (a+(d:ℤ)) (b+(d:ℤ)) (by omega)
    apply (mul_le_mul_iff_left₀ hm).mp
    calc
      (q a*q (b+(d:ℤ)+1))*q (b+(d:ℤ)) =
          (q a*q (b+(d:ℤ)))*q (b+(d:ℤ)+1) := by ring
      _ ≤ (q b*q (a+(d:ℤ)))*q (b+(d:ℤ)+1) :=
        mul_le_mul_of_nonneg_right ih (hn _)
      _ = q b*(q (a+(d:ℤ))*q (b+(d:ℤ)+1)) := by ring
      _ ≤ q b*(q (a+(d:ℤ)+1)*q (b+(d:ℤ))) := mul_le_mul_of_nonneg_left hc (hn _)
      _ = (q b*q (a+(d:ℤ)+1))*q (b+(d:ℤ)) := by ring

/-- Formula (6), derived from ordinary LC and no holes, including zero tails. -/
theorem lc_cross_inequality (q : ℤ → ℚ) (hn : NonnegativeSequence q)
    (hh : NoHoles q) (hlc : LogConcave q) (i j k l : ℤ)
    (hij : i < j) (hkl : k < l) :
    q (l-i)*q (k-j) ≤ q (k-i)*q (l-j) := by
  have h := lc_shift_nat q hn hh hlc (k-j) (k-i) (by omega) (l-k).toNat
  have hd : ((l-k).toNat : ℤ) = l-k := Int.toNat_of_nonneg (by omega)
  rw [hd, show k-i+(l-k)=l-i by omega, show k-j+(l-k)=l-j by omega] at h
  simpa only [mul_comm (q (l-i)) (q (k-j))] using h

theorem weighted_cross_sum (I J : Finset ℤ) (q a b : ℤ → ℚ)
    (ha : ∀ i ∈ I, 0 ≤ a i) (hb : ∀ j ∈ J, 0 ≤ b j)
    (k l : ℤ)
    (hcross : ∀ i ∈ I, ∀ j ∈ J, q (l-i)*q (k-j) ≤ q (k-i)*q (l-j)) :
    (∑ i ∈ I, a i*q (l-i))*(∑ j ∈ J, b j*q (k-j)) ≤
      (∑ i ∈ I, a i*q (k-i))*(∑ j ∈ J, b j*q (l-j)) := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  apply Finset.sum_le_sum
  intro i hi
  calc
    (a i*q (l-i))*(b j*q (k-j)) = (a i*b j)*(q (l-i)*q (k-j)) := by ring
    _ ≤ (a i*b j)*(q (k-i)*q (l-j)) :=
      mul_le_mul_of_nonneg_left (hcross i hi j hj) (mul_nonneg (ha i hi) (hb j hj))
    _ = (a i*q (k-i))*(b j*q (l-j)) := by ring

/-- The final sign argument from the paper; weak plateaus are retained. -/
theorem cross_sum_no_recovery (Ck Dk Cl Dl : ℚ)
    (hCk : 0 ≤ Ck) (_hDk : 0 ≤ Dk) (_hCl : 0 ≤ Cl) (hDl : 0 ≤ Dl)
    (hcross : Cl*Dk ≤ Ck*Dl) (hfall : Ck < Dk) : Cl ≤ Dl := by
  by_contra h
  have hrise : Dl < Cl := lt_of_not_ge h
  have hpos : 0 < Cl := lt_of_le_of_lt hDl hrise
  have h1 : Cl*Ck < Cl*Dk := mul_lt_mul_of_pos_left hfall hpos
  have h2 : Ck*Dl ≤ Ck*Cl := mul_le_mul_of_nonneg_left (le_of_lt hrise) hCk
  nlinarith

theorem signed_convolution_no_recovery (I J : Finset ℤ) (q a b : ℤ → ℚ)
    (hn : NonnegativeSequence q) (hh : NoHoles q) (hlc : LogConcave q)
    (ha : ∀ i ∈ I, 0 ≤ a i) (hb : ∀ j ∈ J, 0 ≤ b j)
    (separated : ∀ i ∈ I, ∀ j ∈ J, i < j)
    (k l : ℤ) (hkl : k < l)
    (fall : (∑ i ∈ I, a i*q (k-i)) - (∑ j ∈ J, b j*q (k-j)) < 0) :
    (∑ i ∈ I, a i*q (l-i)) - (∑ j ∈ J, b j*q (l-j)) ≤ 0 := by
  have hcross := weighted_cross_sum I J q a b ha hb k l
    (fun i hi j hj => lc_cross_inequality q hn hh hlc i j k l (separated i hi j hj) hkl)
  apply sub_nonpos.mpr
  apply cross_sum_no_recovery _ _ _ _ _ _ _ _ hcross (sub_neg.mp fall)
  · exact Finset.sum_nonneg (fun i hi => mul_nonneg (ha i hi) (hn _))
  · exact Finset.sum_nonneg (fun j hj => mul_nonneg (hb j hj) (hn _))
  · exact Finset.sum_nonneg (fun i hi => mul_nonneg (ha i hi) (hn _))
  · exact Finset.sum_nonneg (fun j hj => mul_nonneg (hb j hj) (hn _))

#print axioms lc_cross_inequality
#print axioms weighted_cross_sum
#print axioms cross_sum_no_recovery
#print axioms signed_convolution_no_recovery
end Erdos993.Floor216
