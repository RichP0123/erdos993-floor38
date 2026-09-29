import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Erdos993.Floor216

structure Interval where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq

def Interval.Contains (b : Interval) (x : ℚ) : Prop := b.lo ≤ x ∧ x ≤ b.hi
def Interval.add (a b : Interval) : Interval := ⟨a.lo+b.lo, a.hi+b.hi⟩
def Interval.sub (a b : Interval) : Interval := ⟨a.lo-b.hi, a.hi-b.lo⟩
def Interval.inter (a b : Interval) : Interval := ⟨max a.lo b.lo, min a.hi b.hi⟩
def Interval.mul (a b : Interval) : Interval :=
  ⟨min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi)),
   max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))⟩

theorem add_sound (a b : Interval) (x y : ℚ)
    (hx : a.Contains x) (hy : b.Contains y) : (a.add b).Contains (x+y) := by
  constructor <;> dsimp [Interval.add] <;> linarith [hx.1,hx.2,hy.1,hy.2]

theorem sub_sound (a b : Interval) (x y : ℚ)
    (hx : a.Contains x) (hy : b.Contains y) : (a.sub b).Contains (x-y) := by
  constructor <;> dsimp [Interval.sub] <;> linarith [hx.1,hx.2,hy.1,hy.2]

theorem intersection_sound (a b : Interval) (x : ℚ)
    (ha : a.Contains x) (hb : b.Contains x) : (a.inter b).Contains x := by
  exact ⟨max_le ha.1 hb.1, le_min ha.2 hb.2⟩

theorem fixed_mul_bounds (c x l u : ℚ) (hl : l ≤ x) (hu : x ≤ u) :
    min (c*l) (c*u) ≤ c*x ∧ c*x ≤ max (c*l) (c*u) := by
  by_cases hc : 0 ≤ c
  · exact ⟨le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left hl hc),
      le_trans (mul_le_mul_of_nonneg_left hu hc) (le_max_right _ _)⟩
  · have hc' : c ≤ 0 := le_of_lt (lt_of_not_ge hc)
    exact ⟨le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_left hu hc'),
      le_trans (mul_le_mul_of_nonpos_left hl hc') (le_max_left _ _)⟩

/-- Four-corner multiplication is sound for signed intervals, without
assuming that any coefficient or difference is positive. -/
theorem mul_sound (a b : Interval) (x y : ℚ)
    (hx : a.Contains x) (hy : b.Contains y) : (a.mul b).Contains (x*y) := by
  have hl := fixed_mul_bounds a.lo y b.lo b.hi hy.1 hy.2
  have hu := fixed_mul_bounds a.hi y b.lo b.hi hy.1 hy.2
  have hm := fixed_mul_bounds y x a.lo a.hi hx.1 hx.2
  rw [mul_comm y x, mul_comm y a.lo, mul_comm y a.hi] at hm
  exact ⟨le_trans (min_le_min hl.1 hu.1) hm.1,
    le_trans hm.2 (max_le_max hl.2 hu.2)⟩

def rounded (x : ℚ) : Interval := ⟨(⌊x⌋ : ℤ), (⌈x⌉ : ℤ)⟩

theorem signed_rounding (x : ℚ) : (rounded x).Contains x :=
  ⟨Int.floor_le x, Int.le_ceil x⟩

/-- Formula (5), retaining the same positive denominator and scale. -/
theorem normalized_rounding (z den M : ℚ) (_hden : 0 < den) (hM : 0 < M) :
    ((⌊M*z/den⌋ : ℤ) : ℚ) / M ≤ z/den ∧
      z/den ≤ ((⌈M*z/den⌉ : ℤ) : ℚ) / M := by
  have h := signed_rounding (M*z/den)
  constructor
  · apply (div_le_iff₀ hM).2
    calc
      ((⌊M*z/den⌋ : ℤ) : ℚ) ≤ M*z/den := h.1
      _ = z/den*M := by ring
  · apply (le_div_iff₀ hM).2
    calc
      z/den*M = M*z/den := by ring
      _ ≤ ((⌈M*z/den⌉ : ℤ) : ℚ) := h.2

#print axioms mul_sound
#print axioms intersection_sound
#print axioms normalized_rounding
end Erdos993.Floor216
