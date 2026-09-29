import Floor216Algebra
import Floor216Intervals
import Mathlib.Algebra.BigOperators.NatAntidiagonal

namespace Erdos993.Floor216
open Polynomial
open scoped BigOperators
noncomputable section

abbrev Bounds := ℕ → Interval
def Encloses (b : Bounds) (P : QPoly) : Prop := ∀ k, (b k).Contains (P.coeff k)
def zeroInterval : Interval := ⟨0,0⟩
def addBounds (a b : Bounds) : Bounds := fun k => (a k).add (b k)
def interBounds (a b : Bounds) : Bounds := fun k => (a k).inter (b k)
def shiftBounds (a : Bounds) : Bounds
  | 0 => zeroInterval
  | k+1 => a k
def differenceBounds (a : Bounds) : Bounds := fun k => (a k).sub (shiftBounds a k)
def sumIntervals {ι : Type*} (s : Finset ι) (a : ι → Interval) : Interval :=
  ⟨∑ i ∈ s, (a i).lo, ∑ i ∈ s, (a i).hi⟩
def convolutionBounds (a b : Bounds) : Bounds := fun k =>
  sumIntervals (Finset.range (k+1)) (fun i => (a i).mul (b (k-i)))

theorem sum_sound {ι : Type*} (s : Finset ι) (a : ι → Interval) (x : ι → ℚ)
    (h : ∀ i ∈ s, (a i).Contains (x i)) :
    (sumIntervals s a).Contains (∑ i ∈ s, x i) :=
  ⟨Finset.sum_le_sum (fun i hi => (h i hi).1),
   Finset.sum_le_sum (fun i hi => (h i hi).2)⟩

theorem add_encloses (a b : Bounds) (P Q : QPoly)
    (ha : Encloses a P) (hb : Encloses b Q) : Encloses (addBounds a b) (P+Q) := by
  intro k
  simpa only [Polynomial.coeff_add] using add_sound (a k) (b k) _ _ (ha k) (hb k)

theorem intersection_encloses (a b : Bounds) (P : QPoly)
    (ha : Encloses a P) (hb : Encloses b P) : Encloses (interBounds a b) P := by
  intro k
  exact intersection_sound (a k) (b k) _ (ha k) (hb k)

theorem shift_encloses (a : Bounds) (P : QPoly) (ha : Encloses a P) :
    Encloses (shiftBounds a) (X*P) := by
  intro k
  cases k with
  | zero => simp [shiftBounds, zeroInterval, Interval.Contains]
  | succ k => simpa only [Polynomial.coeff_X_mul] using ha k

theorem difference_encloses (a : Bounds) (P : QPoly) (ha : Encloses a P) :
    Encloses (differenceBounds a) (difference 1 P) := by
  intro k
  cases k with
  | zero =>
    rw [arrival_zero]
    simpa only [sub_zero] using sub_sound (a 0) zeroInterval (P.coeff 0) 0 (ha 0)
      (show zeroInterval.Contains 0 from ⟨le_rfl,le_rfl⟩)
  | succ k =>
    rw [arrival_succ]
    exact sub_sound (a (k+1)) (a k) _ _ (ha (k+1)) (ha k)

/-- Exact signed coefficient convolution, including all zero-extended tails. -/
theorem convolution_encloses (a b : Bounds) (P Q : QPoly)
    (ha : Encloses a P) (hb : Encloses b Q) :
    Encloses (convolutionBounds a b) (P*Q) := by
  intro k
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  exact sum_sound (Finset.range (k+1)) _ _
    (fun i _ => mul_sound (a i) (b (k-i)) _ _ (ha i) (hb (k-i)))

def oneBounds : Bounds
  | 0 => ⟨1,1⟩
  | _+1 => zeroInterval
def productBounds : List Bounds → Bounds
  | [] => oneBounds
  | a :: rest => convolutionBounds a (productBounds rest)

theorem one_encloses : Encloses oneBounds 1 := by
  intro k
  cases k <;> simp [oneBounds,zeroInterval,Interval.Contains,Polynomial.coeff_one]

theorem product_encloses (bs : List Bounds) (ps : List QPoly)
    (h : List.Forall₂ Encloses bs ps) : Encloses (productBounds bs) ps.prod := by
  induction h with
  | nil => exact one_encloses
  | cons hp hrest ih =>
    exact convolution_encloses _ _ _ _ hp ih

def evaluateBounds (bs cs : List Bounds) : Bounds :=
  addBounds (productBounds bs) (shiftBounds (productBounds cs))

/-- The checker evaluation formula (3) is valid for whole coefficient boxes. -/
theorem evaluate_encloses (bs cs : List Bounds) (ps qs : List QPoly)
    (hp : List.Forall₂ Encloses bs ps) (hq : List.Forall₂ Encloses cs qs) :
    Encloses (evaluateBounds bs cs) (ps.prod + X*qs.prod) :=
  add_encloses _ _ _ _ (product_encloses bs ps hp)
    (shift_encloses _ _ (product_encloses cs qs hq))

/-- The new FLOOR216 strengthening: differentiate the tightened first bounds,
then intersect with the old second bounds. -/
theorem tightened_second_difference (d e : Bounds) (P : QPoly)
    (hd : Encloses d (difference 1 P)) (he : Encloses e (difference 2 P)) :
    Encloses (interBounds e (differenceBounds d)) (difference 2 P) := by
  apply intersection_encloses _ _ _ he
  simpa only [difference_iterate] using difference_encloses d (difference 1 P) hd

def outward (M : ℚ) (a : Interval) : Interval :=
  ⟨((⌊M*a.lo⌋ : ℤ) : ℚ)/M, ((⌈M*a.hi⌉ : ℤ) : ℚ)/M⟩

/-- Rounding after convolution preserves inclusion at any positive fixed scale. -/
theorem outward_sound (M : ℚ) (hM : 0 < M) (a : Interval) (x : ℚ)
    (hx : a.Contains x) : (outward M a).Contains x := by
  have hl := normalized_rounding a.lo 1 M (by decide) hM
  have hu := normalized_rounding a.hi 1 M (by decide) hM
  simp only [div_one] at hl hu
  exact ⟨le_trans hl.1 hx.1, le_trans hx.2 hu.2⟩

#print axioms convolution_encloses
#print axioms evaluate_encloses
#print axioms tightened_second_difference
#print axioms outward_sound
end
end Erdos993.Floor216
