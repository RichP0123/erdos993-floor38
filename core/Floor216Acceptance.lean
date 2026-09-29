import Floor216Enclosures
import FloorSafeWindow203
import Mathlib.Tactic.NormNum

namespace Erdos993.Floor216
open Polynomial
open scoped BigOperators
noncomputable section

/-- The polynomial is built from the project's actual graph coefficients. -/
def graphPolynomial {n : ℕ} (G : Graph n) : QPoly :=
  ∑ k ∈ Finset.range (n+1), monomial k (coefficient G k : ℚ)

theorem graphPolynomial_coeff {n : ℕ} (G : Graph n) (k : ℕ) :
    (graphPolynomial G).coeff k = (coefficient G k : ℚ) := by
  classical
  by_cases hk : k < n+1
  · simp [graphPolynomial, Polynomial.coeff_monomial, hk]
  · have hz := coefficient_above_order G (show n < k by omega)
    simp [graphPolynomial, Polynomial.coeff_monomial, hk, hz]

def normalizedGraph {n : ℕ} (G : Graph n) (s : ℚ) : QPoly := C s * graphPolynomial G

theorem normalizedGraph_coeff {n : ℕ} (G : Graph n) (s : ℚ) (k : ℕ) :
    (normalizedGraph G s).coeff k = s * (coefficient G k : ℚ) := by
  simp [normalizedGraph, graphPolynomial_coeff]

/-- Explicit arrival/departure index conversion; no sign convention is implicit. -/
theorem normalized_departure {n : ℕ} (G : Graph n) (s : ℚ) (r : ℕ) :
    (difference 1 (normalizedGraph G s)).coeff (r+1) =
      s * (Floor203.delta (coefficient G) r : ℚ) := by
  rw [arrival_succ, normalizedGraph_coeff, normalizedGraph_coeff]
  simp only [Floor203.delta, Int.cast_sub, Int.cast_natCast]
  ring

theorem normalized_curvature {n : ℕ} (G : Graph n) (s : ℚ) (r : ℕ) (hr : 0 < r) :
    (difference 2 (normalizedGraph G s)).coeff (r+1) =
      s * ((Floor203.delta (coefficient G) r : ℚ) -
        (Floor203.delta (coefficient G) (r-1) : ℚ)) := by
  rw [second_arrival, normalized_departure]
  have prev : (difference 1 (normalizedGraph G s)).coeff r =
      s * (Floor203.delta (coefficient G) (r-1) : ℚ) := by
    have he : r-1+1 = r := by omega
    simpa only [he] using normalized_departure G s (r-1)
  rw [prev]
  ring

def windowCheck (n f l : ℕ) (d e : Bounds) : Bool :=
  (List.range (n+1)).all fun r =>
    decide ((r < f → 0 ≤ (d (r+1)).lo) ∧
      (l < r → (d (r+1)).hi ≤ 0) ∧
      (f < r → r ≤ l → (e (r+1)).hi ≤ 0))

/-- General soundness of the FLOOR216 sign/curvature acceptance formula,
directly for actual graphs. The hypotheses are enclosure and passing bounds,
not the desired unimodality or a census completeness assumption. -/
theorem graph_certificate_sound {n : ℕ} (G : Graph n) (s : ℚ) (hs : 0 < s)
    (d e : Bounds) (f l : ℕ) (hlength : l ≤ n)
    (hd : Encloses d (difference 1 (normalizedGraph G s)))
    (he : Encloses e (difference 2 (normalizedGraph G s)))
    (passed : windowCheck n f l d e = true) : Unimodal (coefficient G) := by
  have tests : ∀ r, r ≤ n →
      (r < f → 0 ≤ (d (r+1)).lo) ∧
      (l < r → (d (r+1)).hi ≤ 0) ∧
      (f < r → r ≤ l → (e (r+1)).hi ≤ 0) := by
    intro r hr
    exact of_decide_eq_true (List.all_eq_true.mp passed r (List.mem_range.mpr (by omega)))
  apply Floor203.graph_safe_window G f l
  · intro r hr hf
    have hb := (hd (r+1)).1
    rw [normalized_departure] at hb
    have hc := (tests r hr).1 hf
    have hrat : (0:ℚ) ≤ (Floor203.delta (coefficient G) r : ℚ) := by nlinarith
    exact_mod_cast hrat
  · intro r hr hl
    have hb := (hd (r+1)).2
    rw [normalized_departure] at hb
    have hc := (tests r hr).2.1 hl
    have hrat : (Floor203.delta (coefficient G) r : ℚ) ≤ 0 := by nlinarith
    exact_mod_cast hrat
  · intro r hf hl
    have hb := (he (r+1)).2
    rw [normalized_curvature G s r (by omega)] at hb
    have hc := (tests r (by omega)).2.2 hf hl
    have hrat : (Floor203.delta (coefficient G) r : ℚ) ≤
        (Floor203.delta (coefficient G) (r-1) : ℚ) := by nlinarith
    exact_mod_cast hrat

#print axioms graphPolynomial_coeff
#print axioms normalized_curvature
#print axioms graph_certificate_sound
end
end Erdos993.Floor216
