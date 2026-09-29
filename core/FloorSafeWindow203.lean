import CriticalExtraction

/-! A sufficient certificate for actual graph coefficients. This module does
not assert that the reported census boxes pass or that a catalogue is complete. -/
namespace Erdos993.Floor203
open Foundation

def delta (a : Nat → Nat) (r : Nat) : Int := (a (r+1) : Int) - a r

theorem decreasing_window (d : Nat → Int) (f l p q : Nat)
    (steps : ∀ r, f < r → r ≤ l → d r ≤ d (r-1))
    (fp : f ≤ p) (pq : p ≤ q) (ql : q ≤ l) : d q ≤ d p := by
  induction q with
  | zero =>
    have hp : p=0 := by omega
    subst p
    exact Int.le_refl _
  | succ q ih =>
    by_cases he : p=q+1
    · rw [he]
      exact Int.le_refl _
    · have h := steps (q+1) (by omega) ql
      have hpq : p ≤ q := by omega
      have hprev := ih hpq (by omega)
      simp only [Nat.add_sub_cancel] at h
      exact Int.le_trans h hprev

theorem graph_safe_window {n : Nat} (G : Graph n) (f l : Nat)
    (pre : ∀ r, r ≤ n → r < f → 0 ≤ delta (coefficient G) r)
    (suffix : ∀ r, r ≤ n → l < r → delta (coefficient G) r ≤ 0)
    (middle : ∀ r, f < r → r ≤ l →
      delta (coefficient G) r ≤ delta (coefficient G) (r-1)) :
    Unimodal (coefficient G) := by
  apply (graph_unimodal_iff_noRecovery G).mpr
  intro p q hpq hp
  by_cases hqn : q ≤ n
  · by_cases hpf : p < f
    · have hh := pre p (by omega) hpf
      unfold delta at hh
      omega
    · by_cases hlq : l < q
      · have hh := suffix q hqn hlq
        unfold delta at hh
        omega
      · have hh := decreasing_window (delta (coefficient G)) f l p q middle
          (by omega) (by omega) (by omega)
        unfold delta at hh
        omega
  · have hz := coefficient_above_order G (show n < q+1 by omega)
    omega

def windowCheck (n f l : Nat) (lo hi bend : Nat → Int) : Bool :=
  (List.range (n+1)).all fun r =>
    decide ((r < f → 0 ≤ lo r) ∧ (l < r → hi r ≤ 0) ∧
      (f < r → r ≤ l → bend r ≤ 0))

theorem checked_window_actual_graph {n : Nat} (G : Graph n) (f l : Nat)
    (lo hi bend : Nat → Int) (hl : l ≤ n)
    (enclose : ∀ r, r ≤ n → lo r ≤ delta (coefficient G) r ∧
      delta (coefficient G) r ≤ hi r)
    (curve : ∀ r, f < r → r ≤ l →
      delta (coefficient G) r - delta (coefficient G) (r-1) ≤ bend r)
    (passed : windowCheck n f l lo hi bend = true) :
    Unimodal (coefficient G) := by
  have checks : ∀ r, r ≤ n →
      (r < f → 0 ≤ lo r) ∧ (l < r → hi r ≤ 0) ∧
      (f < r → r ≤ l → bend r ≤ 0) := by
    intro r hr
    have hh := List.all_eq_true.mp passed r (List.mem_range.mpr (by omega))
    exact of_decide_eq_true hh
  apply graph_safe_window G f l
  · intro r hr hf
    exact Int.le_trans ((checks r hr).1 hf) (enclose r hr).1
  · intro r hr hh
    exact Int.le_trans (enclose r hr).2 ((checks r hr).2.1 hh)
  · intro r hf hr
    have hh := curve r hf hr
    have hn := (checks r (by omega)).2.2 hf hr
    omega

/-- Arithmetic used in the forest composition; LC convolution and actual
component decomposition are not proved by this scalar statement. -/
theorem two_large_components_impossible (L a b n : Nat)
    (ha : L < a) (hb : L < b) (hab : a+b ≤ n) (hn : n ≤ 2*L+1) : False := by
  omega

/-- Universal sorted four-bin terminal case in the centroid packing. -/
theorem four_terminal_bins (h a b c d : Nat)
    (ab : a ≤ b) (bc : b ≤ c) (cd : c ≤ d)
    (pair : h ≤ a+b) (total : a+b+c+d ≤ 2*h) :
    a=b ∧ b=c ∧ c=d ∧ 2*a=h := by omega

theorem five_terminal_bins_impossible (h a b c d e : Nat)
    (bc : b ≤ c) (cd : c ≤ d) (epos : 0 < e)
    (ab : a ≤ b) (pair : h ≤ a+b)
    (total : a+b+c+d+e ≤ 2*h) : False := by omega

theorem composite_half_redistribution (t p : Nat) (hp : 0 < p) (pt : p < t) :
    t+p ≤ 2*t-1 ∧ 2*t-p ≤ 2*t-1 ∧
    (t+p)+(2*t-p)+t=4*t := by omega

theorem floor42_of_actual_census
    (census : ∀ n, n ≤ 41 → ∀ G : Graph n, IsForest G → Unimodal (coefficient G))
    (w : Closure.CriticalWitness) : 42 ≤ w.n := by
  by_cases h : 42 ≤ w.n
  · exact h
  · have hu := census w.n (by omega) w.graph w.forest
    have hn := noRecovery_of_unimodal _ hu w.M w.b w.returnAfterFall w.firstFall
    have hr := w.returningRise
    omega

end Erdos993.Floor203
