import Erdos993Analytic.ResidualSupport
import Erdos993Analytic.ConditionalDeletion
import Erdos993Analytic.FiniteProjection

/-! Bijection and uniform conditional law for arbitrary actual graph exposures.
Residual configurations use original labels; identification of their rank
counts with the relabelled induced graph is a subsequent obligation.
Draft for USER compilation. -/

namespace Erdos993.Analytic.ResidualSupport
open scoped BigOperators

theorem filter_members_of_sublist {α : Type*} [DecidableEq α]
    (xs s : List α) (hx : xs.Nodup) (hs : s.Sublist xs) :
    xs.filter (fun v => decide (v ∈ s)) = s := by
  induction xs generalizing s with
  | nil =>
    have he : s = [] := List.sublist_nil.mp hs
    subst s
    rfl
  | cons a xs ih =>
    obtain ⟨ha, hx⟩ := List.nodup_cons.mp hx
    rcases List.sublist_cons_iff.mp hs with hs | ⟨t, rfl, ht⟩
    · have has : a ∉ s := fun h => ha (hs.subset h)
      simpa [has] using ih s hx hs
    · have he : xs.filter (fun v => decide (v ∈ a :: t)) =
          xs.filter (fun v => decide (v ∈ t)) := by
        apply List.filter_congr
        intro v hv
        have hva : v ≠ a := by intro h; subst v; exact ha hv
        simp [hva]
      rw [List.filter_cons]
      simp only [List.mem_cons_self, decide_true, Bool.true_eq, ite_true]
      rw [he, ih t hx ht]

theorem canonical_of_supported {n : ℕ} (G : Graph n) (s : List (Fin n))
    (hs : s ∈ jointSupport G) : canonical s.toFinset = s := by
  have hsub := (mem_subsets s (List.finRange n)).mp ((mem_jointSupport G s).mp hs).1
  simpa only [canonical, List.mem_toFinset] using
    filter_members_of_sublist (List.finRange n) s (finRange_nodup n) hsub

def fiberConfigs {n : ℕ} (G : Graph n) (B O : Finset (Fin n)) :=
  (jointSupport G).filter (fun s => exposure B s = O)

theorem residual_map_injective {n : ℕ} (G : Graph n) (B O : Finset (Fin n)) :
    Set.InjOn (fun s : List (Fin n) => s.toFinset \ B) (fiberConfigs G B O) := by
  intro s hs t ht he
  change s.toFinset \ B = t.toFinset \ B at he
  obtain ⟨hs, hsO⟩ := Finset.mem_filter.mp hs
  obtain ⟨ht, htO⟩ := Finset.mem_filter.mp ht
  have hsets : s.toFinset = t.toFinset := by
    rw [← supported_reconstruction B O s hsO,
      ← supported_reconstruction B O t htO, he]
  calc
    s = canonical s.toFinset := (canonical_of_supported G s hs).symm
    _ = canonical t.toFinset := congrArg canonical hsets
    _ = t := canonical_of_supported G t ht

theorem fiber_card {n : ℕ} (G : Graph n) (B O : Finset (Fin n))
    (hOB : O ⊆ B) (hO : independentSet G O) :
    (fiberConfigs G B O).card = (residualConfigs G B O).card := by
  have hc := Finset.card_image_iff.mpr (residual_map_injective G B O)
  change (((jointSupport G).filter (fun s => exposure B s = O)).image
    (fun s => s.toFinset \ B)).card = (fiberConfigs G B O).card at hc
  rw [actual_fiber_image G B O hOB hO] at hc
  exact hc.symm

theorem empty_mem_residual {n : ℕ} (G : Graph n) (B O : Finset (Fin n)) :
    ∅ ∈ residualConfigs G B O := by
  rw [mem_residualConfigs]
  simp [independentSet]

theorem residual_card_pos {n : ℕ} (G : Graph n) (B O : Finset (Fin n)) :
    0 < (residualConfigs G B O).card :=
  Finset.card_pos.mpr ⟨∅, empty_mem_residual G B O⟩

theorem fiber_nonempty {n : ℕ} (G : Graph n) (B O : Finset (Fin n))
    (hOB : O ⊆ B) (hO : independentSet G O) : (fiberConfigs G B O).Nonempty := by
  apply Finset.card_pos.mp
  rw [fiber_card G B O hOB hO]
  exact residual_card_pos G B O

noncomputable def observedLaw {n : ℕ} (G : Graph n) (B O : Finset (Fin n))
    (hOB : O ⊆ B) (hO : independentSet G O) : FiniteLaw (List (Fin n)) :=
  (jointLaw G).condition (fun s => exposure B s = O)
    (joint_event_mass_pos G _ (fiber_nonempty G B O hOB hO))

noncomputable def residualLaw {n : ℕ} (G : Graph n) (B O : Finset (Fin n)) :
    FiniteLaw (Finset (Fin n)) where
  support := residualConfigs G B O
  weight _ := 1 / ((residualConfigs G B O).card : ℝ)
  nonneg _ _ := by positivity
  normalized := by
    have hz : ((residualConfigs G B O).card : ℝ) ≠ 0 := by
      exact_mod_cast ne_of_gt (residual_card_pos G B O)
    simp only [Finset.sum_const, nsmul_eq_mul]
    field_simp [hz]

theorem observedLaw_weight {n : ℕ} (G : Graph n) (B O : Finset (Fin n))
    (hOB : O ⊆ B) (hO : independentSet G O) (s : List (Fin n)) :
    (observedLaw G B O hOB hO).weight s =
      1 / ((residualConfigs G B O).card : ℝ) := by
  unfold observedLaw
  rw [joint_condition_weight]
  change 1 / ((fiberConfigs G B O).card : ℝ) = _
  rw [fiber_card G B O hOB hO]

/-- Equality for every test function, not just the mean or variance. -/
theorem observed_residual_expectation {n : ℕ} (G : Graph n)
    (B O : Finset (Fin n)) (hOB : O ⊆ B) (hO : independentSet G O)
    (f : Finset (Fin n) → ℝ) :
    (observedLaw G B O hOB hO).expectation (fun s => f (s.toFinset \ B)) =
      (residualLaw G B O).expectation f := by
  classical
  unfold FiniteLaw.expectation
  simp only [observedLaw_weight]
  change (∑ s ∈ fiberConfigs G B O,
    (1 / ((residualConfigs G B O).card : ℝ)) * f (s.toFinset \ B)) =
    ∑ S ∈ residualConfigs G B O, (1 / ((residualConfigs G B O).card : ℝ)) * f S
  have himage : (fiberConfigs G B O).image (fun s => s.toFinset \ B) =
      residualConfigs G B O := actual_fiber_image G B O hOB hO
  calc
    _ = ∑ S ∈ (fiberConfigs G B O).image (fun s => s.toFinset \ B),
        (1 / ((residualConfigs G B O).card : ℝ)) * f S := by
      symm
      exact Finset.sum_image (residual_map_injective G B O)
    _ = _ := by rw [himage]

theorem observed_length_split {n : ℕ} (G : Graph n) (B O : Finset (Fin n))
    (hOB : O ⊆ B) (s : List (Fin n)) (hs : s ∈ fiberConfigs G B O) :
    s.length = O.card + (s.toFinset \ B).card := by
  obtain ⟨hs, he⟩ := Finset.mem_filter.mp hs
  have hd : Disjoint O (s.toFinset \ B) := by
    apply Finset.disjoint_left.mpr
    intro v hvO hvS
    exact (Finset.mem_sdiff.mp hvS).2 (hOB hvO)
  have hc := Finset.card_union_of_disjoint hd
  rw [supported_reconstruction B O s he] at hc
  rw [← List.toFinset_card_of_nodup (supported_nodup G s hs)]
  exact hc

theorem observed_cardinality_expectation {n : ℕ} (G : Graph n)
    (B O : Finset (Fin n)) (hOB : O ⊆ B) (hO : independentSet G O)
    (f : ℕ → ℝ) :
    (observedLaw G B O hOB hO).expectation (fun s => f s.length) =
      (residualLaw G B O).expectation (fun S => f (O.card + S.card)) := by
  rw [← observed_residual_expectation G B O hOB hO (fun S => f (O.card + S.card))]
  apply FiniteLaw.expectation_congr_support
  intro s hs
  change f s.length = f (O.card + (s.toFinset \ B).card)
  rw [observed_length_split G B O hOB s hs]

theorem observed_mean {n : ℕ} (G : Graph n)
    (B O : Finset (Fin n)) (hOB : O ⊆ B) (hO : independentSet G O) :
    (observedLaw G B O hOB hO).expectation (fun s => (s.length : ℝ)) =
      (O.card : ℝ) + (residualLaw G B O).expectation (fun S => (S.card : ℝ)) := by
  rw [observed_cardinality_expectation]
  simp only [Nat.cast_add, FiniteLaw.expectation_add, FiniteLaw.expectation_const]

theorem observed_variance {n : ℕ} (G : Graph n)
    (B O : Finset (Fin n)) (hOB : O ⊆ B) (hO : independentSet G O) :
    (observedLaw G B O hOB hO).variance (fun s => (s.length : ℝ)) =
      (residualLaw G B O).variance (fun S => (S.card : ℝ)) := by
  unfold FiniteLaw.variance
  rw [observed_mean]
  rw [observed_cardinality_expectation G B O hOB hO
    (fun k => ((k : ℝ) - ((O.card : ℝ) +
      (residualLaw G B O).expectation (fun S => (S.card : ℝ))))^2)]
  apply FiniteLaw.expectation_congr_support
  intro S hS
  push_cast
  ring

#print axioms canonical_of_supported
#print axioms residual_map_injective
#print axioms fiber_card
#print axioms observed_residual_expectation
#print axioms observed_mean
#print axioms observed_variance

end Erdos993.Analytic.ResidualSupport
