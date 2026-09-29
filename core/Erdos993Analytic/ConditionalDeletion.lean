import Erdos993Analytic.GraphExposure
import WeightedInducedCounting

/-! Uniform conditioning and the actual vertex-absent rank distribution.
No connectedness, forest, or unimodality hypothesis. USER compilation required.
The vertex-present and general residual-graph correspondences are separate. -/

namespace Erdos993.Analytic
open scoped BigOperators
open Counting Structure SecondGradient

theorem joint_event_mass {n : ℕ} (G : Graph n) (E : List (Fin n) → Prop)
    [DecidablePred E] :
    (∑ s ∈ (jointSupport G).filter E, (jointLaw G).weight s) =
      (((jointSupport G).filter E).card : ℝ) / ((jointSupport G).card : ℝ) := by
  simp only [jointLaw, Finset.sum_const, nsmul_eq_mul]
  ring

theorem joint_event_mass_pos {n : ℕ} (G : Graph n) (E : List (Fin n) → Prop)
    [DecidablePred E] (hne : ((jointSupport G).filter E).Nonempty) :
    0 < ∑ s ∈ (jointSupport G).filter E, (jointLaw G).weight s := by
  rw [joint_event_mass]
  exact div_pos (by exact_mod_cast Finset.card_pos.mpr hne)
    (by exact_mod_cast jointSupport_card_pos G)

theorem joint_condition_weight {n : ℕ} (G : Graph n) (E : List (Fin n) → Prop)
    [DecidablePred E]
    (hp : 0 < ∑ s ∈ (jointSupport G).filter E, (jointLaw G).weight s)
    (s : List (Fin n)) :
    ((jointLaw G).condition E hp).weight s =
      1 / (((jointSupport G).filter E).card : ℝ) := by
  change (1 / ((jointSupport G).card : ℝ)) /
      (∑ t ∈ (jointSupport G).filter E, (jointLaw G).weight t) = _
  rw [joint_event_mass]
  have hc : ((jointSupport G).card : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (jointSupport_card_pos G)
  rw [joint_event_mass] at hp
  have he : (((jointSupport G).filter E).card : ℝ) ≠ 0 := by
    intro he
    simp [he] at hp
  field_simp [hc, he]

def absentSupport {n : ℕ} (G : Graph n) (u : Fin n) : Finset (List (Fin n)) :=
  (jointSupport G).filter (fun s => u ∉ s)

theorem absentSupport_nonempty {n : ℕ} (G : Graph n) (u : Fin n) :
    (absentSupport G u).Nonempty := by
  exact ⟨[], Finset.mem_filter.mpr ⟨empty_mem_jointSupport G, by simp⟩⟩

theorem absent_rank_card {n : ℕ} (G : Graph n) (u : Fin n) (r : ℕ) :
    ((absentSupport G u).filter (fun s => s.length = r)).card =
      coefficient (deleteVertex G u) r := by
  have he : (absentSupport G u).filter (fun s => s.length = r) =
      (avoidingSets G u r).toFinset := by
    ext s
    simp only [absentSupport, Finset.mem_filter, mem_jointSupport,
      List.mem_toFinset, avoidingSets, List.mem_filter, mem_independentSets]
    simp only [List.contains_eq_mem, Bool.not_eq_true', decide_eq_false_iff_not]
    tauto
  rw [he, List.toFinset_card_of_nodup]
  · exact WeightedInduced.avoiding_coefficient G u r
  · exact List.Sublist.nodup List.filter_sublist
      (List.Sublist.nodup List.filter_sublist (vertex_subsets_nodup n))

theorem absentSupport_card {n : ℕ} (G : Graph n) (u : Fin n) :
    (absentSupport G u).card = CardinalityMoments.partition (deleteVertex G u) := by
  have hmap : ∀ s ∈ absentSupport G u, s.length ∈ Finset.range (n+1) := by
    intro s hs
    have h := supported_length_le G s (Finset.mem_filter.mp hs).1
    exact Finset.mem_range.mpr (by omega)
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  simp only [absent_rank_card]
  rw [← massThrough_eq_sum]
  apply CardinalityMoments.mass_stable
  · have h := deleteVertices_length u
    omega
  · exact fun j hj => coefficient_above_order _ hj

theorem absent_mass {n : ℕ} (G : Graph n) (u : Fin n) :
    (∑ s ∈ absentSupport G u, (jointLaw G).weight s) =
      mass (deleteVertex G u) / mass G := by
  rw [absentSupport, joint_event_mass G (fun s => u ∉ s)]
  change ((absentSupport G u).card : ℝ) / ((jointSupport G).card : ℝ) = _
  rw [absentSupport_card, jointSupport_card_partition] <;> rfl

noncomputable def absentLaw {n : ℕ} (G : Graph n) (u : Fin n) :
    FiniteLaw (List (Fin n)) :=
  (jointLaw G).condition (fun s => u ∉ s)
    (joint_event_mass_pos G _ (absentSupport_nonempty G u))

theorem absentLaw_weight {n : ℕ} (G : Graph n) (u : Fin n) (s : List (Fin n)) :
    (absentLaw G u).weight s = 1 / mass (deleteVertex G u) := by
  unfold absentLaw
  rw [joint_condition_weight]
  change 1 / ((absentSupport G u).card : ℝ) = _
  rw [absentSupport_card] <;> rfl

/-- The true conditional rank probability equals the actual minor's coefficient law. -/
theorem absent_rank_probability {n : ℕ} (G : Graph n) (u : Fin n) (r : ℕ) :
    (∑ s ∈ (absentLaw G u).support.filter (fun s => s.length = r),
      (absentLaw G u).weight s) = cardinalityProbability (deleteVertex G u) r := by
  simp only [absentLaw_weight, Finset.sum_const, nsmul_eq_mul]
  change (((absentSupport G u).filter (fun s => s.length = r)).card : ℝ) *
    (1 / mass (deleteVertex G u)) = _
  rw [absent_rank_card]
  unfold cardinalityProbability
  ring

#print axioms joint_condition_weight
#print axioms absentSupport_card
#print axioms absent_mass
#print axioms absent_rank_probability

end Erdos993.Analytic
