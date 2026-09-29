import Erdos993Analytic.ResidualLaw
import Erdos993Analytic.ConditionalMoments

/-! Exact rank correspondence with the actual relabelled induced residual graph.
No assumed equality of laws, forest bound, or connectedness hypothesis.
Draft for USER compilation. -/

namespace Erdos993.Analytic.ResidualSupport
open scoped BigOperators
open Counting Structure

theorem residual_rank_card {n : ℕ} (G : Graph n) (B O : Finset (Fin n)) (r : ℕ) :
    ((residualConfigs G B O).filter (fun S => S.card = r)).card =
      coefficient (residualGraph G B O) r := by
  classical
  let E := eligible G B O
  let A := (jointSupport G).filter (fun s => s.toFinset ⊆ E ∧ s.length = r)
  let C := (subsets (canonical E)).filter (fun s => decide (s.length = r) && independent G s)
  have hC : C.toFinset = A := by
    ext s
    simp [C, A, canonical, WeightedInduced.subsets_filter, mem_jointSupport,
      Finset.subset_iff, List.all_eq_true, and_assoc, and_left_comm, and_comm]
  have hn : C.Nodup :=
    List.Sublist.nodup List.filter_sublist (subsets_nodup _ (canonical_nodup E))
  have hc : A.card = coefficient (residualGraph G B O) r := by
    rw [← hC, List.toFinset_card_of_nodup hn]
    change C.length = coefficient (inducedOn G (canonical E)) r
    rw [coefficient_inducedOn, VertexIncidence.rankCount_as_filter]
  have hi : Set.InjOn (fun s : List (Fin n) => s.toFinset) A := by
    intro s hs t ht he
    change s.toFinset = t.toFinset at he
    have hsG := (Finset.mem_filter.mp hs).1
    have htG := (Finset.mem_filter.mp ht).1
    calc
      s = canonical s.toFinset := (canonical_of_supported G s hsG).symm
      _ = canonical t.toFinset := congrArg canonical he
      _ = t := canonical_of_supported G t htG
  have himage : A.image (fun s => s.toFinset) =
      (residualConfigs G B O).filter (fun S => S.card = r) := by
    ext S
    constructor
    · intro h
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨hsG, hsub, hr⟩ := Finset.mem_filter.mp hs
      apply Finset.mem_filter.mpr
      refine ⟨(mem_residualConfigs G B O _).mpr
        ⟨hsub, supported_independentSet G s hsG⟩, ?_⟩
      rw [List.toFinset_card_of_nodup (supported_nodup G s hsG), hr]
    · intro h
      obtain ⟨hS, hr⟩ := Finset.mem_filter.mp h
      obtain ⟨hsub, hind⟩ := (mem_residualConfigs G B O S).mp hS
      apply Finset.mem_image.mpr
      refine ⟨canonical S, ?_, canonical_toFinset S⟩
      apply Finset.mem_filter.mpr
      refine ⟨(canonical_mem_joint G S).mpr hind, ?_, ?_⟩
      · simpa only [canonical_toFinset] using hsub
      · rw [canonical_length, hr]
  rw [← himage, Finset.card_image_iff.mpr hi, hc]

theorem residual_card_partition {n : ℕ} (G : Graph n) (B O : Finset (Fin n)) :
    (residualConfigs G B O).card = CardinalityMoments.partition (residualGraph G B O) := by
  let N := (canonical (eligible G B O)).length
  have hmap : ∀ S ∈ residualConfigs G B O, S.card ∈ Finset.range (N+1) := by
    intro S hS
    have h := Finset.card_le_card ((mem_residualConfigs G B O S).mp hS).1
    have he : N = (eligible G B O).card := canonical_length _
    exact Finset.mem_range.mpr (by omega)
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  simp only [residual_rank_card]
  exact (massThrough_eq_sum (coefficient (residualGraph G B O)) N).symm

theorem residual_rank_probability {n : ℕ} (G : Graph n) (B O : Finset (Fin n)) (r : ℕ) :
    (∑ S ∈ (residualLaw G B O).support.filter (fun S => S.card = r),
      (residualLaw G B O).weight S) = cardinalityProbability (residualGraph G B O) r := by
  simp only [residualLaw, Finset.sum_const, nsmul_eq_mul]
  rw [residual_rank_card, residual_card_partition]
  unfold cardinalityProbability mass
  ring

theorem residual_graph_expectation {n : ℕ} (G : Graph n) (B O : Finset (Fin n))
    (f : ℕ → ℝ) :
    (residualLaw G B O).expectation (fun S => f S.card) =
      (coefficientLaw (residualGraph G B O)).expectation f := by
  apply cardinality_pushforward (residualLaw G B O) Finset.card
    (residualGraph G B O) (canonical (eligible G B O)).length (le_refl _)
  · intro S hS
    rw [canonical_length]
    exact Finset.card_le_card ((mem_residualConfigs G B O S).mp hS).1
  · exact residual_rank_probability G B O

theorem residual_graph_mean {n : ℕ} (G : Graph n) (B O : Finset (Fin n)) :
    (residualLaw G B O).expectation (fun S => (S.card : ℝ)) =
      mean (residualGraph G B O) := by
  rw [residual_graph_expectation, coefficientLaw_mean]

theorem residual_graph_variance {n : ℕ} (G : Graph n) (B O : Finset (Fin n)) :
    (residualLaw G B O).variance (fun S => (S.card : ℝ)) =
      cardinalityVariance (residualGraph G B O) := by
  unfold FiniteLaw.variance
  rw [residual_graph_mean]
  exact residual_graph_expectation G B O
    (fun k => ((k : ℝ) - mean (residualGraph G B O))^2)

theorem observed_actual_graph_mean {n : ℕ} (G : Graph n)
    (B O : Finset (Fin n)) (hOB : O ⊆ B) (hO : independentSet G O) :
    (observedLaw G B O hOB hO).expectation (fun s => (s.length : ℝ)) =
      (O.card : ℝ) + mean (residualGraph G B O) := by
  rw [observed_mean, residual_graph_mean]

theorem observed_actual_graph_variance {n : ℕ} (G : Graph n)
    (B O : Finset (Fin n)) (hOB : O ⊆ B) (hO : independentSet G O) :
    (observedLaw G B O hOB hO).variance (fun s => (s.length : ℝ)) =
      cardinalityVariance (residualGraph G B O) := by
  rw [observed_variance, residual_graph_variance]

#print axioms residual_rank_card
#print axioms residual_rank_probability
#print axioms residual_graph_expectation
#print axioms observed_actual_graph_mean
#print axioms observed_actual_graph_variance

end Erdos993.Analytic.ResidualSupport
