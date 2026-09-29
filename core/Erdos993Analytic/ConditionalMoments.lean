import Erdos993Analytic.ConditionalInclusion

/-! Expectations and variances of the actual single-vertex conditional laws.
These use the rank probability identities, not an assumed distribution match.
USER compilation required. -/

namespace Erdos993.Analytic
open scoped BigOperators
open Counting Structure LeafBoundary ForestReturnPhases

theorem cardinality_pushforward {Ω : Type*} (P : FiniteLaw Ω) (rank : Ω → ℕ)
    {m : ℕ} (H : Graph m) (N : ℕ) (hm : m ≤ N)
    (hbound : ∀ x ∈ P.support, rank x ≤ N)
    (hprob : ∀ r, (∑ x ∈ P.support.filter (fun x => rank x = r), P.weight x) =
      cardinalityProbability H r) (f : ℕ → ℝ) :
    P.expectation (fun x => f (rank x)) = (coefficientLaw H).expectation f := by
  classical
  have hmap : ∀ x ∈ P.support, rank x ∈ Finset.range (N+1) := by
    intro x hx
    exact Finset.mem_range.mpr (by have h := hbound x hx; omega)
  unfold FiniteLaw.expectation
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  calc
    _ = ∑ r ∈ Finset.range (N+1), cardinalityProbability H r * f r := by
      apply Finset.sum_congr rfl
      intro r hr
      calc
        _ = ∑ x ∈ P.support.filter (fun x => rank x = r), P.weight x * f r := by
          apply Finset.sum_congr rfl
          intro x hx
          change P.weight x * f (rank x) = P.weight x * f r
          rw [(Finset.mem_filter.mp hx).2]
        _ = _ := by rw [← Finset.sum_mul, hprob]
    _ = ∑ r ∈ Finset.range (m+1), cardinalityProbability H r * f r := by
      symm
      apply Finset.sum_subset
      · exact Finset.range_mono (by omega)
      · intro r hr hnot
        have hmr : m < r := by
          simp only [Finset.mem_range] at hnot
          omega
        rw [cardinalityProbability_above_order H hmr, zero_mul]
    _ = _ := rfl

theorem absent_expectation {n : ℕ} (G : Graph n) (u : Fin n) (f : ℕ → ℝ) :
    (absentLaw G u).expectation (fun s => f s.length) =
      (coefficientLaw (deleteVertex G u)).expectation f := by
  apply cardinality_pushforward (absentLaw G u) List.length (deleteVertex G u) n
  · have h := deleteVertices_length u
    omega
  · intro s hs
    exact supported_length_le G s (Finset.mem_filter.mp hs).1
  · exact absent_rank_probability G u

theorem absent_mean {n : ℕ} (G : Graph n) (u : Fin n) :
    (absentLaw G u).expectation (fun s => (s.length : ℝ)) =
      mean (deleteVertex G u) := by
  rw [absent_expectation, coefficientLaw_mean]

theorem absent_variance {n : ℕ} (G : Graph n) (u : Fin n) :
    (absentLaw G u).variance (fun s => (s.length : ℝ)) =
      cardinalityVariance (deleteVertex G u) := by
  unfold FiniteLaw.variance
  rw [absent_mean]
  exact absent_expectation G u (fun r => ((r : ℝ) - mean (deleteVertex G u))^2)

theorem present_length_pos {n : ℕ} (G : Graph n) (u : Fin n)
    (s : List (Fin n)) (hs : s ∈ (presentLaw G u).support) : 0 < s.length := by
  have hu : u ∈ s := (Finset.mem_filter.mp hs).2
  cases s with
  | nil => simp at hu
  | cons v t => simp

theorem present_residual_rank_probability {n : ℕ} (G : Graph n) (u : Fin n) (r : ℕ) :
    (∑ s ∈ (presentLaw G u).support.filter (fun s => s.length-1 = r),
      (presentLaw G u).weight s) =
        cardinalityProbability (inducedOn G (closedVertices G u)) r := by
  have he : (presentLaw G u).support.filter (fun s => s.length-1 = r) =
      (presentLaw G u).support.filter (fun s => s.length = r+1) := by
    ext s
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hs, hr⟩
      have hp := present_length_pos G u s hs
      exact ⟨hs, by omega⟩
    · rintro ⟨hs, hr⟩
      exact ⟨hs, by omega⟩
  rw [he]
  exact present_rank_probability_succ G u r

theorem present_residual_expectation {n : ℕ} (G : Graph n) (u : Fin n) (f : ℕ → ℝ) :
    (presentLaw G u).expectation (fun s => f (s.length-1)) =
      (coefficientLaw (inducedOn G (closedVertices G u))).expectation f := by
  apply cardinality_pushforward (presentLaw G u) (fun s => s.length-1)
    (inducedOn G (closedVertices G u)) n
  · have hlen := deleteVertices_length u
    have hf : (closedVertices G u).length ≤ (deleteVertices u).length :=
      List.length_filter_le _ _
    omega
  · intro s hs
    have h := supported_length_le G s (Finset.mem_filter.mp hs).1
    omega
  · exact present_residual_rank_probability G u

theorem present_expectation {n : ℕ} (G : Graph n) (u : Fin n) (f : ℕ → ℝ) :
    (presentLaw G u).expectation (fun s => f s.length) =
      (coefficientLaw (inducedOn G (closedVertices G u))).expectation (fun r => f (r+1)) := by
  rw [← present_residual_expectation G u (fun r => f (r+1))]
  apply Finset.sum_congr rfl
  intro s hs
  have hp := present_length_pos G u s hs
  have he : s.length-1+1 = s.length := by omega
  change (presentLaw G u).weight s * f s.length =
    (presentLaw G u).weight s * f (s.length-1+1)
  rw [he]

theorem present_mean {n : ℕ} (G : Graph n) (u : Fin n) :
    (presentLaw G u).expectation (fun s => (s.length : ℝ)) =
      1 + mean (inducedOn G (closedVertices G u)) := by
  rw [present_expectation]
  simp only [Nat.cast_add, Nat.cast_one, FiniteLaw.expectation_add,
    FiniteLaw.expectation_const, coefficientLaw_mean]
  ring

theorem present_variance {n : ℕ} (G : Graph n) (u : Fin n) :
    (presentLaw G u).variance (fun s => (s.length : ℝ)) =
      cardinalityVariance (inducedOn G (closedVertices G u)) := by
  unfold FiniteLaw.variance
  rw [present_mean]
  rw [present_expectation G u
    (fun r => ((r : ℝ) - (1 + mean (inducedOn G (closedVertices G u))))^2)]
  change (∑ r ∈ Finset.range ((closedVertices G u).length+1),
    cardinalityProbability (inducedOn G (closedVertices G u)) r *
      (((r+1 : ℕ) : ℝ) - (1 + mean (inducedOn G (closedVertices G u))))^2) = _
  unfold cardinalityVariance
  apply Finset.sum_congr rfl
  intro r hr
  push_cast
  ring

#print axioms cardinality_pushforward
#print axioms absent_mean
#print axioms absent_variance
#print axioms present_mean
#print axioms present_variance

end Erdos993.Analytic
