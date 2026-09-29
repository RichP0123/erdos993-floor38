import Erdos993Analytic.FiniteLaw

/-! Uniform law on actual canonical independent vertex subsets.
This constructs the joint occupation space, retaining all components,
and identifies each rank probability with the original graph coefficient law.
Graph-deletion conditional correspondences remain separate obligations.
New draft: USER compilation required. -/

namespace Erdos993.Analytic
open scoped BigOperators

def jointSupport {n : ℕ} (G : Graph n) : Finset (List (Fin n)) :=
  ((subsets (List.finRange n)).filter (independent G)).toFinset

theorem mem_jointSupport {n : ℕ} (G : Graph n) (s : List (Fin n)) :
    s ∈ jointSupport G ↔ s ∈ subsets (List.finRange n) ∧ independent G s = true := by
  simp [jointSupport]

theorem empty_mem_jointSupport {n : ℕ} (G : Graph n) : [] ∈ jointSupport G := by
  apply (mem_jointSupport G []).2
  exact ⟨(mem_subsets [] (List.finRange n)).2 (List.nil_sublist _), independent_empty G⟩

theorem jointSupport_card_pos {n : ℕ} (G : Graph n) : 0 < (jointSupport G).card :=
  Finset.card_pos.mpr ⟨[], empty_mem_jointSupport G⟩

noncomputable def jointLaw {n : ℕ} (G : Graph n) : FiniteLaw (List (Fin n)) where
  support := jointSupport G
  weight _ := 1 / ((jointSupport G).card : ℝ)
  nonneg _ _ := le_of_lt (one_div_pos.mpr (by exact_mod_cast jointSupport_card_pos G))
  normalized := by
    have hc : ((jointSupport G).card : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (jointSupport_card_pos G))
    simp [hc]

def occupation {n : ℕ} (v : Fin n) (s : List (Fin n)) : ℝ := if v ∈ s then 1 else 0

theorem occupation_nonneg {n : ℕ} (v : Fin n) (s : List (Fin n)) :
    0 ≤ occupation v s := by simp only [occupation]; split <;> norm_num

theorem occupation_le_one {n : ℕ} (v : Fin n) (s : List (Fin n)) :
    occupation v s ≤ 1 := by simp only [occupation]; split <;> norm_num

theorem occupation_idempotent {n : ℕ} (v : Fin n) (s : List (Fin n)) :
    (occupation v s)^2 = occupation v s := by
  simp only [occupation]; split <;> norm_num

theorem adjacent_not_both {n : ℕ} (G : Graph n) (u v : Fin n)
    (huv : G.adj u v = true) (s : List (Fin n)) (hs : s ∈ jointSupport G) :
    occupation u s * occupation v s = 0 := by
  have hind := (independent_iff G s).mp ((mem_jointSupport G s).mp hs).2
  by_cases hu : u ∈ s
  · have hv : v ∉ s := by
      intro hv
      have he := hind u hu v hv
      rw [huv] at he
      cases he
    simp [occupation, hu, hv]
  · simp [occupation, hu]

noncomputable def marginal {n : ℕ} (G : Graph n) (v : Fin n) : ℝ :=
  (jointLaw G).expectation (occupation v)

theorem marginal_bounds {n : ℕ} (G : Graph n) (v : Fin n) :
    0 ≤ marginal G v ∧ marginal G v ≤ 1 := by
  constructor
  · exact (jointLaw G).expectation_nonneg _ (fun s _ => occupation_nonneg v s)
  · have h := (jointLaw G).expectation_mono (occupation v) (fun _ => 1)
      (fun s _ => occupation_le_one v s)
    simpa only [FiniteLaw.expectation_const] using h

theorem occupation_variance {n : ℕ} (G : Graph n) (v : Fin n) :
    (jointLaw G).variance (occupation v) = marginal G v*(1-marginal G v) := by
  rw [FiniteLaw.variance_eq_second_moment]
  have he : (fun s => (occupation v s)^2) = occupation v := by
    funext s
    exact occupation_idempotent v s
  rw [he]
  unfold marginal
  ring

/-- All supported lists are canonical, so their lengths count actual vertices. -/
theorem supported_nodup {n : ℕ} (G : Graph n) (s : List (Fin n))
    (hs : s ∈ jointSupport G) : s.Nodup :=
  ((mem_subsets s (List.finRange n)).mp ((mem_jointSupport G s).mp hs).1).nodup
    (finRange_nodup n)

theorem supported_length_le {n : ℕ} (G : Graph n) (s : List (Fin n))
    (hs : s ∈ jointSupport G) : s.length ≤ n := by
  have h := ((mem_subsets s (List.finRange n)).mp ((mem_jointSupport G s).mp hs).1).length_le
  simpa using h

theorem rank_fiber_card {n : ℕ} (G : Graph n) (r : ℕ) :
    ((jointSupport G).filter (fun s => s.length = r)).card = coefficient G r := by
  have he : (jointSupport G).filter (fun s => s.length = r) =
      (Counting.independentSets G r).toFinset := by
    ext s
    simp only [Finset.mem_filter, mem_jointSupport, List.mem_toFinset,
      Counting.mem_independentSets]
    tauto
  rw [he]
  have hn : (Counting.independentSets G r).Nodup :=
    List.Sublist.nodup List.filter_sublist (vertex_subsets_nodup n)
  rw [List.toFinset_card_of_nodup hn]
  rfl

theorem jointSupport_card_partition {n : ℕ} (G : Graph n) :
    (jointSupport G).card = CardinalityMoments.partition G := by
  have hmap : Set.MapsTo List.length (jointSupport G : Set (List (Fin n)))
      (Finset.range (n+1) : Set ℕ) := by
    intro s hs
    exact Finset.mem_range.mpr (by have h := supported_length_le G s hs; omega)
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  simp only [rank_fiber_card]
  exact (massThrough_eq_sum (coefficient G) n).symm

/-- This is a pointwise pushforward identity, not an assumed distribution match. -/
theorem joint_rank_probability {n : ℕ} (G : Graph n) (r : ℕ) :
    (∑ s ∈ (jointSupport G).filter (fun s => s.length = r), (jointLaw G).weight s) =
      cardinalityProbability G r := by
  simp only [jointLaw, Finset.sum_const, nsmul_eq_mul, rank_fiber_card,
    jointSupport_card_partition, cardinalityProbability, mass]
  ring

theorem joint_rank_expectation {n : ℕ} (G : Graph n) (f : ℕ → ℝ) :
    (jointLaw G).expectation (fun s => f s.length) = (coefficientLaw G).expectation f := by
  have hmap : ∀ s ∈ jointSupport G, s.length ∈ Finset.range (n+1) := by
    intro s hs
    exact Finset.mem_range.mpr (by have h := supported_length_le G s hs; omega)
  unfold FiniteLaw.expectation
  change (∑ s ∈ jointSupport G, (jointLaw G).weight s * f s.length) = _
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  apply Finset.sum_congr rfl
  intro k hk
  calc
    (∑ s ∈ (jointSupport G).filter (fun s => s.length = k),
        (jointLaw G).weight s * f s.length) =
      ∑ s ∈ (jointSupport G).filter (fun s => s.length = k),
        (jointLaw G).weight s * f k := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [(Finset.mem_filter.mp hs).2]
    _ = cardinalityProbability G k * f k := by
      rw [← Finset.sum_mul, joint_rank_probability]

theorem joint_mean {n : ℕ} (G : Graph n) :
    (jointLaw G).expectation (fun s => (s.length : ℝ)) = mean G := by
  rw [joint_rank_expectation, coefficientLaw_mean]

theorem joint_variance {n : ℕ} (G : Graph n) :
    (jointLaw G).variance (fun s => (s.length : ℝ)) = cardinalityVariance G := by
  unfold FiniteLaw.variance
  rw [joint_mean]
  exact joint_rank_expectation G (fun r : ℕ => ((r : ℝ) - mean G) ^ 2)

#print axioms adjacent_not_both
#print axioms occupation_variance
#print axioms supported_nodup
#print axioms jointSupport_card_partition
#print axioms joint_rank_probability
#print axioms joint_mean
#print axioms joint_variance

end Erdos993.Analytic
