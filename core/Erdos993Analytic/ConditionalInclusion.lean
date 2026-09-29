import Erdos993Analytic.ConditionalDeletion

/-! The vertex-present conditional law has the rank distribution of the actual
closed-neighborhood minor, shifted by one. USER compilation required. -/

namespace Erdos993.Analytic
open scoped BigOperators
open Counting Structure LeafBoundary RootingBridgeAudit ForestReturnPhases

def presentSupport {n : ℕ} (G : Graph n) (u : Fin n) : Finset (List (Fin n)) :=
  (jointSupport G).filter (fun s => u ∈ s)

theorem present_rank_incidence {n : ℕ} (G : Graph n) (u : Fin n) (r : ℕ) :
    ((presentSupport G u).filter (fun s => s.length = r)).card = inc G u r := by
  have he : (presentSupport G u).filter (fun s => s.length = r) =
      ((independentSets G r).filter (fun s => s.contains u)).toFinset := by
    ext s
    simp only [presentSupport, Finset.mem_filter, mem_jointSupport,
      List.mem_toFinset, List.mem_filter, mem_independentSets, List.contains_iff_mem]
    tauto
  have hn : ((independentSets G r).filter (fun s => s.contains u)).Nodup :=
    List.Sublist.nodup List.filter_sublist
      (List.Sublist.nodup List.filter_sublist (vertex_subsets_nodup n))
  rw [he, List.toFinset_card_of_nodup hn] <;> rfl

theorem present_rank_card_succ {n : ℕ} (G : Graph n) (u : Fin n) (r : ℕ) :
    ((presentSupport G u).filter (fun s => s.length = r+1)).card =
      coefficient (inducedOn G (closedVertices G u)) r := by
  rw [present_rank_incidence]
  exact VertexIncidence.incidence_closed_deletion G u r

theorem present_rank_zero {n : ℕ} (G : Graph n) (u : Fin n) :
    (presentSupport G u).filter (fun s => s.length = 0) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro s hs
  obtain ⟨hs, hz⟩ := Finset.mem_filter.mp hs
  have hu := (Finset.mem_filter.mp hs).2
  have he : s = [] := List.length_eq_zero_iff.mp hz
  simp [he] at hu

theorem presentSupport_card {n : ℕ} (G : Graph n) (u : Fin n) :
    (presentSupport G u).card =
      CardinalityMoments.partition (inducedOn G (closedVertices G u)) := by
  have hsplit := (jointSupport G).card_filter_add_card_filter_not (fun s => u ∈ s)
  change (presentSupport G u).card + (absentSupport G u).card =
    (jointSupport G).card at hsplit
  rw [absentSupport_card, jointSupport_card_partition] at hsplit
  have hgraph := CardinalityMoments.partition_vertex G u
  omega

theorem presentSupport_nonempty {n : ℕ} (G : Graph n) (u : Fin n) :
    (presentSupport G u).Nonempty := by
  apply Finset.card_pos.mp
  rw [presentSupport_card]
  exact CardinalityMoments.partition_positive _

theorem present_mass {n : ℕ} (G : Graph n) (u : Fin n) :
    (∑ s ∈ presentSupport G u, (jointLaw G).weight s) = inclusionWeight G u := by
  rw [presentSupport, joint_event_mass G (fun s => u ∈ s)]
  change ((presentSupport G u).card : ℝ) / ((jointSupport G).card : ℝ) = _
  rw [presentSupport_card, jointSupport_card_partition] <;> rfl

theorem marginal_eq_inclusionWeight {n : ℕ} (G : Graph n) (u : Fin n) :
    marginal G u = inclusionWeight G u := by
  unfold marginal FiniteLaw.expectation
  simp only [occupation, mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
  exact present_mass G u

noncomputable def presentLaw {n : ℕ} (G : Graph n) (u : Fin n) :
    FiniteLaw (List (Fin n)) :=
  (jointLaw G).condition (fun s => u ∈ s)
    (joint_event_mass_pos G _ (presentSupport_nonempty G u))

theorem presentLaw_weight {n : ℕ} (G : Graph n) (u : Fin n) (s : List (Fin n)) :
    (presentLaw G u).weight s = 1 / mass (inducedOn G (closedVertices G u)) := by
  unfold presentLaw
  rw [joint_condition_weight]
  change 1 / ((presentSupport G u).card : ℝ) = _
  rw [presentSupport_card] <;> rfl

theorem present_rank_probability_succ {n : ℕ} (G : Graph n) (u : Fin n) (r : ℕ) :
    (∑ s ∈ (presentLaw G u).support.filter (fun s => s.length = r+1),
      (presentLaw G u).weight s) =
        cardinalityProbability (inducedOn G (closedVertices G u)) r := by
  simp only [presentLaw_weight, Finset.sum_const, nsmul_eq_mul]
  change (((presentSupport G u).filter (fun s => s.length = r+1)).card : ℝ) *
    (1 / mass (inducedOn G (closedVertices G u))) = _
  rw [present_rank_card_succ]
  unfold cardinalityProbability
  ring

theorem present_rank_probability_zero {n : ℕ} (G : Graph n) (u : Fin n) :
    (∑ s ∈ (presentLaw G u).support.filter (fun s => s.length = 0),
      (presentLaw G u).weight s) = 0 := by
  change (∑ s ∈ (presentSupport G u).filter (fun s => s.length = 0), _) = 0
  rw [present_rank_zero, Finset.sum_empty]

#print axioms presentSupport_card
#print axioms marginal_eq_inclusionWeight
#print axioms present_rank_probability_succ
#print axioms present_rank_probability_zero

end Erdos993.Analytic
