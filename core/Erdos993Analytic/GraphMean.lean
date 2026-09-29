import CardinalityMoments
import Mathlib.Tactic

/-! Actual-graph mean identities. DRAFT: not compiled in this session.
The graph definitions and counting theorems are unchanged vendored sources.
No forest, connectedness, unimodality or analytic premise is needed here. -/

namespace Erdos993.Analytic

open Counting Structure LeafBoundary ForestReturnPhases

noncomputable def mass {n : ℕ} (G : Graph n) : ℝ :=
  CardinalityMoments.partition G

noncomputable def moment {n : ℕ} (G : Graph n) : ℝ :=
  CardinalityMoments.firstMoment G

noncomputable def mean {n : ℕ} (G : Graph n) : ℝ := moment G / mass G

theorem mass_pos {n : ℕ} (G : Graph n) : 0 < mass G := by
  unfold mass
  exact_mod_cast CardinalityMoments.partition_positive G

theorem moment_nonneg {n : ℕ} (G : Graph n) : 0 ≤ moment G := by
  unfold moment
  positivity

theorem mean_nonneg {n : ℕ} (G : Graph n) : 0 ≤ mean G :=
  div_nonneg (moment_nonneg G) (le_of_lt (mass_pos G))

theorem mass_mul_mean {n : ℕ} (G : Graph n) : mass G * mean G = moment G := by
  unfold mean
  field_simp [ne_of_gt (mass_pos G)]

theorem mass_vertex {n : ℕ} (G : Graph n) (u : Fin n) :
    mass G = mass (deleteVertex G u) +
      mass (inducedOn G (closedVertices G u)) := by
  unfold mass
  exact_mod_cast CardinalityMoments.partition_vertex G u

theorem moment_vertex {n : ℕ} (G : Graph n) (u : Fin n) :
    moment G = moment (deleteVertex G u) +
      moment (inducedOn G (closedVertices G u)) +
      mass (inducedOn G (closedVertices G u)) := by
  unfold moment mass
  exact_mod_cast CardinalityMoments.firstMoment_vertex G u

/-- The exact actual-graph mixture, with every spectator retained in the minors.
`mean` is explicitly the normalized first cardinality moment. -/
theorem mean_vertex {n : ℕ} (G : Graph n) (u : Fin n) :
    mean G =
      (mass (deleteVertex G u) * mean (deleteVertex G u) +
        mass (inducedOn G (closedVertices G u)) *
          (1 + mean (inducedOn G (closedVertices G u)))) /
      (mass (deleteVertex G u) + mass (inducedOn G (closedVertices G u))) := by
  apply (eq_div_iff (ne_of_gt (add_pos (mass_pos _) (mass_pos _)))).2
  calc
    mean G * (mass (deleteVertex G u) + mass (inducedOn G (closedVertices G u)))
        = mean G * mass G := by rw [← mass_vertex G u]
    _ = moment G := by simpa [mul_comm] using mass_mul_mean G
    _ = moment (deleteVertex G u) + moment (inducedOn G (closedVertices G u)) +
        mass (inducedOn G (closedVertices G u)) := moment_vertex G u
    _ = _ := by rw [mul_add, mul_one, mass_mul_mean, mass_mul_mean]; ring

noncomputable def inclusionWeight {n : ℕ} (G : Graph n) (u : Fin n) : ℝ :=
  mass (inducedOn G (closedVertices G u)) / mass G

theorem inclusionWeight_pos {n : ℕ} (G : Graph n) (u : Fin n) :
    0 < inclusionWeight G u := div_pos (mass_pos _) (mass_pos G)

theorem inclusionWeight_lt_one {n : ℕ} (G : Graph n) (u : Fin n) :
    inclusionWeight G u < 1 := by
  unfold inclusionWeight
  apply (div_lt_one (mass_pos G)).2
  rw [mass_vertex G u]
  linarith [mass_pos (deleteVertex G u)]

theorem mean_vertex_convex {n : ℕ} (G : Graph n) (u : Fin n) :
    mean G = (1 - inclusionWeight G u) * mean (deleteVertex G u) +
      inclusionWeight G u * (1 + mean (inducedOn G (closedVertices G u))) := by
  rw [mean_vertex G u]
  unfold inclusionWeight
  rw [mass_vertex G u]
  field_simp [ne_of_gt (add_pos (mass_pos (deleteVertex G u))
    (mass_pos (inducedOn G (closedVertices G u))))]
  <;> ring

theorem mean_vertex_between {n : ℕ} (G : Graph n) (u : Fin n) :
    min (mean (deleteVertex G u)) (1 + mean (inducedOn G (closedVertices G u))) ≤ mean G ∧
    mean G ≤ max (mean (deleteVertex G u)) (1 + mean (inducedOn G (closedVertices G u))) := by
  have hp := inclusionWeight_pos G u
  have hp1 := inclusionWeight_lt_one G u
  rw [mean_vertex_convex G u]
  by_cases h : mean (deleteVertex G u) ≤ 1 + mean (inducedOn G (closedVertices G u))
  · rw [min_eq_left h, max_eq_right h]
    have hprod := mul_nonneg (le_of_lt hp) (sub_nonneg.mpr h)
    have hprod' := mul_nonneg (sub_nonneg.mpr (le_of_lt hp1)) (sub_nonneg.mpr h)
    constructor <;> nlinarith
  · have hh : 1 + mean (inducedOn G (closedVertices G u)) ≤ mean (deleteVertex G u) :=
      le_of_lt (lt_of_not_ge h)
    rw [min_eq_right hh, max_eq_left hh]
    have hprod := mul_nonneg (le_of_lt hp) (sub_nonneg.mpr hh)
    have hprod' := mul_nonneg (sub_nonneg.mpr (le_of_lt hp1)) (sub_nonneg.mpr hh)
    constructor <;> nlinarith

#print axioms mean_vertex
#print axioms mean_vertex_convex
#print axioms mean_vertex_between

end Erdos993.Analytic
