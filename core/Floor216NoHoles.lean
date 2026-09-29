import Floor216ConvolutionClosure

namespace Erdos993.Floor216
open Polynomial
open Erdos993.Analytic.GeneralActivity Erdos993.Analytic.ResidualSupport
open Erdos993.Counting Erdos993.Structure
noncomputable section

theorem coefficient_pos_iff {n : ℕ} (G : Graph n) (k : ℕ) :
    0 < coefficient G k ↔ ∃ s ∈ subsets (List.finRange n),
      s.length = k ∧ independent G s = true := by
  simp [coefficient, List.length_pos_iff_exists_mem]

/-- Taking a subset of an independent set proves all smaller ranks occur. -/
theorem coefficient_positive_downward {n : ℕ} (G : Graph n) (i j : ℕ)
    (hij : i ≤ j) (hj : 0 < coefficient G j) : 0 < coefficient G i := by
  obtain ⟨s,hs,hsize,hind⟩ := (coefficient_pos_iff G j).mp hj
  apply (coefficient_pos_iff G i).mpr
  refine ⟨s.take i, (mem_subsets _ _).mpr ((List.take_sublist i s).trans ((mem_subsets _ _).mp hs)), ?_, ?_⟩
  · simp [List.length_take, hsize, Nat.min_eq_left hij]
  · apply (independent_iff G _).mpr
    intro u hu v hv
    exact (independent_iff G s).mp hind u ((List.take_sublist i s).subset hu)
      v ((List.take_sublist i s).subset hv)

theorem actual_graph_no_holes {n : ℕ} (G : Graph n) :
    NoHoles (intCoeff (graphPolynomial G)) := by
  intro a b c hab hbc ha hc
  have ha0 : 0 ≤ a := by
    by_contra h
    simp [intCoeff,h] at ha
  have hb0 : 0 ≤ b := le_trans ha0 hab
  have hc0 : 0 ≤ c := le_trans hb0 hbc
  have hcn : 0 < coefficient G c.toNat := by
    simpa [intCoeff, hc0, graphPolynomial_coeff] using hc
  have hbn := coefficient_positive_downward G b.toNat c.toNat (Int.toNat_le_toNat hbc) hcn
  simpa [intCoeff, hb0, graphPolynomial_coeff] using hbn

theorem actual_graph_lc_convolution_closed {n a b : ℕ}
    (G : Graph n) (H : Graph a) (K : Graph b)
    (identity : graphPolynomial G = graphPolynomial H * graphPolynomial K)
    (hu : Unimodal (coefficient H))
    (hlc : LogConcave (intCoeff (graphPolynomial K))) : Unimodal (coefficient G) :=
  actual_graph_lc_convolution G H K identity hu (actual_graph_no_holes K) hlc

theorem inducedPolynomial_univ {n : ℕ} (G : Graph n) :
    inducedPolynomial G Finset.univ = graphPolynomial G := by
  ext k
  rw [inducedPolynomial_coeff, graphPolynomial_coeff]
  congr 1
  rw [coefficient_inducedOn, VertexIncidence.rankCount_as_filter]
  simp [canonical, coefficient]

/-- A genuine disjoint graph union preserves unimodality when one factor is LC.
Both the coefficient product identity and no-hole property are discharged. -/
theorem separated_union_lc_unimodal {n : ℕ} (G : Graph n)
    (U V : Finset (Fin n)) (dis : Disjoint U V) (sep : Separated G U V)
    (hu : Unimodal (coefficient (inducedOn G (canonical U))))
    (hlc : LogConcave (intCoeff (graphPolynomial (inducedOn G (canonical V))))) :
    Unimodal (coefficient (inducedOn G (canonical (U ∪ V)))) := by
  apply actual_graph_lc_convolution_closed _ _ _ _ hu hlc
  simp only [← inducedPolynomial_eq_actual]
  exact inducedPolynomial_union G U V dis sep

theorem whole_graph_lc_split {n : ℕ} (G : Graph n)
    (U V : Finset (Fin n)) (dis : Disjoint U V) (sep : Separated G U V)
    (cover : U ∪ V = Finset.univ)
    (hu : Unimodal (coefficient (inducedOn G (canonical U))))
    (hlc : LogConcave (intCoeff (graphPolynomial (inducedOn G (canonical V))))) :
    Unimodal (coefficient G) := by
  apply actual_graph_lc_convolution_closed G _ _ _ hu hlc
  rw [← inducedPolynomial_eq_actual, ← inducedPolynomial_eq_actual,
    ← inducedPolynomial_union G U V dis sep, cover, inducedPolynomial_univ]

#print axioms actual_graph_no_holes
#print axioms whole_graph_lc_split
end
end Erdos993.Floor216
