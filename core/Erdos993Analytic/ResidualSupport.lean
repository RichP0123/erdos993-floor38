import Erdos993Analytic.GraphExposure
import WeightedInducedCounting

/-! Actual residual support after an arbitrary occupation observation.
No connectedness, forest, or probabilistic independence premise.
Draft for USER compilation; this is not a sharp analytic bound. -/

namespace Erdos993.Analytic.ResidualSupport
open Counting Structure

def independentSet {n : ℕ} (G : Graph n) (S : Finset (Fin n)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, G.adj u v = false

def canonical {n : ℕ} (S : Finset (Fin n)) : List (Fin n) :=
  (List.finRange n).filter (fun v => decide (v ∈ S))

theorem mem_canonical {n : ℕ} (S : Finset (Fin n)) (v : Fin n) :
    v ∈ canonical S ↔ v ∈ S := by simp [canonical]

theorem canonical_toFinset {n : ℕ} (S : Finset (Fin n)) :
    (canonical S).toFinset = S := by ext v; simp [mem_canonical]

theorem canonical_nodup {n : ℕ} (S : Finset (Fin n)) : (canonical S).Nodup :=
  List.Sublist.nodup List.filter_sublist (finRange_nodup n)

theorem canonical_length {n : ℕ} (S : Finset (Fin n)) :
    (canonical S).length = S.card := by
  have h := List.toFinset_card_of_nodup (canonical_nodup S)
  rw [canonical_toFinset] at h
  exact h.symm

theorem canonical_mem_joint {n : ℕ} (G : Graph n) (S : Finset (Fin n)) :
    canonical S ∈ jointSupport G ↔ independentSet G S := by
  rw [mem_jointSupport]
  have hs : canonical S ∈ subsets (List.finRange n) :=
    (mem_subsets _ _).mpr List.filter_sublist
  simp only [hs, true_and, independent_iff, mem_canonical, independentSet]

theorem supported_independentSet {n : ℕ} (G : Graph n) (s : List (Fin n))
    (hs : s ∈ jointSupport G) : independentSet G s.toFinset := by
  intro u hu v hv
  exact (independent_iff G s).mp ((mem_jointSupport G s).mp hs).2
    u (List.mem_toFinset.mp hu) v (List.mem_toFinset.mp hv)

/-- O is the observed occupied set, B the full observed vertex set. -/
def eligible {n : ℕ} (G : Graph n) (B O : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun v => v ∉ B ∧ ∀ u ∈ O, G.adj v u = false)

theorem mem_eligible {n : ℕ} (G : Graph n) (B O : Finset (Fin n)) (v : Fin n) :
    v ∈ eligible G B O ↔ v ∉ B ∧ ∀ u ∈ O, G.adj v u = false := by
  simp [eligible]

def residualGraph {n : ℕ} (G : Graph n) (B O : Finset (Fin n)) :=
  inducedOn G (canonical (eligible G B O))

theorem residualGraph_isForest {n : ℕ} (G : Graph n) (hf : IsForest G)
    (B O : Finset (Fin n)) : IsForest (residualGraph G B O) :=
  inducedOn_isForest G hf _ (canonical_nodup _)

/-- Exact graph-side residual configurations, with original vertex labels. -/
noncomputable def residualConfigs {n : ℕ} (G : Graph n) (B O : Finset (Fin n)) :
    Finset (Finset (Fin n)) := by
  classical
  exact (eligible G B O).powerset.filter (independentSet G)

theorem mem_residualConfigs {n : ℕ} (G : Graph n) (B O S : Finset (Fin n)) :
    S ∈ residualConfigs G B O ↔ S ⊆ eligible G B O ∧ independentSet G S := by
  classical
  simp [residualConfigs]

theorem residual_union_independent {n : ℕ} (G : Graph n) (B O S : Finset (Fin n))
    (hO : independentSet G O) (hS : S ∈ residualConfigs G B O) :
    independentSet G (O ∪ S) := by
  obtain ⟨hsub, hind⟩ := (mem_residualConfigs G B O S).mp hS
  intro u hu v hv
  rcases Finset.mem_union.mp hu with hu | hu <;>
    rcases Finset.mem_union.mp hv with hv | hv
  · exact hO u hu v hv
  · rw [G.symm u v]
    exact ((mem_eligible G B O v).mp (hsub hv)).2 u hu
  · exact ((mem_eligible G B O u).mp (hsub hu)).2 v hv
  · exact hind u hu v hv

theorem residual_union_exposure {n : ℕ} (G : Graph n) (B O S : Finset (Fin n))
    (hOB : O ⊆ B) (hS : S ∈ residualConfigs G B O) :
    exposure B (canonical (O ∪ S)) = O := by
  have hsub := ((mem_residualConfigs G B O S).mp hS).1
  ext v
  simp only [mem_exposure, mem_canonical, Finset.mem_union]
  constructor
  · rintro ⟨hvB, hvO | hvS⟩
    · exact hvO
    · exact (((mem_eligible G B O v).mp (hsub hvS)).1 hvB).elim
  · intro hvO
    exact ⟨hOB hvO, Or.inl hvO⟩

theorem supported_residual {n : ℕ} (G : Graph n) (B O : Finset (Fin n))
    (s : List (Fin n)) (hs : s ∈ jointSupport G) (he : exposure B s = O) :
    s.toFinset \ B ∈ residualConfigs G B O := by
  apply (mem_residualConfigs G B O _).mpr
  have hind := supported_independentSet G s hs
  constructor
  · intro v hv
    obtain ⟨hvs, hvB⟩ := Finset.mem_sdiff.mp hv
    apply (mem_eligible G B O v).mpr
    refine ⟨hvB, ?_⟩
    intro u hu
    have huE : u ∈ exposure B s := he.symm ▸ hu
    exact hind v hvs u (List.mem_toFinset.mpr ((mem_exposure B s u).mp huE).2)
  · intro u hu v hv
    exact hind u (Finset.mem_sdiff.mp hu).1 v (Finset.mem_sdiff.mp hv).1

theorem supported_reconstruction {n : ℕ} (B O : Finset (Fin n))
    (s : List (Fin n)) (he : exposure B s = O) :
    O ∪ (s.toFinset \ B) = s.toFinset := by
  ext v
  have hv : v ∈ O ↔ v ∈ B ∧ v ∈ s := by
    rw [← he, mem_exposure]
  simp only [Finset.mem_union, Finset.mem_sdiff, List.mem_toFinset, hv]
  tauto

theorem residual_reconstruction {n : ℕ} (G : Graph n) (B O S : Finset (Fin n))
    (hOB : O ⊆ B) (hS : S ∈ residualConfigs G B O) :
    (O ∪ S) \ B = S := by
  have hsub := ((mem_residualConfigs G B O S).mp hS).1
  ext v
  simp only [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨hvO | hvS, hvB⟩
    · exact (hvB (hOB hvO)).elim
    · exact hvS
  · intro hvS
    exact ⟨Or.inr hvS, ((mem_eligible G B O v).mp (hsub hvS)).1⟩

/-- All residual configurations and no others arise from the ACTUAL observed fiber. -/
theorem actual_fiber_image {n : ℕ} (G : Graph n) (B O : Finset (Fin n))
    (hOB : O ⊆ B) (hO : independentSet G O) :
    ((jointSupport G).filter (fun s => exposure B s = O)).image
      (fun s => s.toFinset \ B) = residualConfigs G B O := by
  classical
  ext S
  constructor
  · intro h
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp h
    exact supported_residual G B O s (Finset.mem_filter.mp hs).1 (Finset.mem_filter.mp hs).2
  · intro hS
    apply Finset.mem_image.mpr
    refine ⟨canonical (O ∪ S), Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
    · exact (canonical_mem_joint G _).mpr (residual_union_independent G B O S hO hS)
    · exact residual_union_exposure G B O S hOB hS
    · rw [canonical_toFinset]
      exact residual_reconstruction G B O S hOB hS

#print axioms residualGraph_isForest
#print axioms supported_residual
#print axioms actual_fiber_image

end Erdos993.Analytic.ResidualSupport
