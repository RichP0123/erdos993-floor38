import ForestCore.Graph
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Sort

/-!
The original list-based coefficient counts exactly Mathlib's finite independent
sets. This bridge uses no rooted catalogue, certificate data, or floor bound.
-/

namespace Erdos993.ForestCore

theorem independent_iff_isIndepSet {n : ℕ} (G : Erdos993.Graph n)
    (s : List (Fin n)) :
    independent G s = true ↔ (toSimpleGraph G).IsIndepSet (s.toFinset : Set (Fin n)) := by
  rw [independent_iff]
  constructor
  · intro h u hu v hv _
    change ¬G.adj u v = true
    have huv := h u (by simpa using hu) v (by simpa using hv)
    simp [huv]
  · intro h u hu v hv
    by_cases huv : u = v
    · subst v
      exact G.loopless u
    · have hn := h (by simpa using hu) (by simpa using hv) huv
      change ¬G.adj u v = true at hn
      cases hval : G.adj u v <;> simp_all

private theorem canonical_sublist_injective {n : ℕ} {s t : List (Fin n)}
    (hs : s ∈ subsets (List.finRange n))
    (ht : t ∈ subsets (List.finRange n))
    (hst : s.toFinset = t.toFinset) : s = t := by
  have hss := (List.sortedLT_finRange n).pairwise.sublist ((mem_subsets _ _).mp hs)
  have htt := (List.sortedLT_finRange n).pairwise.sublist ((mem_subsets _ _).mp ht)
  apply hss.eq_of_mem_iff htt
  intro x
  have hx : x ∈ s.toFinset ↔ x ∈ t.toFinset := by rw [hst]
  simpa using hx

/-- The original coefficient is the number of independent `r`-vertex finsets
in the corresponding Mathlib graph. This is valid for every graph, not only forests. -/
theorem coefficient_eq_card_indepSetFinset {n : ℕ} (G : Erdos993.Graph n) (r : ℕ) :
    coefficient G r = ((toSimpleGraph G).indepSetFinset r).card := by
  classical
  let candidates := (subsets (List.finRange n)).filter
    (fun s => decide (s.length = r) && independent G s)
  have hcandidates : candidates.Nodup := (vertex_subsets_nodup n).filter _
  have hmem (s : List (Fin n)) :
      s ∈ candidates.toFinset ↔
      s ∈ subsets (List.finRange n) ∧ s.length = r ∧ independent G s = true := by
    simp [candidates, Bool.and_eq_true]
  change candidates.length = _
  rw [← List.toFinset_card_of_nodup hcandidates]
  apply Finset.card_bij (fun s _ => s.toFinset)
  · intro s hs
    obtain ⟨hsub, hlen, hind⟩ := (hmem s).mp hs
    apply SimpleGraph.mem_indepSetFinset_iff.mpr
    refine ⟨(independent_iff_isIndepSet G s).mp hind, ?_⟩
    have hnodup : s.Nodup := (finRange_nodup n).sublist ((mem_subsets _ _).mp hsub)
    exact (List.toFinset_card_of_nodup hnodup).trans hlen
  · intro s hs t ht heq
    exact canonical_sublist_injective ((hmem s).mp hs).1 ((hmem t).mp ht).1 heq
  · intro s hs
    have hind := SimpleGraph.mem_indepSetFinset_iff.mp hs
    let vertices := (List.finRange n).filter (fun x => decide (x ∈ s))
    have hsub : vertices.Sublist (List.finRange n) := List.filter_sublist
    have hvertices : vertices.toFinset = s := by
      ext x
      simp [vertices]
    have hnodup : vertices.Nodup := (finRange_nodup n).sublist hsub
    have hlen : vertices.length = r := by
      rw [← List.toFinset_card_of_nodup hnodup, hvertices]
      exact hind.card_eq
    have hi : independent G vertices = true := by
      apply (independent_iff_isIndepSet G vertices).mpr
      simpa [hvertices] using hind.isIndepSet
    refine ⟨vertices, (hmem vertices).mpr ⟨(mem_subsets _ _).mpr hsub, hlen, hi⟩, hvertices⟩

#print axioms independent_iff_isIndepSet
#print axioms coefficient_eq_card_indepSetFinset

end Erdos993.ForestCore
