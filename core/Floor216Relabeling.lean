import Floor216NoHoles

namespace Erdos993.Floor216
open Polynomial
open scoped BigOperators
open Erdos993.Analytic.GeneralActivity Erdos993.Analytic.ResidualSupport
noncomputable section

theorem relabel_configs_mem {n m : ℕ} (G : Graph n) (H : Graph m)
    (f : Fin n ≃ Fin m) (adj : ∀ u v, G.adj u v = H.adj (f u) (f v))
    (U S : Finset (Fin n)) (hS : S ∈ configs G U) :
    S.map f.toEmbedding ∈ configs H (U.map f.toEmbedding) := by
  classical
  obtain ⟨hsub,hind⟩ := (mem_configs G U S).mp hS
  apply (mem_configs H _ _).mpr
  constructor
  · exact Finset.map_subset_map.mpr hsub
  · intro u hu v hv
    obtain ⟨u,huS,rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨v,hvS,rfl⟩ := Finset.mem_map.mp hv
    exact (adj u v).symm.trans (hind u huS v hvS)

/-- Graph relabeling preserves every induced independence polynomial. -/
theorem inducedPolynomial_relabel {n m : ℕ} (G : Graph n) (H : Graph m)
    (f : Fin n ≃ Fin m) (adj : ∀ u v, G.adj u v = H.adj (f u) (f v))
    (U : Finset (Fin n)) : inducedPolynomial G U = inducedPolynomial H (U.map f.toEmbedding) := by
  classical
  unfold inducedPolynomial
  refine Finset.sum_bij (fun S _ => S.map f.toEmbedding) ?_ ?_ ?_ ?_
  · intro S hS
    exact relabel_configs_mem G H f adj U S hS
  · intro S _ T _ he
    exact Finset.map_injective f.toEmbedding he
  · intro T hT
    have ha : ∀ u v, H.adj u v = G.adj (f.symm u) (f.symm v) := by
      intro u v
      simpa using (adj (f.symm u) (f.symm v)).symm
    have hm := relabel_configs_mem H G f.symm ha (U.map f.toEmbedding) T hT
    have hU : (U.map f.toEmbedding).map f.symm.toEmbedding = U := by ext v; simp
    rw [hU] at hm
    refine ⟨T.map f.symm.toEmbedding,hm,?_⟩
    ext v
    simp
  · intro S _
    simp

theorem coefficient_relabel {n m : ℕ} (G : Graph n) (H : Graph m)
    (f : Fin n ≃ Fin m) (adj : ∀ u v, G.adj u v = H.adj (f u) (f v))
    (k : ℕ) : coefficient G k = coefficient H k := by
  classical
  have hp := inducedPolynomial_relabel G H f adj Finset.univ
  have hu : (Finset.univ : Finset (Fin n)).map f.toEmbedding = Finset.univ := by
    ext v
    simp
  rw [hu,inducedPolynomial_univ,inducedPolynomial_univ] at hp
  have hc := congrArg (fun P : QPoly => P.coeff k) hp
  simp only [graphPolynomial_coeff] at hc
  exact_mod_cast hc

theorem isForest_relabel {n m : ℕ} (G : Graph n) (H : Graph m)
    (f : Fin n ≃ Fin m) (adj : ∀ u v, G.adj u v = H.adj (f u) (f v))
    (hf : IsForest G) : IsForest H := by
  intro k v hinj hcycle
  apply hf k (fun i => f.symm (v i))
  · intro i j he
    exact hinj i j (f.symm.injective he)
  · intro i
    simpa only [adj,Equiv.apply_symm_apply] using hcycle i

#print axioms coefficient_relabel
#print axioms isForest_relabel
end
end Erdos993.Floor216
