import Floor216Acceptance
import Erdos993Analytic.ActivityVertexRecurrence

namespace Erdos993.Floor216
open Polynomial
open scoped BigOperators
open Erdos993.Analytic.GeneralActivity Erdos993.Analytic.ResidualSupport
open Erdos993.Counting Erdos993.Structure
open Classical
noncomputable section

/-- Independence polynomial of an actual vertex-induced subgraph. -/
def inducedPolynomial {n : ℕ} (G : Graph n) (U : Finset (Fin n)) : QPoly :=
  ∑ S ∈ configs G U, X ^ S.card

theorem inducedPolynomial_coeff {n : ℕ} (G : Graph n) (U : Finset (Fin n)) (k : ℕ) :
    (inducedPolynomial G U).coeff k =
      (coefficient (inducedOn G (canonical U)) k : ℚ) := by
  classical
  rw [← configs_rank_card G U k]
  simp [inducedPolynomial, Polynomial.coeff_X_pow, eq_comm]

theorem inducedPolynomial_eq_actual {n : ℕ} (G : Graph n) (U : Finset (Fin n)) :
    inducedPolynomial G U = graphPolynomial (inducedOn G (canonical U)) := by
  ext k
  rw [inducedPolynomial_coeff, graphPolynomial_coeff]

theorem inducedPolynomial_powerset {n : ℕ} (G : Graph n) (U : Finset (Fin n)) :
    inducedPolynomial G U = ∑ S ∈ U.powerset, if independentSet G S then X^S.card else 0 := by
  classical
  exact Finset.sum_filter _ _

/-- Actual-graph vertex deletion formula, with no assumed coefficient identity. -/
theorem inducedPolynomial_insert {n : ℕ} (G : Graph n) (U : Finset (Fin n))
    (v : Fin n) (hv : v ∉ U) :
    inducedPolynomial G (insert v U) = inducedPolynomial G U +
      X * inducedPolynomial G (U.filter (fun u => G.adj v u = false)) := by
  classical
  rw [inducedPolynomial_powerset, Finset.sum_powerset_insert hv, ← inducedPolynomial_powerset]
  congr 1
  unfold inducedPolynomial
  rw [filtered_configs, Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  have hvS : v ∉ S := fun h => hv ((Finset.mem_powerset.mp hS) h)
  rw [independent_insert, Finset.card_insert_of_notMem hvS, pow_succ]
  split <;> simp_all [mul_comm]

def Separated {n : ℕ} (G : Graph n) (U V : Finset (Fin n)) : Prop :=
  ∀ u ∈ U, ∀ v ∈ V, G.adj u v = false

theorem independent_union_of_separated {n : ℕ} (G : Graph n) (U V S T : Finset (Fin n))
    (sep : Separated G U V) (hs : S ⊆ U) (ht : T ⊆ V)
    (hindS : independentSet G S) (hindT : independentSet G T) :
    independentSet G (S ∪ T) := by
  intro u hu v hv
  rcases Finset.mem_union.mp hu with hu | hu <;> rcases Finset.mem_union.mp hv with hv | hv
  · exact hindS u hu v hv
  · exact sep u (hs hu) v (ht hv)
  · rw [G.symm]
    exact sep v (hs hv) u (ht hu)
  · exact hindT u hu v hv

theorem union_pair_injective {α : Type*} [DecidableEq α] (U V : Finset α)
    (dis : Disjoint U V) (S T S' T' : Finset α)
    (hs : S ⊆ U) (ht : T ⊆ V) (hs' : S' ⊆ U) (ht' : T' ⊆ V)
    (he : S ∪ T = S' ∪ T') : S = S' ∧ T = T' := by
  have left_eq : S = S' := by
    ext x
    constructor
    · intro hx
      have hu : x ∈ S' ∪ T' := he ▸ Finset.mem_union_left T hx
      rcases Finset.mem_union.mp hu with h | h
      · exact h
      · exact False.elim (Finset.disjoint_left.mp dis (hs hx) (ht' h))
    · intro hx
      have hu : x ∈ S ∪ T := he.symm ▸ Finset.mem_union_left T' hx
      rcases Finset.mem_union.mp hu with h | h
      · exact h
      · exact False.elim (Finset.disjoint_left.mp dis (hs' hx) (ht h))
  have right_eq : T = T' := by
    ext x
    constructor
    · intro hx
      have hu : x ∈ S' ∪ T' := he ▸ Finset.mem_union_right S hx
      rcases Finset.mem_union.mp hu with h | h
      · exact False.elim (Finset.disjoint_left.mp dis (hs' h) (ht hx))
      · exact h
    · intro hx
      have hu : x ∈ S ∪ T := he.symm ▸ Finset.mem_union_right S' hx
      rcases Finset.mem_union.mp hu with h | h
      · exact False.elim (Finset.disjoint_left.mp dis (hs h) (ht' hx))
      · exact h
  exact ⟨left_eq,right_eq⟩

/-- Independence polynomials multiply across actual disjoint separated sets. -/
theorem inducedPolynomial_union {n : ℕ} (G : Graph n) (U V : Finset (Fin n))
    (dis : Disjoint U V) (sep : Separated G U V) :
    inducedPolynomial G (U ∪ V) = inducedPolynomial G U * inducedPolynomial G V := by
  classical
  symm
  calc
    inducedPolynomial G U * inducedPolynomial G V =
        ∑ pair ∈ configs G U ×ˢ configs G V, (X : QPoly)^(pair.1.card+pair.2.card) := by
      simp only [inducedPolynomial, Finset.sum_product, Finset.sum_mul, Finset.mul_sum, pow_add]
      exact Finset.sum_comm
    _ = inducedPolynomial G (U ∪ V) := by
      unfold inducedPolynomial
      refine Finset.sum_bij (fun pair _ => pair.1 ∪ pair.2) ?_ ?_ ?_ ?_
      · intro pair hp
        obtain ⟨hS,hT⟩ := Finset.mem_product.mp hp
        obtain ⟨hs,hiS⟩ := (mem_configs G U pair.1).mp hS
        obtain ⟨ht,hiT⟩ := (mem_configs G V pair.2).mp hT
        exact (mem_configs G (U ∪ V) _).mpr
          ⟨Finset.union_subset_union hs ht, independent_union_of_separated G U V _ _ sep hs ht hiS hiT⟩
      · intro pair hp other ho he
        obtain ⟨hS,hT⟩ := Finset.mem_product.mp hp
        obtain ⟨hS',hT'⟩ := Finset.mem_product.mp ho
        have h := union_pair_injective U V dis pair.1 pair.2 other.1 other.2
          ((mem_configs G U _).mp hS).1 ((mem_configs G V _).mp hT).1
          ((mem_configs G U _).mp hS').1 ((mem_configs G V _).mp hT').1 he
        exact Prod.ext h.1 h.2
      · intro S hS
        obtain ⟨hs,hi⟩ := (mem_configs G (U ∪ V) S).mp hS
        refine ⟨(S ∩ U, S ∩ V), Finset.mem_product.mpr ⟨?_,?_⟩, ?_⟩
        · exact (mem_configs G U _).mpr ⟨Finset.inter_subset_right,
            fun u hu v hv => hi u (Finset.mem_inter.mp hu).1 v (Finset.mem_inter.mp hv).1⟩
        · exact (mem_configs G V _).mpr ⟨Finset.inter_subset_right,
            fun u hu v hv => hi u (Finset.mem_inter.mp hu).1 v (Finset.mem_inter.mp hv).1⟩
        · exact (Finset.inter_union_distrib_left S U V).symm.trans (Finset.inter_eq_left.mpr hs)
      · intro pair hp
        obtain ⟨hS,hT⟩ := Finset.mem_product.mp hp
        have hd := dis.mono ((mem_configs G U _).mp hS).1 ((mem_configs G V _).mp hT).1
        rw [Finset.card_union_of_disjoint hd]

#print axioms inducedPolynomial_coeff
#print axioms inducedPolynomial_insert
#print axioms inducedPolynomial_union
end
end Erdos993.Floor216
