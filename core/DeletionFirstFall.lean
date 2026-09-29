import LeafReturnDepth

namespace Erdos993.DeletionFirstFall
open Counting Structure LeafBoundary LeafPhases ForestReturnPhases

/-- First strict falling departure, including the final drop to zero.
 This is not an arbitrarily chosen mode on a plateau. -/
def FirstFall (a : Nat → Nat) (r : Nat) : Prop :=
 a (r+1)<a r ∧ ∀ i, i<r → a i≤a (i+1)

theorem graph_first_fall_exists {n : Nat} (G : Graph n) :
 ∃ r, FirstFall (coefficient G) r := by
 obtain ⟨z,hz,hmin⟩ := Foundation.least_witness
   (fun z => coefficient G z=0)
   ⟨n+1,coefficient_above_order G (by omega)⟩
 have h0 := Extraction.coefficient_zero G
 have hp : 1≤z := by
   by_cases he : z=0
   · subst z; omega
   · omega
 have hprev : 0<coefficient G (z-1) := by
   have hh := hmin (z-1) (by omega)
   omega
 have hf : coefficient G ((z-1)+1)<coefficient G (z-1) := by
   have he : z-1+1=z := by omega
   rw [he,hz]
   exact hprev
 obtain ⟨r,hr,hrmin⟩ := Foundation.least_witness
   (fun r => coefficient G (r+1)<coefficient G r) ⟨z-1,hf⟩
 refine ⟨r,hr,?_⟩
 intro i hi
 have hh := hrmin i hi
 omega

theorem fall_after_first (a : Nat → Nat) (i r : Nat)
 (hi : FirstFall a i) (hr : a (r+1)<a r) : i≤r := by
 by_cases h : i≤r
 · exact h
 · have hh := hi.2 r (by omega); omega

theorem rise_before_first (a : Nat → Nat) (ua : Unimodal a) (i r : Nat)
 (hi : FirstFall a i) (hr : a r<a (r+1)) : r<i := by
 by_cases h : r<i
 · exact h
 · have hh := unimodal_tail_of_fall a ua i hi.1 r (by omega); omega

/-- The two actual deletion sequences must have first falls on opposite
 sides of the entire fall/return interval, after shifting the second by one. -/
theorem separation (f d e : Nat → Nat) (M b i j : Nat)
 (hM : 1≤M) (hb : M<b)
 (rec : ∀ r, f (r+1)=d (r+1)+e r)
 (fall : f (M+1)<f M) (rise : f b<f (b+1))
 (ud : Unimodal d) (ue : Unimodal e)
 (di : FirstFall d i) (ej : FirstFall e j) :
 (i≤M ∧ b<j+1) ∨ (j+1≤M ∧ b<i) := by
 have hm : M-1+1=M := by omega
 have hbi : b-1+1=b := by omega
 rcases partition f d e M b hM hb rec fall rise ud ue with hp | hq
 · have h1 := fall_after_first d i M di hp.1
   have he : e (b-1)<e ((b-1)+1) := by rw [hbi]; exact hp.2
   have h2 := rise_before_first e ue j (b-1) ej he
   exact Or.inl ⟨h1,by omega⟩
 · have he : e ((M-1)+1)<e (M-1) := by rw [hm]; exact hq.1
   have h1 := fall_after_first e j (M-1) ej he
   have h2 := rise_before_first d ud i b di hq.2
   exact Or.inr ⟨by omega,h2⟩

theorem critical_separation (w : Closure.CriticalWitness) (v : Fin w.n)
 (i j : Nat)
 (di : FirstFall (coefficient (deleteVertex w.graph v)) i)
 (ej : FirstFall (coefficient (inducedOn w.graph (closedVertices w.graph v))) j) :
 (i≤w.M ∧ w.b<j+1) ∨ (j+1≤w.M ∧ w.b<i) := by
 have hv := v.isLt
 have hl := deleteVertices_length v
 have ud := critical_inducedOn_unimodal w (deleteVertices v) (deleteVertices_nodup v) (by omega)
 have he : (closedVertices w.graph v).length≤(deleteVertices v).length := List.length_filter_le _ _
 have ue := critical_inducedOn_unimodal w (closedVertices w.graph v)
   ((deleteVertices_nodup v).filter _) (by omega)
 exact separation _ _ _ _ _ i j w.positiveFallIndex w.returnAfterFall
   (coefficient_vertex_recurrence w.graph v) w.firstFall w.returningRise ud ue di ej

/-- Existential bounded vertex coupling remains a conjectural input.
 i in [j,j+2] means distance at most one from the shifted first fall j+1. -/
def CloseVertex {n : Nat} (G : Graph n) : Prop :=
 ∃ v : Fin n, ∃ i j,
 FirstFall (coefficient (deleteVertex G v)) i ∧
 FirstFall (coefficient (inducedOn G (closedVertices G v))) j ∧
 j≤i ∧ i≤j+2

theorem critical_no_close_vertex (w : Closure.CriticalWitness) : ¬CloseVertex w.graph := by
 rintro ⟨v,i,j,hi,hj,h1,h2⟩
 have h := critical_separation w v i j hi hj
 have hb := w.returnAfterFall
 rcases h with h | h <;> omega

/-- CONDITIONAL global implication only. No proof of the displayed universal
 CloseVertex premise is supplied or assumed as an axiom. -/
theorem target_of_close_vertex
 (close : ∀ n, 0<n → ∀ G : Graph n, IsForest G → CloseVertex G) : Target := by
 apply Classical.byContradiction
 intro ht
 obtain ⟨w⟩ := Extraction.critical_witness_of_not_target ht
 have hn : 0<w.n := by
   have hh := InteriorDegreeTwo.critical_order_above_half w
   omega
 exact critical_no_close_vertex w (close w.n hn w.graph w.forest)

end Erdos993.DeletionFirstFall
