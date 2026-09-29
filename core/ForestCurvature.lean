import FiniteMarkedFamilies
import RootingBridgeAudit

namespace Erdos993.CurvatureProof
open Counting Structure MarkedInjectionAudit ParentConstruction FiniteMarked
set_option maxHeartbeats 8000000

def nonroot {n : Nat} {G : Graph n} (R : ParentCertificate G) (v : Fin n) : Nat :=
 if R.parent v=none then 0 else 1

theorem parent_count {n : Nat} {G : Graph n} (R : ParentCertificate G) (v : Fin n) :
 sumBy (List.finRange n) (fun u => if R.parent v=some u then 1 else 0)=nonroot R v := by
 cases hp : R.parent v with
 | none => simp [nonroot,hp]
 | some a =>
   have he : (fun u : Fin n => if R.parent v=some u then 1 else 0)=
     (fun u => if u=a then 1 else 0) := by funext u; simp [hp,eq_comm]
   rw [hp] at he
   rw [he,sumBy_equal_indicator _ (finRange_nodup n) a]
   simp [nonroot,hp]

theorem degree_partition {n : Nat} {G : Graph n} (R : ParentCertificate G) (v : Fin n) :
 degree G v=(children R v).length+nonroot R v := by
 unfold degree
 rw [←sumBy_indicator]
 have he : sumBy (List.finRange n) (fun u => if G.adj v u then 1 else 0)=
   sumBy (List.finRange n) (fun u =>
     (if R.parent u=some v then 1 else 0)+(if R.parent v=some u then 1 else 0)) := by
   apply sumBy_congr
   intro u hu
   dsimp
   by_cases hc : R.parent u=some v
   · by_cases hp : R.parent v=some u
     · exact False.elim (R.noTwoCycle u v ⟨hc,hp⟩)
     · have ha := (R.edges v u).mpr (Or.inr hc)
       simp [hc,hp,ha]
   · by_cases hp : R.parent v=some u
     · have ha := (R.edges v u).mpr (Or.inl hp)
       simp [hc,hp,ha]
     · have ha : G.adj v u=false := by
         cases h : G.adj v u with
         | false => rfl
         | true => exact False.elim ((R.edges v u).mp h |>.elim hp hc)
       simp [hc,hp,ha]
 rw [he,sumBy_add,parent_count]
 have hc : sumBy (List.finRange n) (fun u => if R.parent u=some v then 1 else 0)=
   (children R v).length := by
   have hh := sumBy_indicator (List.finRange n) (fun u => decide (R.parent u=some v))
   simpa [children] using hh
 rw [hc]

theorem source_length {n : Nat} {G : Graph n} (R : ParentCertificate G) (r : Nat) :
 (sources R r).length=
 sumBy (independentSets G r) (fun s => sumBy s (fun v => (children R v).length)) := by
 unfold sources
 rw [pairs_length]
 apply sumBy_congr
 intro s hs
 exact pairs_length s (children R)

theorem target_length {n : Nat} {G : Graph n} (R : ParentCertificate G) (r : Nat) :
 (targets R r).length=sumBy (independentSets G r) (fun s => sumBy s (nonroot R)) := by
 unfold targets
 rw [pairs_length]
 apply sumBy_congr
 intro s hs
 rw [←sumBy_indicator]
 apply sumBy_congr
 intro v hv
 simp [nonroot]

theorem selected_degree_partition {n : Nat} {G : Graph n} (R : ParentCertificate G) (r : Nat) :
 sumBy (independentSets G r) (selectedDegree G)=
 (sources R r).length+(targets R r).length := by
 rw [source_length,target_length,←sumBy_add]
 apply sumBy_congr
 intro s hs
 unfold selectedDegree
 rw [←sumBy_add]
 apply sumBy_congr
 intro v hv
 exact degree_partition R v

theorem selected_root_budget {n : Nat} {G : Graph n} (R : ParentCertificate G)
 (root : Fin n) (hr : R.parent root=none) (s : List (Fin n)) (hs : s.Nodup) :
 sumBy s (nonroot R)+(if root∈s then 1 else 0)≤s.length := by
 have hh := sumBy_le s
   (fun v => nonroot R v+(if v=root then 1 else 0)) (fun _ => 1) ?_
 · rw [sumBy_add,sumBy_equal_indicator s hs root,sumBy_const] at hh
   simpa using hh
 · intro v hv
   by_cases he : v=root
   · subst v; simp [nonroot,hr]
   · simp only [nonroot,he,if_false,Nat.add_zero]
     split <;> omega

theorem target_plus_root_budget {n : Nat} {G : Graph n} (R : ParentCertificate G)
 (root : Fin n) (hr : R.parent root=none) (r : Nat) :
 (targets R r).length+RootingBridgeAudit.inc G root r≤r*coefficient G r := by
 have hh := sumBy_le (independentSets G r)
   (fun s => sumBy s (nonroot R)+(if root∈s then 1 else 0)) (fun _ => r) ?_
 · have hi : sumBy (independentSets G r) (fun s => if root∈s then 1 else 0)=
       RootingBridgeAudit.inc G root r := by
     have hx := sumBy_indicator (independentSets G r) (fun s => s.contains root)
     simpa [RootingBridgeAudit.inc] using hx
   rw [sumBy_add,←target_length,hi,sumBy_const,independentSets_length] at hh
   simpa [Nat.mul_comm] using hh
 · intro s hs
   have hm := (mem_independentSets G r s).mp hs
   have hn := List.Sublist.nodup ((mem_subsets _ _).mp hm.1) (finRange_nodup n)
   have ht := selected_root_budget R root hr s hn
   simpa [hm.2.1] using ht

/-- The marked injection supplies the actual graph's pointed curvature bound. -/
theorem pointed_curvature {n : Nat} {G : Graph n} (R : ParentCertificate G)
 (root : Fin n) (hr : R.parent root=none) (r : Nat) :
 2*(RootingBridgeAudit.inc G root r:Int)≤curvature G r := by
 have hd := selected_degree_partition R r
 have hi := sources_le_targets R r
 have hb := target_plus_root_budget R root hr r
 have hnat : sumBy (independentSets G r) (selectedDegree G)+
     2*RootingBridgeAudit.inc G root r≤2*(r*coefficient G r) := by omega
 have hh := Int.ofNat_le.mpr hnat
 simp only [Int.natCast_add,Int.natCast_mul] at hh
 unfold curvature
 simp only [Int.mul_assoc]
 omega

/-- Full global-order curvature theorem on the existing finite-graph model.
No parent certificate, weighted invariant or marked-count identity is assumed.
The theorem includes disconnected, empty and unsupported-rank cases. -/
theorem forest_curvature_bound {n : Nat} (G : Graph n) (hf : IsForest G) (r : Nat) :
 2*(r:Int)*(coefficient G r:Int)≤(n:Int)*curvature G r := by
 apply RootingBridgeAudit.curvature_bound_of_pointed_bounds G r
 intro v
 obtain ⟨R,hr⟩ := forest_parent_certificate G hf v
 exact pointed_curvature R v hr r

theorem forest_curvature_nonnegative {n : Nat} (G : Graph n) (hf : IsForest G) (r : Nat) :
 0≤curvature G r := by
 by_cases hn : n=0
 · subst n
   cases r <;> simp [curvature,coefficient,independentSets,subsets,independent,selectedDegree,sumBy]
 · let v : Fin n := ⟨0,by omega⟩
   obtain ⟨R,hr⟩ := forest_parent_certificate G hf v
   have hh := pointed_curvature R v hr r
   have hnat : 0≤(RootingBridgeAudit.inc G v r:Int) := Int.natCast_nonneg _
   omega

/-- Unconditional forest quarter bound at every strict falling rank. -/
theorem forest_first_fall_quarter_bound {n : Nat} (G : Graph n) (hf : IsForest G)
 (r : Nat) (hfall : coefficient G (r+1)<coefficient G r) : n≤4*r :=
 first_fall_quarter_bound G r hfall (forest_curvature_nonnegative G hf r)

theorem critical_quarter_bound (w : Closure.CriticalWitness) : w.n≤4*w.M :=
 forest_first_fall_quarter_bound w.graph w.forest w.M w.firstFall

theorem forest_global_growth {n : Nat} (G : Graph n) (hf : IsForest G) (r : Nat) :
 ((n:Int)*((n:Int)-3*(r:Int))+2*(r:Int))*(coefficient G r:Int)≤
 (n:Int)*((r:Int)+1)*(coefficient G (r+1):Int) := by
 have hh := growth_of_component_curvature G r (n:Int) (Int.natCast_nonneg n)
   (forest_curvature_bound G hf r)
 exact hh

end Erdos993.CurvatureProof
