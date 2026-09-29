import LeafAttachment
import RootedSecondGradientGoal
namespace Erdos993.AttachmentCounting
open Counting LeafAttachment SecondGradient

theorem independent_old {n : Nat} (G : Graph n) (v : Fin n) (s : List (Fin n)) :
 independent (attachLeaf G v) (s.map Fin.succ)=independent G s := by
 simp [independent,List.all_map,attachLeaf,Function.comp_def]

theorem all_not_decide {n : Nat} (v : Fin n) (s : List (Fin n)) :
 s.all (fun u => !(decide (u=v)))= !(s.contains v) := by
 have he : (fun u : Fin n => !(decide (u=v)))=(fun u => u != v) := by
   funext u
   by_cases hu : u=v <;> simp [hu,bne]
 rw [he,VertexIncidence.all_avoid]

theorem independent_new {n : Nat} (G : Graph n) (v : Fin n) (s : List (Fin n)) :
 independent (attachLeaf G v) (0::s.map Fin.succ)=(independent G s && !(s.contains v)) := by
 rw [independent_cons_bool,independent_old,List.all_map]
 change (independent G s && s.all (fun u => !(decide (u=v))))=_
 rw [all_not_decide]

/-- Exact weighted partition of canonical independent lists after attachment.
 Arbitrary natural weights permit count, incidence and degree specializations. -/
theorem attachment_weighted_partition {n : Nat} (G : Graph n) (v : Fin n) (r : Nat)
 (f : List (Fin (n+1)) → Nat) :
 sumBy (independentSets (attachLeaf G v) (r+1)) f=
 sumBy (independentSets G (r+1)) (fun s => f (s.map Fin.succ))+
 sumBy (avoidingSets G v r) (fun s => f (0::s.map Fin.succ)) := by
 unfold avoidingSets independentSets
 simp only [sumBy_filter]
 rw [List.finRange_succ,subsets,subsets_map,sumBy_append,sumBy_map,sumBy_map]
 congr 1
 · apply sumBy_congr
   intro s hs
   simp [List.length_map,independent_old]
 · rw [sumBy_map]
   apply sumBy_congr
   intro s hs
   simp only [List.length_cons,List.length_map,Nat.add_right_cancel_iff,independent_new]
   by_cases hr : s.length=r <;> cases independent G s <;> cases s.contains v <;> simp [hr]

theorem degree_selected_old {n : Nat} (G : Graph n) (v : Fin n)
 (s : List (Fin n)) (hs : s.Nodup) :
 selectedDegree (attachLeaf G v) (s.map Fin.succ)=selectedDegree G s+(if v∈s then 1 else 0) := by
 unfold selectedDegree
 rw [sumBy_map]
 have he : (fun u => degree (attachLeaf G v) u.succ)=
     (fun u => degree G u+(if u=v then 1 else 0)) := by funext u; exact degree_old G v u
 rw [he,sumBy_add,sumBy_equal_indicator s hs v]

theorem degree_selected_new {n : Nat} (G : Graph n) (v : Fin n)
 (s : List (Fin n)) (hs : s.Nodup) (hv : v∉s) :
 selectedDegree (attachLeaf G v) (0::s.map Fin.succ)=1+selectedDegree G s := by
 change degree (attachLeaf G v) 0+selectedDegree (attachLeaf G v) (s.map Fin.succ)=_
 rw [degree_new,degree_selected_old G v s hs]
 simp [hv]

theorem attachment_coefficient {n : Nat} (G : Graph n) (v : Fin n) (r : Nat) :
 coefficient (attachLeaf G v) (r+1)=coefficient G (r+1)+(avoidingSets G v r).length := by
 have h := attachment_weighted_partition G v r (fun _ => 1)
 simpa [sumBy_const,independentSets_length] using h

theorem attachment_incidence {n : Nat} (G : Graph n) (v : Fin n) (r : Nat) :
 RootingBridgeAudit.inc (attachLeaf G v) 0 (r+1)=(avoidingSets G v r).length := by
 have h := attachment_weighted_partition G v r (fun s => if s.contains 0 then 1 else 0)
 rw [sumBy_indicator] at h
 simpa [RootingBridgeAudit.inc,List.contains_eq_mem,sumBy_const,sumBy_zero] using h

theorem attachment_degree_sum {n : Nat} (G : Graph n) (v : Fin n) (r : Nat) :
 sumBy (independentSets (attachLeaf G v) (r+1)) (selectedDegree (attachLeaf G v))=
 sumBy (independentSets G (r+1)) (selectedDegree G)+RootingBridgeAudit.inc G v (r+1)+
 (avoidingSets G v r).length+sumBy (avoidingSets G v r) (selectedDegree G) := by
 rw [attachment_weighted_partition]
 have ho : sumBy (independentSets G (r+1))
     (fun s => selectedDegree (attachLeaf G v) (s.map Fin.succ))=
     sumBy (independentSets G (r+1)) (fun s => selectedDegree G s+(if s.contains v then 1 else 0)) := by
   apply sumBy_congr
   intro s hs
   have hn := List.Sublist.nodup ((mem_subsets _ _).mp ((mem_independentSets G (r+1) s).mp hs).1) (finRange_nodup n)
   simpa using degree_selected_old G v s hn
 have hn : sumBy (avoidingSets G v r)
     (fun s => selectedDegree (attachLeaf G v) (0::s.map Fin.succ))=
     sumBy (avoidingSets G v r) (fun s => 1+selectedDegree G s) := by
   apply sumBy_congr
   intro s hs
   have hm := List.mem_filter.mp hs
   have hd := List.Sublist.nodup ((mem_subsets _ _).mp ((mem_independentSets G r s).mp hm.1).1) (finRange_nodup n)
   have hv : v∉s := by simpa using hm.2
   exact degree_selected_new G v s hd hv
 rw [ho,hn,sumBy_add,sumBy_add,sumBy_indicator,sumBy_const]
 change _+RootingBridgeAudit.inc G v (r+1)+(_*1+_)=_
 omega

/-- The second rooted gradient is pointed curvature on a one-leaf extension,
 rooted at the new leaf. No second branch invariant is assumed. -/
theorem forest_second_gradient {n : Nat} (G : Graph n) (hf : IsForest G)
 (v : Fin n) (r : Nat) :
 (RootingBridgeAudit.inc G v (r+1):Int)+((avoidingSets G v r).length:Int)≤
 curvature G (r+1)+avoidingCurvature G v r := by
 have h := attached_pointed_curvature G hf v (r+1)
 rw [attachment_incidence] at h
 unfold curvature at h
 rw [attachment_coefficient,attachment_degree_sum] at h
 unfold curvature avoidingCurvature
 simp only [Int.natCast_add,Int.natCast_one,Int.mul_add,Int.add_mul,Int.mul_one] at h ⊢
 omega

theorem rooted_second_gradient_verified : RootedSecondGradient := by
 intro n G hf v r
 exact forest_second_gradient G hf v r

end Erdos993.AttachmentCounting
