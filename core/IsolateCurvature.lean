import QuarterBoundaryExclusion
namespace Erdos993.IsolateCurvature
open Counting Structure CurvatureProof MarkedInjectionAudit ParentConstruction FiniteMarked RootingBridgeAudit

def isolatedInc {n : Nat} (G : Graph n) (p : Fin n → Bool) (r : Nat) : Nat :=
 sumBy (independentSets G r) (fun s => sumBy s (fun u => if p u then 1 else 0))

theorem isolate_parent_none {n : Nat} {G : Graph n} (R : ParentCertificate G) (v : Fin n)
 (hi : ∀u,G.adj v u=false) : R.parent v=none := by
 cases hp : R.parent v with
 | none => rfl
 | some u =>
   have hh := (R.edges v u).mpr (Or.inl hp)
   rw [hi] at hh
   contradiction

theorem isolated_selected_budget {n : Nat} {G : Graph n} (R : ParentCertificate G)
 (p : Fin n → Bool) (hi : ∀u,p u=true → R.parent u=none)
 (v : Fin n) (hv : p v=false) (hr : R.parent v=none)
 (s : List (Fin n)) (hs : s.Nodup) :
 sumBy s (nonroot R)+sumBy s (fun u => if p u then 1 else 0)+(if v∈s then 1 else 0)≤s.length := by
 have hh := sumBy_le s
   (fun u => nonroot R u+(if p u then 1 else 0)+(if u=v then 1 else 0)) (fun _ => 1) ?_
 · rw [sumBy_add,sumBy_add,sumBy_equal_indicator s hs v,sumBy_const] at hh
   simpa using hh
 · intro u hu
   by_cases he : u=v
   · subst u; simp [nonroot,hr,hv]
   · cases hp : p u
     · simp [hp,he,nonroot]; split <;> omega
     · simp [hp,he,nonroot,hi u hp]

theorem pointed_isolated_curvature {n : Nat} (G : Graph n) (hf : IsForest G)
 (p : Fin n → Bool) (hi : ∀u,p u=true → ∀v,G.adj u v=false)
 (v : Fin n) (hv : p v=false) (r : Nat) :
 2*((isolatedInc G p r+inc G v r):Int)≤curvature G r := by
 obtain ⟨R,hr⟩ := forest_parent_certificate G hf v
 have hb := sumBy_le (independentSets G r)
   (fun s => sumBy s (nonroot R)+sumBy s (fun u => if p u then 1 else 0)+(if v∈s then 1 else 0))
   (fun _ => r) ?_
 · have he : sumBy (independentSets G r) (fun s => if v∈s then 1 else 0)=inc G v r := by
     simpa [inc] using sumBy_indicator (independentSets G r) (fun s => s.contains v)
   rw [sumBy_add,sumBy_add,←target_length,he,sumBy_const,independentSets_length] at hb
   have hd := selected_degree_partition R r
   have hs := sources_le_targets R r
   change (targets R r).length+isolatedInc G p r+inc G v r≤coefficient G r*r at hb
   have hn : sumBy (independentSets G r) (selectedDegree G)+2*(isolatedInc G p r+inc G v r)≤
       2*(r*coefficient G r) := by
     rw [Nat.mul_comm (coefficient G r) r] at hb
     omega
   have hh := Int.ofNat_le.mpr hn
   simp only [Int.natCast_add,Int.natCast_mul] at hh
   unfold curvature
   simp only [Int.mul_assoc]
   omega
 · intro s hs
   have hm := (mem_independentSets G r s).mp hs
   have ht := isolated_selected_budget R p (fun u hu => isolate_parent_none R u (hi u hu)) v hv hr s
     (List.Sublist.nodup ((mem_subsets _ _).mp hm.1) (finRange_nodup n))
   simpa [hm.2.1] using ht

theorem sum_inc_filter {n : Nat} (G : Graph n) (p : Fin n → Bool) (r : Nat) :
 sumBy ((List.finRange n).filter p) (fun v => inc G v r)=isolatedInc G p r := by
 have he : (fun v => inc G v r)=
     (fun v => sumBy (independentSets G r) (fun s => if v∈s then 1 else 0)) := by
   funext v
   unfold inc
   rw [←sumBy_indicator]
   simp
 rw [he,sumBy_swap]
 unfold isolatedInc
 apply sumBy_congr
 intro s hs
 have hm := (mem_independentSets G r s).mp hs
 have hc := canonical_sublist (List.finRange n) s (finRange_nodup n) ((mem_subsets _ _).mp hm.1)
 have hb : sumBy ((List.finRange n).filter p) (fun v => if v∈s then 1 else 0)=
     (((List.finRange n).filter p).filter (fun v => decide (v∈s))).length := by
   simpa using sumBy_indicator ((List.finRange n).filter p) (fun v => decide (v∈s))
 have hf : ((List.finRange n).filter p).filter (fun v => decide (v∈s))=
     ((List.finRange n).filter (fun v => decide (v∈s))).filter p := by
   simp only [List.filter_filter]
   apply List.filter_congr
   intro v hv
   exact Bool.and_comm _ _
 rw [hb,hf,hc,sumBy_indicator]

theorem isolated_inc_partition {n : Nat} (G : Graph n) (p : Fin n → Bool) (r : Nat) :
 isolatedInc G p r+isolatedInc G (fun u => !(p u)) r=r*coefficient G r := by
 rw [←sum_inc_filter,←sum_inc_filter]
 have hh : sumBy ((List.finRange n).filter p) (fun v => inc G v r)+
     sumBy ((List.finRange n).filter (fun u => !(p u))) (fun v => inc G v r)=
     sumBy (List.finRange n) (fun v => inc G v r) := by
   rw [sumBy_filter,sumBy_filter,←sumBy_add]
   apply sumBy_congr
   intro v hv
   cases p v <;> simp
 rw [hh,sum_inc]

/-- Isolate-sensitive global curvature, with the remaining order as denominator.
 The statement avoids division and covers an empty non-isolate part. -/
theorem forest_isolate_curvature {n : Nat} (G : Graph n) (hf : IsForest G)
 (p : Fin n → Bool) (hi : ∀u,p u=true → ∀v,G.adj u v=false) (r : Nat) :
 2*(r:Int)*(coefficient G r:Int)+
   2*((((List.finRange n).filter (fun u => !(p u))).length:Int)-1)*(isolatedInc G p r:Int)≤
 (((List.finRange n).filter (fun u => !(p u))).length:Int)*curvature G r := by
 have hh := sum_int_const_bound ((List.finRange n).filter (fun u => !(p u)))
   (fun v => isolatedInc G p r+inc G v r) (curvature G r) ?_
 · rw [sumBy_add,sumBy_const,sum_inc_filter] at hh
   have hp := isolated_inc_partition G p r
   have hpi := congrArg (fun x : Nat => (x:Int)) hp
   simp only [Int.natCast_add,Int.natCast_mul] at hh hpi
   grind
 · intro v hv
   have hp : p v=false := by simpa using (List.mem_filter.mp hv).2
   exact pointed_isolated_curvature G hf p hi v hp r

end Erdos993.IsolateCurvature
