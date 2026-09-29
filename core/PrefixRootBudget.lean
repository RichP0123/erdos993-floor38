import SeparatedRootCurvature
namespace Erdos993.PrefixRootBudget
open Counting CurvatureProof RootingBridgeAudit MarkedInjectionAudit ParentConstruction FiniteMarked
set_option maxHeartbeats 8000000

def roots {n : Nat} {G : Graph n} (R : ParentCertificate G) : List (Fin n) :=
 (List.finRange n).filter (fun v => decide (R.parent v=none))

theorem sumBy_mul_left {α : Type} (xs : List α) (f : α → Nat) (c : Nat) :
 sumBy xs (fun x => c*f x)=c*sumBy xs f := by
 induction xs with
 | nil => simp
 | cons x xs ih => simp only [sumBy_cons,ih,Nat.mul_add]

theorem sumBy_sub_of_le {α : Type} (xs : List α) (f g : α → Nat)
 (h : ∀x∈xs,g x≤f x) : sumBy xs (fun x => f x-g x)+sumBy xs g=sumBy xs f := by
 induction xs with
 | nil => simp
 | cons x xs ih =>
   have hx := h x (by simp)
   have ht := ih (by intro y hy; exact h y (by simp [hy]))
   simp only [sumBy_cons]
   omega

theorem roots_nonroot_sum {n : Nat} {G : Graph n} (R : ParentCertificate G) :
 (roots R).length+sumBy (List.finRange n) (nonroot R)=n := by
 have h := sumBy_congr (List.finRange n)
   (fun v => (if R.parent v=none then 1 else 0)+nonroot R v) (fun _ => 1) ?_
 · rw [sumBy_add,sumBy_const] at h
   have hr : sumBy (List.finRange n) (fun v => if R.parent v=none then 1 else 0)=
     (roots R).length := by
     simpa [roots] using sumBy_indicator (List.finRange n) (fun v => decide (R.parent v=none))
   simpa [hr] using h
 · intro v hv
   simp only [nonroot]
   split <;> simp_all

theorem children_total {n : Nat} {G : Graph n} (R : ParentCertificate G) :
 sumBy (List.finRange n) (fun v => (children R v).length)=
 sumBy (List.finRange n) (nonroot R) := by
 have he (v : Fin n) : (children R v).length=
   sumBy (List.finRange n) (fun u => if R.parent u=some v then 1 else 0) := by
   simpa [children] using (sumBy_indicator (List.finRange n) (fun u => decide (R.parent u=some v))).symm
 rw [sumBy_congr _ _ _ (by intro v hv; exact he v),sumBy_swap]
 exact sumBy_congr _ _ _ (by intro u hu; exact parent_count R u)

theorem degree_total_with_roots {n : Nat} {G : Graph n} (R : ParentCertificate G) :
 sumBy (List.finRange n) (degree G)+2*(roots R).length=2*n := by
 have hd := sumBy_congr (List.finRange n) (degree G)
   (fun v => (children R v).length+nonroot R v) (by intro v hv; exact degree_partition R v)
 rw [sumBy_add,children_total] at hd
 have hr := roots_nonroot_sum R
 omega

theorem root_membership_sum {n : Nat} {G : Graph n} (R : ParentCertificate G)
 (s : List (Fin n)) (hs : s.Nodup) :
 sumBy (roots R) (fun v => if v∈s then 1 else 0)=
 sumBy s (fun v => if R.parent v=none then 1 else 0) := by
 unfold roots
 rw [sumBy_filter]
 have hi (v : Fin n) : (if R.parent v=none then (if v∈s then 1 else 0) else 0)=
   sumBy s (fun u => if u=v then (if R.parent u=none then 1 else 0) else 0) := by
   rw [sumBy_congr s _ (fun u => (if u=v then 1 else 0)*(if R.parent v=none then 1 else 0)) ?_]
   · by_cases hv : R.parent v=none
     · simp only [hv,if_true,Nat.mul_one]
       exact (sumBy_equal_indicator s hs v).symm
     · simp [hv]
   · intro u hu
     by_cases he : u=v <;> simp_all
 have he := sumBy_congr (List.finRange n)
   (fun v => if decide (R.parent v=none) then (if v∈s then 1 else 0) else 0)
   (fun v => sumBy s (fun u => if u=v then (if R.parent u=none then 1 else 0) else 0))
   (by intro v hv; simpa using hi v)
 rw [he,sumBy_swap]
 apply sumBy_congr
 intro u hu
 by_cases hp : R.parent u=none
 · simpa [hp,eq_comm] using sumBy_equal_indicator (List.finRange n) (finRange_nodup n) u
 · simp [hp]

/-- Simultaneous pointed curvature at all roots of one actual forest certificate. -/
theorem all_roots_curvature {n : Nat} {G : Graph n} (R : ParentCertificate G) (r : Nat) :
 2*(sumBy (roots R) (fun v => inc G v r):Int)≤curvature G r := by
 have hb := sumBy_le (independentSets G r)
   (fun s => sumBy s (nonroot R)+sumBy (roots R) (fun v => if v∈s then 1 else 0))
   (fun _ => r) ?_
 · have hi (v : Fin n) : sumBy (independentSets G r) (fun s => if v∈s then 1 else 0)=inc G v r := by
     simpa [inc] using sumBy_indicator (independentSets G r) (fun s => s.contains v)
   rw [sumBy_add,←target_length,sumBy_swap,
     sumBy_congr _ _ _ (by intro v hv; exact hi v),sumBy_const,independentSets_length] at hb
   have hd := selected_degree_partition R r
   have hj := sources_le_targets R r
   have hn : sumBy (independentSets G r) (selectedDegree G)+
     2*sumBy (roots R) (fun v => inc G v r)≤2*(r*coefficient G r) := by
     rw [Nat.mul_comm (coefficient G r) r] at hb
     omega
   have hz := Int.ofNat_le.mpr hn
   simp only [Int.natCast_add,Int.natCast_mul] at hz
   unfold curvature
   simp only [Int.mul_assoc]
   omega
 · intro s hs
   dsimp only
   have hm := (mem_independentSets G r s).mp hs
   have hn := List.Sublist.nodup ((mem_subsets _ _).mp hm.1) (finRange_nodup n)
   rw [root_membership_sum R s hn,←sumBy_add]
   have he := sumBy_congr s
     (fun v => nonroot R v+(if R.parent v=none then 1 else 0)) (fun _ => 1) ?_
   · rw [he,sumBy_const,hm.2.1]; simp
   · intro v hv
     simp only [nonroot]
     split <;> simp_all

end Erdos993.PrefixRootBudget
