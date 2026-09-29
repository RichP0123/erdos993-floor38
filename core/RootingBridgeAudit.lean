import ForestLeafStructure

/-! Auditor implementation of the first rooting-bridge seat's counting reduction.
The rooting existence and weighted invariant are not proved here. -/
namespace Erdos993.RootingBridgeAudit
open Counting

def inc {n : Nat} (G : Graph n) (v : Fin n) (r : Nat) : Nat :=
 ((independentSets G r).filter (fun s => s.contains v)).length

theorem sum_inc {n : Nat} (G : Graph n) (r : Nat) :
 sumBy (List.finRange n) (fun v => inc G v r)=r*coefficient G r := by
 have he : (fun v => inc G v r)=
   (fun v => sumBy (independentSets G r) (fun s => if v∈s then 1 else 0)) := by
   funext v
   unfold inc
   rw [←sumBy_indicator]
   simp
 rw [he,sumBy_swap]
 have hh : sumBy (independentSets G r)
     (fun s => sumBy (List.finRange n) (fun v => if v∈s then 1 else 0))=
     sumBy (independentSets G r) (fun _ => r) := by
   apply sumBy_congr
   intro s hs
   have hm := (mem_independentSets G r s).mp hs
   have hn := List.Sublist.nodup ((mem_subsets _ _).mp hm.1) (finRange_nodup n)
   rw [selected_membership_sum s hn,hm.2.1]
 rw [hh,sumBy_const,independentSets_length,Nat.mul_comm]

theorem sum_int_const_bound {α : Type} (xs : List α) (f : α → Nat) (K : Int)
 (h : ∀ v∈xs, 2*(f v:Int)≤K) :
 2*(sumBy xs f:Int)≤(xs.length:Int)*K := by
 induction xs with
 | nil => simp
 | cons v xs ih =>
   have hv := h v (by simp)
   have ht := ih (by intro w hw; exact h w (by simp [hw]))
   simp only [sumBy_cons,List.length_cons,Int.natCast_add,Int.natCast_one]
   grind

/-- A conditional assembly theorem, with the missing per-vertex bound explicit. -/
theorem curvature_bound_of_pointed_bounds {n : Nat} (G : Graph n) (r : Nat)
 (h : ∀ v : Fin n, 2*(inc G v r:Int)≤curvature G r) :
 2*(r:Int)*(coefficient G r:Int)≤(n:Int)*curvature G r := by
 have hh := sum_int_const_bound (List.finRange n) (fun v => inc G v r) (curvature G r)
   (by intro v hv; exact h v)
 rw [sum_inc] at hh
 simpa [Int.natCast_mul,Int.mul_assoc] using hh

#print axioms sum_inc
#print axioms sum_int_const_bound
#print axioms curvature_bound_of_pointed_bounds
end Erdos993.RootingBridgeAudit
