import PrefixForkNeighborhood
namespace Erdos993.PrefixCenterPairs
open Counting Structure PrefixForkPacking PrefixForkNeighborhood Overlap
set_option maxHeartbeats 8000000

def pairUp {n : Nat} (c : Fin n) : List (Fin n) → List (Fork n)
 | [] => []
 | [_] => []
 | a::b::xs => ⟨a,b,c⟩::pairUp c xs

theorem pairUp_length {n : Nat} (c : Fin n) (xs : List (Fin n)) :
 (pairUp c xs).length=xs.length/2 := by
 match xs with
 | [] => simp [pairUp]
 | [a] => simp [pairUp]
 | a::b::xs =>
   have h := pairUp_length c xs
   simp only [pairUp,List.length_cons,h]
   omega

theorem pairUp_sublist {n : Nat} (c : Fin n) (xs : List (Fin n)) :
 (endpoints (pairUp c xs)).Sublist xs := by
 match xs with
 | [] => simp [pairUp,endpoints]
 | [a] => simp [pairUp,endpoints]
 | a::b::xs =>
   exact (pairUp_sublist c xs).cons_cons b |>.cons_cons a

theorem pairUp_members {n : Nat} (c : Fin n) (xs : List (Fin n)) :
 ∀p∈pairUp c xs,p.center=c ∧ p.left∈xs ∧ p.right∈xs := by
 match xs with
 | [] => simp [pairUp]
 | [a] => simp [pairUp]
 | a::b::xs =>
   intro p hp
   rcases List.mem_cons.mp hp with he | ht
   · subst p; simp
   · obtain ⟨hc,hl,hr⟩ := pairUp_members c xs p ht
     exact ⟨hc,by simp [hl],by simp [hr]⟩

def lowNeighbors {n : Nat} (G : Graph n) (c : Fin n) : List (Fin n) :=
 (List.finRange n).filter (fun u => G.adj c u && decide (degree G u≤3))

theorem lowNeighbors_mem {n : Nat} (G : Graph n) (c u : Fin n) :
 u∈lowNeighbors G c ↔ G.adj c u=true ∧ degree G u≤3 := by
 simp [lowNeighbors]

theorem center_packing {n : Nat} (G : Graph n) (c : Fin n) :
 Packing G (pairUp c (lowNeighbors G c)) := by
 refine ⟨?_,?_,?_⟩
 · exact (pairUp_sublist c _).nodup ((finRange_nodup n).filter _)
 · intro p hp
   obtain ⟨hc,hl,hr⟩ := pairUp_members c _ p hp
   rw [hc]
   exact ⟨((lowNeighbors_mem G c _).mp hl).1,((lowNeighbors_mem G c _).mp hr).1⟩
 · intro p hp
   obtain ⟨_,hl,hr⟩ := pairUp_members c _ p hp
   exact ⟨((lowNeighbors_mem G c _).mp hl).2,((lowNeighbors_mem G c _).mp hr).2⟩

theorem center_pair_overlap {n : Nat} (G : Graph n) (r : Nat) :
 sumBy (List.finRange n) (fun c => sumBy (pairUp c (lowNeighbors G c))
   (fun p => pairInc G p.left p.right r))≤overlap G r := by
 have h := sumBy_le (independentSets G r)
   (fun s => sumBy (List.finRange n) (fun c =>
     sumBy (pairUp c (lowNeighbors G c)) (selectedAt s c))) (overlapSet G) ?_
 · rw [sumBy_swap] at h
   have he (c : Fin n) :
     sumBy (independentSets G r) (fun s =>
       sumBy (pairUp c (lowNeighbors G c)) (selectedAt s c))=
     sumBy (pairUp c (lowNeighbors G c)) (fun p => pairInc G p.left p.right r) := by
     rw [sumBy_swap]
     apply sumBy_congr
     intro p hp
     have hc := (pairUp_members c _ p hp).1
     apply sumBy_congr
     intro s hs
     simp [selectedAt,hc]
   rw [sumBy_congr _ _ _ (by intro c hc; exact he c)] at h
   exact h
 · intro s hs
   have hm := (mem_independentSets G r s).mp hs
   have hn := ((mem_subsets _ _).mp hm.1).nodup (finRange_nodup n)
   exact sumBy_le _ _ _ (by intro c hc; exact packing_overlap_at G _ (center_packing G c) s hn c)

def pairBudget {n : Nat} (G : Graph n) : Nat :=
 sumBy (List.finRange n) (fun c => (lowNeighbors G c).length/2)

/-- All local counting estimates sum on the actual forest. -/
theorem forest_overlap_budget {n : Nat} (G : Graph n) (hf : IsForest G)
 (r : Nat) (hr : 16≤r) (hn : n≤4*r)
 (hpre : ∀u w c : Fin n,u≠w → G.adj u c=true → G.adj w c=true →
   degree G u≤3 → degree G w≤3 → ∀j,j≤r-2 →
   coefficient (inducedOn G (PrefixPairIncidence.pairClosedVertices G u w)) j≤
   coefficient (inducedOn G (PrefixPairIncidence.pairClosedVertices G u w)) (r-2)) :
 pairBudget G*coefficient G r≤64*overlap G r := by
 have hc (c : Fin n) : (lowNeighbors G c).length/2*coefficient G r≤
   64*sumBy (pairUp c (lowNeighbors G c)) (fun p => pairInc G p.left p.right r) := by
   have hp := center_packing G c
   have hh := sumBy_le (pairUp c (lowNeighbors G c)) (fun _ => coefficient G r)
     (fun p => 64*pairInc G p.left p.right r) ?_
   · rw [sumBy_const,PrefixRootBudget.sumBy_mul_left,pairUp_length] at hh
     simpa [Nat.mul_comm] using hh
   · intro p hm
     have hd := hp.low p hm
     have ha := hp.adjacent p hm
     have he : p.left≠p.right := by
       have hsub : [p.left,p.right].Sublist (endpoints (pairUp c (lowNeighbors G c))) := by
         clear hp hd ha
         generalize pairUp c (lowNeighbors G c)=ps at hm ⊢
         induction ps with
         | nil => simp at hm
         | cons q qs ih =>
           rcases List.mem_cons.mp hm with hh | ht
           · subst p; exact (List.nil_sublist (endpoints qs)).cons_cons q.right |>.cons_cons q.left
           · exact (ih ht).cons q.right |>.cons q.left
       simpa using hsub.nodup hp.nodup
     have hu : G.adj p.left p.center=true := by rw [G.symm]; exact ha.1
     have hw : G.adj p.right p.center=true := by rw [G.symm]; exact ha.2
     exact forest_pair_local64 G hf _ _ _ he hu hw hd.1 hd.2 r hr hn
       (hpre _ _ _ he hu hw hd.1 hd.2)
 have hh := sumBy_le (List.finRange n) _ _ (by intro c hm; exact hc c)
 rw [PrefixRootBudget.sumBy_mul_left] at hh
 have he := PrefixRootBudget.sumBy_mul_left (List.finRange n)
   (fun c => (lowNeighbors G c).length/2) (coefficient G r)
 have hl : sumBy (List.finRange n) (fun c => (lowNeighbors G c).length/2*coefficient G r)=
   pairBudget G*coefficient G r := by
   simpa [Nat.mul_comm,pairBudget] using he
 rw [hl] at hh
 exact Nat.le_trans hh (Nat.mul_le_mul_left 64 (center_pair_overlap G r))

end Erdos993.PrefixCenterPairs
