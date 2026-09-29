import PrefixSubsetTotals
import DegreeNeighborTools
namespace Erdos993.PrefixForkNeighborhood
open Counting Structure LeafBoundary PrefixForkPacking PrefixPairIncidence PrefixLocalCounting PrefixSubsetTotals
set_option maxHeartbeats 12000000

theorem nodup_subset_length_le {n : Nat} (xs ys : List (Fin n))
 (hx : xs.Nodup) (hy : ys.Nodup) (hsub : ∀v∈xs,v∈ys) : xs.length≤ys.length := by
 have h := sumBy_le (List.finRange n) (fun v => if v∈xs then 1 else 0)
   (fun v => if v∈ys then 1 else 0) ?_
 · rw [selected_membership_sum xs hx,selected_membership_sum ys hy] at h
   exact h
 · intro v hv
   by_cases hxv : v∈xs
   · simp [hxv,hsub v hxv]
   · simp [hxv]

def blockPred {n : Nat} (G : Graph n) (u w z : Fin n) : Bool :=
 decide (z=u) || decide (z=w) || G.adj u z || G.adj w z

def closedBlock {n : Nat} (G : Graph n) (u w : Fin n) : List (Fin n) :=
 (List.finRange n).filter (blockPred G u w)

theorem closedBlock_nodup {n : Nat} (G : Graph n) (u w : Fin n) :
 (closedBlock G u w).Nodup := (finRange_nodup n).filter _

theorem closedBlock_mem {n : Nat} (G : Graph n) (u w z : Fin n) :
 z∈closedBlock G u w ↔ z=u ∨ z=w ∨ G.adj u z=true ∨ G.adj w z=true := by
 simp [closedBlock,blockPred,or_assoc]

theorem closedBlock_complement {n : Nat} (G : Graph n) (u w : Fin n) :
 (List.finRange n).filter (fun z => !(blockPred G u w z))=pairClosedVertices G u w := by
 apply sublist_eq_of_members (List.finRange n) _ _ (finRange_nodup n) List.filter_sublist
   (List.filter_sublist.trans (List.erase_sublist.trans List.erase_sublist))
 intro z
 change z∈(List.finRange n).filter (fun z => !(blockPred G u w z)) ↔ z∈pairClosedVertices G u w
 rw [pairClosed_mem]
 simp [blockPred,and_assoc]

theorem closedBlock_lengths {n : Nat} (G : Graph n) (u w : Fin n) :
 (closedBlock G u w).length+(pairClosedVertices G u w).length=n := by
 have h := filter_complement_lengths (List.finRange n) (blockPred G u w)
 rw [closedBlock_complement] at h
 simpa [closedBlock] using h

theorem closedBlock_le_seven {n : Nat} (G : Graph n) (u w c : Fin n)
 (hu : G.adj u c=true) (hw : G.adj w c=true) (hdu : degree G u≤3) (hdw : degree G w≤3) :
 (closedBlock G u w).length≤7 := by
 have h := sumBy_le (List.finRange n)
   (fun z => (if blockPred G u w z then 1 else 0)+(if z=c then 1 else 0))
   (fun z => (if z=u then 1 else 0)+(if z=w then 1 else 0)+
     (if G.adj u z then 1 else 0)+(if G.adj w z then 1 else 0)) ?_
 · simp only [sumBy_add] at h
   rw [sumBy_indicator,sumBy_equal_indicator _ (finRange_nodup n),
     sumBy_equal_indicator _ (finRange_nodup n),sumBy_equal_indicator _ (finRange_nodup n),
     sumBy_indicator,sumBy_indicator] at h
   have ht : (closedBlock G u w).length+1≤2+degree G u+degree G w := by
     simpa [closedBlock,degree] using h
   omega
 · intro z hz
   dsimp only
   by_cases he : z=c
   · subst z
     simp [blockPred,hu,hw]
   · by_cases heu : z=u <;> by_cases hew : z=w <;>
       cases ha : G.adj u z <;> cases hb : G.adj w z <;> simp_all [blockPred]

theorem closedBlock_ge_three {n : Nat} (G : Graph n) (u w c : Fin n)
 (hne : u≠w) (hu : G.adj u c=true) (hw : G.adj w c=true) :
 3≤(closedBlock G u w).length := by
 have huc : u≠c := by intro he; subst c; rw [G.loopless] at hu; contradiction
 have hwc : w≠c := by intro he; subst c; rw [G.loopless] at hw; contradiction
 have h := nodup_subset_length_le [u,w,c] (closedBlock G u w)
   (by simp [hne,huc,hwc]) (closedBlock_nodup G u w) ?_
 · exact h
 · intro z hz
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
   rcases hz with hz | hz | hz <;> subst z <;> simp [closedBlock_mem,hu]

def middleBlock {n : Nat} (G : Graph n) (u w : Fin n) : List (Fin n) :=
 ((closedBlock G u w).erase u).erase w

theorem middleBlock_mem {n : Nat} (G : Graph n) (u w z : Fin n) :
 z∈middleBlock G u w ↔ z≠w ∧ z≠u ∧ z∈closedBlock G u w := by
 rw [middleBlock,List.Nodup.mem_erase_iff ((closedBlock_nodup G u w).erase u),
   List.Nodup.mem_erase_iff (closedBlock_nodup G u w)]

theorem block_two_perm {n : Nat} (G : Graph n) (u w : Fin n) (hne : u≠w) :
 (closedBlock G u w).Perm (u::w::middleBlock G u w) := by
 have hu : u∈closedBlock G u w := by simp [closedBlock_mem]
 have hw : w∈(closedBlock G u w).erase u := by
   rw [List.Nodup.mem_erase_iff (closedBlock_nodup G u w)]
   exact ⟨Ne.symm hne,by simp [closedBlock_mem]⟩
 exact (List.perm_cons_erase hu).trans ((List.perm_cons_erase hw).cons u)

theorem middle_avoiding_le_two {n : Nat} (G : Graph n) (u w c : Fin n)
 (hu : G.adj u c=true) (hw : G.adj w c=true) (hdw : degree G w≤3) :
 ((middleBlock G u w).filter (fun z => !(G.adj u z))).length≤2 := by
 let ns := (List.finRange n).filter (fun z => G.adj w z)
 have hn : ns.Nodup := (finRange_nodup n).filter _
 have hc : c∈ns := by simp [ns,hw]
 have hlen : (ns.erase c).length≤2 := by
   have hh := List.length_erase_of_mem hc
   change ns.length≤3 at hdw
   omega
 have hs := nodup_subset_length_le ((middleBlock G u w).filter (fun z => !(G.adj u z)))
   (ns.erase c) (((closedBlock_nodup G u w).erase u).erase w |>.filter _) (hn.erase c) ?_
 · omega
 · intro z hz
   obtain ⟨hm,hnot⟩ := List.mem_filter.mp hz
   have hm2 := (middleBlock_mem G u w z).mp hm
   have hnot0 : G.adj u z=false := by simpa using hnot
   have hzc : z≠c := by intro he; subst z; rw [hu] at hnot0; contradiction
   have hwz : G.adj w z=true := by
     have hd := (closedBlock_mem G u w z).mp hm2.2.2
     rcases hd with h | h | h | h
     · exact False.elim (hm2.2.1 h)
     · exact False.elim (hm2.1 h)
     · rw [hnot0] at h; contradiction
     · exact h
   exact (List.Nodup.mem_erase_iff hn).mpr ⟨hzc,by simp [ns,hwz]⟩

theorem middleBlock_swap {n : Nat} (G : Graph n) (u w : Fin n) :
 middleBlock G u w=middleBlock G w u := by
 apply sublist_eq_of_members (List.finRange n) _ _ (finRange_nodup n)
   (List.erase_sublist.trans (List.erase_sublist.trans List.filter_sublist))
   (List.erase_sublist.trans (List.erase_sublist.trans List.filter_sublist))
 intro z
 change z∈middleBlock G u w ↔ z∈middleBlock G w u
 simp only [middleBlock_mem,closedBlock_mem]
 grind only

theorem middle_both_empty {n : Nat} (G : Graph n) (u w : Fin n) :
 (middleBlock G u w).filter (fun z => !(G.adj u z) && !(G.adj w z))=[] := by
 cases he : (middleBlock G u w).filter (fun z => !(G.adj u z) && !(G.adj w z)) with
 | nil => rfl
 | cons z zs =>
   have hz : z∈(middleBlock G u w).filter (fun z => !(G.adj u z) && !(G.adj w z)) := by rw [he]; simp
   obtain ⟨hm,hh⟩ := List.mem_filter.mp hz
   have hm2 := (middleBlock_mem G u w z).mp hm
   have hn : G.adj u z=false ∧ G.adj w z=false := by simpa using hh
   have hd := (closedBlock_mem G u w z).mp hm2.2.2
   grind only

theorem pow_two_small (k : Nat) (hk : k≤2) : 2^k≤4 := by
 have hh : k=0 ∨ k=1 ∨ k=2 := by omega
 rcases hh with hh | hh | hh <;> simp [hh]

/-- The33 bound is a four-way set partition, not a finite graph census. -/
theorem closedBlock_higher_le33 {n : Nat} (G : Graph n) (u w c : Fin n)
 (hne : u≠w) (hn : G.adj u w=false) (hu : G.adj u c=true) (hw : G.adj w c=true)
 (hdu : degree G u≤3) (hdw : degree G w≤3) : higherSubsets G (closedBlock G u w)≤33 := by
 let ys := middleBlock G u w
 have hp := block_two_perm G u w hne
 have hlen : (closedBlock G u w).length=ys.length+2 := by
   have h := hp.length_eq
   simp only [List.length_cons] at h
   dsimp only [ys]
   omega
 have hy : ys.length≤5 := by
   have h := closedBlock_le_seven G u w c hu hw hdu hdw
   omega
 have hu2 := middle_avoiding_le_two G u w c hu hw hdw
 have hw2 := middle_avoiding_le_two G w u c hw hu hdu
 rw [←middleBlock_swap G u w] at hw2
 have hpowu := pow_two_small _ hu2
 have hpoww := pow_two_small _ hw2
 have hb := totalCount_upper (independent G) ys
 have hbu := totalCount_upper (independent G) (ys.filter (fun z => !(G.adj u z)))
 have hbw := totalCount_upper (independent G) (ys.filter (fun z => !(G.adj w z)))
 have ht := totalCount_perm hp (independent G) (independent_permInvariant G)
 rw [two_vertex_total G u w _ hn,middle_both_empty] at ht
 have hz : totalCount (independent G) ([]:List (Fin n))=1 := by simp [totalCount,subsets,independent_empty]
 rw [hz] at ht
 have hd := totalCount_high_decomposition G (closedBlock G u w)
 have hm : higherSubsets G (closedBlock G u w)+ys.length≤2^ys.length+6 := by
   rw [hlen] at hd
   dsimp only [ys] at hb hbu hbw hd ⊢
   omega
 have hc : ys.length=0 ∨ ys.length=1 ∨ ys.length=2 ∨ ys.length=3 ∨ ys.length=4 ∨ ys.length=5 := by omega
 rcases hc with hc | hc | hc | hc | hc | hc <;> rw [hc] at hm <;> simp only [Nat.reducePow] at hm <;> omega

/-- Actual local forest estimate. Its residual-prefix premise is discharged
 later by the induction on order; it is not an assumed prefix on this forest. -/
theorem forest_pair_local64 {n : Nat} (G : Graph n) (hf : IsForest G) (u w c : Fin n)
 (hne : u≠w) (hu : G.adj u c=true) (hw : G.adj w c=true)
 (hdu : degree G u≤3) (hdw : degree G w≤3) (r : Nat) (hr : 16≤r) (hn : n≤4*r)
 (hpre : ∀j,j≤r-2 → coefficient (inducedOn G (pairClosedVertices G u w)) j≤
   coefficient (inducedOn G (pairClosedVertices G u w)) (r-2)) :
 coefficient G r≤64*pairInc G u w r := by
 have huw := NeighborTools.forest_no_triangle G hf u c w hu (by rw [G.symm]; exact hw) hne
 have hsum := closedBlock_lengths G u w
 have hmin := closedBlock_ge_three G u w c hne hu hw
 have hmax := closedBlock_le_seven G u w c hu hw hdu hdw
 have h33 := closedBlock_higher_le33 G u w c hne huw hu hw hdu hdw
 have hb := block_local64 G (closedBlock G u w) (pairClosedVertices G u w) r hr
   (by omega) hmax h33 (by intro j hj; simpa [coefficient_inducedOn] using hpre j hj)
 have hp := List.filter_append_perm (blockPred G u w) (List.finRange n)
 rw [closedBlock_complement] at hp
 have he := rankCount_perm hp (independent G) (independent_permInvariant G) r
 change rankCount (independent G) (closedBlock G u w++pairClosedVertices G u w) r=
   rankCount (independent G) (List.finRange n) r at he
 rw [he,rankCount_graph] at hb
 have hi := pairInc_closed_deletion G u w hne huw (r-2)
 rw [show r-2+2=r by omega,coefficient_inducedOn] at hi
 rw [←hi] at hb
 exact hb

end Erdos993.PrefixForkNeighborhood
