import UniformForestPrefix
namespace Erdos993.PrefixLocal63
open Counting Structure PrefixLocalCounting PrefixSubsetTotals PrefixForkNeighborhood
open PrefixForkPacking PrefixPairIncidence PrefixCenterPairs Overlap
set_option maxHeartbeats 8000000

theorem local63_algebra (r d h A B C F : Int) (hr : 2≤r) (hd : 3≤d)
 (hd7 : d≤7) (hh : h≤33) (hsmall : d≤4 → h≤11) (hA : 0≤A) (hC0 : 0≤C)
 (hC : (r-1)*C≤(3*r-d+2)*A) (hB : r*B≤(3*r-d+1)*C)
 (hF : F≤B+d*C+h*A) : F≤63*A := by
 have hB1 := Int.mul_le_mul_of_nonneg_right (show 3*r-d+1≤3*r by omega) hC0
 have hB2 : r*B≤r*(3*C) := by grind only
 have hB3 := Int.le_of_mul_le_mul_left hB2 (show 0<r by omega)
 by_cases hs : d≤4
 · have hC1 := Int.mul_le_mul_of_nonneg_right (show 3*r-d+2≤5*(r-1) by omega) hA
   have hC2 : (r-1)*C≤(r-1)*(5*A) := by grind only
   have hC3 := Int.le_of_mul_le_mul_left hC2 (show 0<r-1 by omega)
   have hdC := Int.mul_le_mul_of_nonneg_right hs hC0
   have hhA := Int.mul_le_mul_of_nonneg_right (hsmall hs) hA
   omega
 · have hC1 := Int.mul_le_mul_of_nonneg_right (show 3*r-d+2≤3*(r-1) by omega) hA
   have hC2 : (r-1)*C≤(r-1)*(3*A) := by grind only
   have hC3 := Int.le_of_mul_le_mul_left hC2 (show 0<r-1 by omega)
   have hdC := Int.mul_le_mul_of_nonneg_right hd7 hC0
   have hhA := Int.mul_le_mul_of_nonneg_right hh hA
   omega

theorem higher_small_block {n : Nat} (G : Graph n) (xs : List (Fin n))
 (hmin : 3≤xs.length) (hmax : xs.length≤4) : higherSubsets G xs≤11 := by
 have h := totalCount_upper (independent G) xs
 have he := totalCount_high_decomposition G xs
 have hd : xs.length=3 ∨ xs.length=4 := by omega
 rcases hd with hd | hd <;> rw [hd] at h he <;> simp only [Nat.reducePow] at h <;> omega

theorem block_local63 {n : Nat} (G : Graph n) (xs ys : List (Fin n)) (r : Nat)
 (hr : 2≤r) (hn : xs.length+ys.length≤4*r) (hmin : 3≤xs.length)
 (hmax : xs.length≤7) (hh : higherSubsets G xs≤33)
 (hpre : ∀j,j≤r-2 → rankCount (independent G) ys j≤rankCount (independent G) ys (r-2)) :
 rankCount (independent G) (xs++ys) r≤63*rankCount (independent G) ys (r-2) := by
 have hf := block_partition_bound G xs ys r hr hpre
 have hc := graph_extension_upper_int (inducedOn G ys) (r-2)
 have hb := graph_extension_upper_int (inducedOn G ys) (r-1)
 simp only [coefficient_inducedOn,show r-2+1=r-1 by omega] at hc
 simp only [coefficient_inducedOn,show r-1+1=r by omega] at hb
 have hc0 : 0≤(rankCount (independent G) ys (r-1):Int) := Int.natCast_nonneg _
 have ha0 : 0≤(rankCount (independent G) ys (r-2):Int) := Int.natCast_nonneg _
 have hc1 := Int.mul_le_mul_of_nonneg_right
   (show (ys.length:Int)-((r-2:Nat):Int)≤3*(r:Int)-(xs.length:Int)+2 by omega) ha0
 have hb1 := Int.mul_le_mul_of_nonneg_right
   (show (ys.length:Int)-((r-1:Nat):Int)≤3*(r:Int)-(xs.length:Int)+1 by omega) hc0
 have hf' := Int.ofNat_le.mpr hf
 simp only [Int.natCast_add,Int.natCast_mul] at hf'
 have h := local63_algebra (r:Int) xs.length (higherSubsets G xs)
   (rankCount (independent G) ys (r-2)) (rankCount (independent G) ys r)
   (rankCount (independent G) ys (r-1)) (rankCount (independent G) (xs++ys) r)
   (by omega) (by omega) (by omega) (by omega)
   (by intro h; have ht := higher_small_block G xs hmin (by omega); omega)
   ha0 hc0 ?_ ?_ hf'
 · exact Int.ofNat_le.mp h
 · have he : ((r-2:Nat):Int)+1=(r:Int)-1 := by omega
   rw [he] at hc
   exact Int.le_trans hc hc1
 · have he : ((r-1:Nat):Int)+1=(r:Int) := by omega
   rw [he] at hb
   exact Int.le_trans hb hb1

theorem forest_pair_local63 {n : Nat} (G : Graph n) (hf : IsForest G) (u w c : Fin n)
 (hne : u≠w) (hu : G.adj u c=true) (hw : G.adj w c=true)
 (hdu : degree G u≤3) (hdw : degree G w≤3) (r : Nat) (hr : 2≤r) (hn : n≤4*r)
 (hpre : ∀j,j≤r-2 → coefficient (inducedOn G (pairClosedVertices G u w)) j≤
   coefficient (inducedOn G (pairClosedVertices G u w)) (r-2)) :
 coefficient G r≤63*pairInc G u w r := by
 have huw := NeighborTools.forest_no_triangle G hf u c w hu (by rw [G.symm]; exact hw) hne
 have hsum := closedBlock_lengths G u w
 have hmin := closedBlock_ge_three G u w c hne hu hw
 have hmax := closedBlock_le_seven G u w c hu hw hdu hdw
 have h33 := closedBlock_higher_le33 G u w c hne huw hu hw hdu hdw
 have hb := block_local63 G (closedBlock G u w) (pairClosedVertices G u w) r hr
   (by omega) hmin hmax h33 (by intro j hj; simpa [coefficient_inducedOn] using hpre j hj)
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

theorem packing_pair_distinct {n : Nat} (G : Graph n) (ps : List (Fork n))
 (hp : Packing G ps) (p : Fork n) (hm : p∈ps) : p.left≠p.right := by
 have hsub : [p.left,p.right].Sublist (endpoints ps) := by
   clear hp
   induction ps with
   | nil => simp at hm
   | cons q qs ih =>
     rcases List.mem_cons.mp hm with hh | ht
     · subst p
       exact (List.nil_sublist (endpoints qs)).cons_cons q.right |>.cons_cons q.left
     · exact (ih ht).cons q.right |>.cons q.left
 simpa using hsub.nodup hp.nodup

theorem center_budget_of_pair_counts {n : Nat} (G : Graph n) (r C : Nat)
 (h : ∀c,∀p∈pairUp c (lowNeighbors G c),
   coefficient G r≤C*pairInc G p.left p.right r) :
 pairBudget G*coefficient G r≤C*overlap G r := by
 have hc (c : Fin n) : (lowNeighbors G c).length/2*coefficient G r≤
     C*sumBy (pairUp c (lowNeighbors G c)) (fun p => pairInc G p.left p.right r) := by
   have hh := sumBy_le (pairUp c (lowNeighbors G c)) (fun _ => coefficient G r)
     (fun p => C*pairInc G p.left p.right r)
     (by intro p hp; exact h c p hp)
   rw [sumBy_const,PrefixRootBudget.sumBy_mul_left,pairUp_length] at hh
   simpa [Nat.mul_comm] using hh
 have hh := sumBy_le (List.finRange n) _ _ (by intro c hm; exact hc c)
 rw [PrefixRootBudget.sumBy_mul_left] at hh
 have he := PrefixRootBudget.sumBy_mul_left (List.finRange n)
   (fun c => (lowNeighbors G c).length/2) (coefficient G r)
 have hl : sumBy (List.finRange n) (fun c => (lowNeighbors G c).length/2*coefficient G r)=
   pairBudget G*coefficient G r := by
   simpa [Nat.mul_comm,pairBudget] using he
 rw [hl] at hh
 exact Nat.le_trans hh (Nat.mul_le_mul_left C (center_pair_overlap G r))

theorem forest_overlap_budget63 {n : Nat} (G : Graph n) (hf : IsForest G)
 (r : Nat) (hr : 2≤r) (hn : n≤4*r)
 (hpre : ∀u w c : Fin n,u≠w → G.adj u c=true → G.adj w c=true →
   degree G u≤3 → degree G w≤3 → ∀j,j≤r-2 →
   coefficient (inducedOn G (pairClosedVertices G u w)) j≤
   coefficient (inducedOn G (pairClosedVertices G u w)) (r-2)) :
 pairBudget G*coefficient G r≤63*Overlap.overlap G r := by
 apply center_budget_of_pair_counts
 intro c p hp
 have hpack := center_packing G c
 have he := packing_pair_distinct G _ hpack p hp
 have ha := hpack.adjacent p hp
 have hd := hpack.low p hp
 have hu : G.adj p.left p.center=true := by rw [G.symm]; exact ha.1
 have hw : G.adj p.right p.center=true := by rw [G.symm]; exact ha.2
 exact forest_pair_local63 G hf _ _ _ he hu hw hd.1 hd.2 r hr hn
   (hpre _ _ _ he hu hw hd.1 hd.2)

end Erdos993.PrefixLocal63
