import PrefixPartitionCounting
namespace Erdos993.PrefixLocalCounting
open Counting Structure PrefixRootBudget PrefixPartitionCounting
set_option maxHeartbeats 12000000

def higherSubsets {n : Nat} (G : Graph n) (xs : List (Fin n)) : Nat :=
 sumBy (subsets xs) (fun s => if independent G s && decide (2≤s.length) then 1 else 0)

theorem rankCount_independent_zero {n : Nat} (G : Graph n) (xs : List (Fin n)) :
 rankCount (independent G) xs 0=1 := by simp [rankCount_zero,independent_empty]

theorem rankCount_independent_one {n : Nat} (G : Graph n) (xs : List (Fin n)) :
 rankCount (independent G) xs 1=xs.length := by
 induction xs with
 | nil => simp [rankCount,subsets]
 | cons a xs ih =>
   rw [show 1=0+1 from rfl,rankCount_cons_succ,rankCount_zero]
   simp [independent_singleton,ih]

theorem prefix_values_le (a : Nat → Nat) (k : Nat)
 (h : ∀j,j<k → a j≤a (j+1)) : ∀j,j≤k → a j≤a k := by
 induction k with
 | zero =>
   intro j hj
   have he : j=0 := by omega
   simp [he]
 | succ k ih =>
   intro j hj
   by_cases he : j=k+1
   · simp [he]
   · have h1 := ih (by intro t ht; exact h t (by omega)) j (by omega)
     exact Nat.le_trans h1 (h k (by omega))

theorem graded_partition_sum {n : Nat} (G : Graph n) (xs : List (Fin n)) (A B C : Nat) :
 sumBy (subsets xs) (fun s => if independent G s then
   (if s.length=0 then B else if s.length=1 then C else A) else 0)=
 B+xs.length*C+higherSubsets G xs*A := by
 have he := sumBy_congr (subsets xs)
   (fun s => if independent G s then (if s.length=0 then B else if s.length=1 then C else A) else 0)
   (fun s => B*(if s.length=0 then (if independent G s then 1 else 0) else 0)+
     C*(if s.length=1 then (if independent G s then 1 else 0) else 0)+
     A*(if independent G s && decide (2≤s.length) then 1 else 0)) ?_
 · rw [he,sumBy_add,sumBy_add,sumBy_mul_left,sumBy_mul_left,sumBy_mul_left]
   change B*rankCount (independent G) xs 0+C*rankCount (independent G) xs 1+
     A*higherSubsets G xs=_
   rw [rankCount_independent_zero,rankCount_independent_one]
   simp [Nat.mul_comm]
 · intro s hs
   dsimp only
   cases hi : independent G s
   · simp
   · by_cases h0 : s.length=0
     · simp [h0]
     · by_cases h1 : s.length=1
       · simp [h1]
       · have h2 : 2≤s.length := by omega
         simp [h0,h1,h2]

/-- A local block with at most33 independent subsets of size>=2 gives the
 exact three-term upper bound, when the actual complementary coefficients ascend. -/
theorem block_partition_bound {n : Nat} (G : Graph n) (xs ys : List (Fin n))
 (r : Nat) (hr : 2≤r) (hpre : ∀j,j≤r-2 →
   rankCount (independent G) ys j≤rankCount (independent G) ys (r-2)) :
 rankCount (independent G) (xs++ys) r≤rankCount (independent G) ys r+
   xs.length*rankCount (independent G) ys (r-1)+
   higherSubsets G xs*rankCount (independent G) ys (r-2) := by
 have hp := partition_upper G xs ys r
 have hb := sumBy_le (subsets xs)
   (fun s => if independent G s then (if s.length≤r then rankCount (independent G) ys (r-s.length) else 0) else 0)
   (fun s => if independent G s then
     (if s.length=0 then rankCount (independent G) ys r
      else if s.length=1 then rankCount (independent G) ys (r-1)
      else rankCount (independent G) ys (r-2)) else 0) ?_
 · rw [graded_partition_sum] at hb
   exact Nat.le_trans hp hb
 · intro s hs
   dsimp only
   cases hi : independent G s
   · simp
   · simp only [if_true]
     by_cases h0 : s.length=0
     · simp [h0]
     · by_cases h1 : s.length=1
       · simp [h1,show 1≤r by omega]
       · simp only [h0,h1,if_false]
         by_cases hlen : s.length≤r
         · simp only [hlen,if_true]
           exact hpre (r-s.length) (by omega)
         · simp [hlen]

theorem local64_algebra (r A B C F : Int) (hr : 16≤r) (hA : 0≤A)
 (hC : (r-1)*C≤(3*r-1)*A) (hB : r*B≤(3*r-2)*C)
 (hF : F≤B+7*C+33*A) : F≤64*A := by
 have hm0 := Int.mul_nonneg (show 0≤r-16 by omega) (show 0≤r by omega)
 have hm : 0≤r*r-15*r-2 := by grind only
 have hmA := Int.mul_nonneg hm hA
 have hb := Int.mul_le_mul_of_nonneg_left hB (show 0≤r-1 by omega)
 have hc := Int.mul_le_mul_of_nonneg_left hC (show 0≤10*r-2 by omega)
 have hf := Int.mul_le_mul_of_nonneg_left hF
   (Int.mul_nonneg (show 0≤r by omega) (show 0≤r-1 by omega))
 have hh : (r*(r-1))*F≤(r*(r-1))*(64*A) := by grind only
 exact Int.le_of_mul_le_mul_left hh (Int.mul_pos (by omega) (by omega))

theorem block_local64 {n : Nat} (G : Graph n) (xs ys : List (Fin n))
 (r : Nat) (hr : 16≤r) (hn : ys.length+3≤4*r)
 (hxs : xs.length≤7) (hh : higherSubsets G xs≤33)
 (hpre : ∀j,j≤r-2 → rankCount (independent G) ys j≤rankCount (independent G) ys (r-2)) :
 rankCount (independent G) (xs++ys) r≤64*rankCount (independent G) ys (r-2) := by
 have hf := block_partition_bound G xs ys r (by omega) hpre
 have hc := graph_extension_upper_int (inducedOn G ys) (r-2)
 have hb := graph_extension_upper_int (inducedOn G ys) (r-1)
 have he1 : r-2+1=r-1 := by omega
 have he2 : r-1+1=r := by omega
 simp only [coefficient_inducedOn,he1] at hc
 simp only [coefficient_inducedOn,he2] at hb
 have hca : 0≤(rankCount (independent G) ys (r-2):Int) := Int.natCast_nonneg _
 have hcb : 0≤(rankCount (independent G) ys (r-1):Int) := Int.natCast_nonneg _
 have hsz : (ys.length:Int)≤4*(r:Int)-3 := by omega
 have hc1 := Int.mul_le_mul_of_nonneg_right
   (show (ys.length:Int)-(r-2:Int)≤3*(r:Int)-1 by omega) hca
 have hb1 := Int.mul_le_mul_of_nonneg_right
   (show (ys.length:Int)-(r-1:Int)≤3*(r:Int)-2 by omega) hcb
 have ha := local64_algebra (r:Int) (rankCount (independent G) ys (r-2):Int)
   (rankCount (independent G) ys r:Int) (rankCount (independent G) ys (r-1):Int)
   (rankCount (independent G) (xs++ys) r:Int) (by omega) hca ?_ ?_ ?_
 · exact Int.ofNat_le.mp (by simpa using ha)
 · have hcast : ((r-2:Nat):Int)=(r:Int)-2 := by omega
   rw [hcast] at hc
   grind only
 · have hcast : ((r-1:Nat):Int)=(r:Int)-1 := by omega
   rw [hcast] at hb
   grind only
 · have hf0 := Int.ofNat_le.mpr hf
   have hx := Nat.mul_le_mul_right (rankCount (independent G) ys (r-1)) hxs
   have hx2 := Nat.mul_le_mul_right (rankCount (independent G) ys (r-2)) hh
   omega

end Erdos993.PrefixLocalCounting
