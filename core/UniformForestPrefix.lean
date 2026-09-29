import PrefixSmallCurvature
namespace Erdos993.UniformForestPrefix
open Counting Structure RootingBridgeAudit PrefixPairDensity PrefixDegreeSums
open PrefixSmallIncidence PrefixSmallCurvature PrefixRootBudget PrefixCenterPairs
open PrefixForkNeighborhood PrefixPairIncidence PrefixLocalCounting Overlap
set_option maxHeartbeats 8000000

theorem mass_assembly (n r A K O M s : Int) (hn : 3≤n) (hM : 0≤M)
 (hc : 2*r*A+(n-2)*M≤n*K) (hs : s*A≤5*M) (ho : n*A≤s*A+640*O) :
 (1280*r+n*n)*A≤640*n*(K+O) := by
 have h1 := Int.mul_le_mul_of_nonneg_left hs (show 0≤n by omega)
 have h2 := Int.mul_le_mul_of_nonneg_right (show 5*n≤640*(n-2) by omega) hM
 have h3 := Int.mul_le_mul_of_nonneg_left hc (show (0:Int)≤640 by omega)
 have h4 := Int.mul_le_mul_of_nonneg_left ho (show 0≤n by omega)
 have he1 : n*(s*A)=(n*s)*A := by grind only
 have he2 : n*(5*M)=5*n*M := by grind only
 have he3 : 640*(n-2)*M=640*((n-2)*M) := by grind only
 rw [he1,he2] at h1
 rw [he3] at h2
 simp only [Int.mul_add] at h3 h4 ⊢
 grind only

theorem prefix_algebra (n r A B K O : Int) (hn : 3≤n) (hr : 0≤r) (hA : 0≤A)
 (hband : n≤4*r) (hdom : 2560*r+320≤641*n)
 (hid : (r+1)*B=(n-3*r)*A+K+O)
 (hm : (1280*r+n*n)*A≤640*n*(K+O)) : A≤B := by
 have hd := Int.mul_nonneg (show 0≤n by omega) (show 0≤641*n-2560*r-320 by omega)
 have he : 0≤640*n*(n-4*r-1)+1280*r+n*n := by grind only
 have hp := Int.mul_nonneg he hA
 have hi := congrArg (fun z => 640*n*z) hid
 have hh : 640*n*(r+1)*A≤640*n*(r+1)*B := by grind only
 exact Int.le_of_mul_le_mul_left hh (by
   have h := Int.mul_pos (show (0:Int)<640 by omega) (show 0<n by omega)
   exact Int.mul_pos h (by omega))

/-- Uniform ascending prefix. All deletion-prefix premises are discharged here
 by strong induction on the actual forest order. -/
theorem forest_prefix {n : Nat} (G : Graph n) (hf : IsForest G) (r : Nat)
 (hdom : 2560*r+320≤641*n) : coefficient G r≤coefficient G (r+1) := by
 induction n using Nat.strongRecOn generalizing r with
 | ind n ih =>
   by_cases hquarter : 4*r<n
   · exact LeafBoundary.forest_prefix_step G hf r hquarter
   have hband : n≤4*r := by omega
   have hn : 320≤n := by omega
   have hr : 80≤r := by omega
   have hp : ∀u w c : Fin n,u≠w → G.adj u c=true → G.adj w c=true →
       degree G u≤3 → degree G w≤3 → ∀j,j≤r-2 →
       coefficient (inducedOn G (pairClosedVertices G u w)) j≤
       coefficient (inducedOn G (pairClosedVertices G u w)) (r-2) := by
     intro u w c hne hu hw hdu hdw
     have hl := closedBlock_lengths G u w
     have hmin := closedBlock_ge_three G u w c hne hu hw
     have hmax := closedBlock_le_seven G u w c hu hw hdu hdw
     have hf' := inducedOn_isForest G hf (pairClosedVertices G u w) (pairClosed_nodup G u w)
     apply prefix_values_le
     intro j hj
     exact ih (pairClosedVertices G u w).length (by omega) _ hf' j (by omega)
   have ho := forest_overlap_budget G hf r (by omega) hband hp
   have hd := forest_pair_density G hf
   have hd' := Nat.mul_le_mul_right (coefficient G r) hd
   have hs := small_mass_lower G r (by omega) hband
   have hc := forest_small_global G hf r
   have hb : n*coefficient G r≤count (small G)*coefficient G r+640*overlap G r := by
     have hh := Nat.mul_le_mul_left 10 ho
     grind only
   have hs' := Int.ofNat_le.mpr hs
   have hb' := Int.ofNat_le.mpr hb
   simp only [Int.natCast_add,Int.natCast_mul] at hs' hb'
   have hm := mass_assembly (n:Int) r (coefficient G r) (curvature G r) (overlap G r)
     (mass (small G) (fun v => inc G v r)) (count (small G)) (by omega)
     (Int.natCast_nonneg _) hc hs' hb'
   have hid := graph_curvature_overlap_identity G r
   have ha := prefix_algebra (n:Int) r (coefficient G r) (coefficient G (r+1))
     (curvature G r) (overlap G r) (by omega) (Int.natCast_nonneg _) (Int.natCast_nonneg _)
     (by omega) (by omega) hid hm
   exact Int.ofNat_le.mp ha

theorem strict_fall_rank_bound {n : Nat} (G : Graph n) (hf : IsForest G) (r : Nat)
 (hfall : coefficient G (r+1)<coefficient G r) : 641*n<2560*r+320 := by
 by_cases hd : 2560*r+320≤641*n
 · have h := forest_prefix G hf r hd
   omega
 · omega

theorem strict_fall_deficit_bound {n : Nat} (G : Graph n) (hf : IsForest G) (r : Nat)
 (hfall : coefficient G (r+1)<coefficient G r) :
 (n:Int)<640*(4*(r:Int)-(n:Int))+320 := by
 have h := strict_fall_rank_bound G hf r hfall
 omega

/-- Applies to the entire order/rank slice, hence also to its pure-two family. -/
theorem four_k_one_fall_cutoff {n : Nat} (G : Graph n) (hf : IsForest G) (k : Nat)
 (hn : n=4*k+1) (hfall : coefficient G (k+2)<coefficient G (k+1)) : k≤559 := by
 have h := strict_fall_rank_bound G hf (k+1) (by simpa [Nat.add_assoc] using hfall)
 omega

theorem critical_deficit_bound (w : Closure.CriticalWitness) :
 (w.n:Int)<640*(4*(w.M:Int)-(w.n:Int))+320 :=
 strict_fall_deficit_bound w.graph w.forest w.M w.firstFall

theorem critical_four_k_one_cutoff (w : Closure.CriticalWitness) (k : Nat)
 (hn : w.n=4*k+1) (hm : w.M=k+1) : k≤559 := by
 apply four_k_one_fall_cutoff w.graph w.forest k hn
 simpa [hm,Nat.add_assoc] using w.firstFall

end Erdos993.UniformForestPrefix
