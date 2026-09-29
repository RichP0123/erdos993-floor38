import LeafIncidenceBounds
namespace Erdos993.InteriorRootSlope
open Counting Structure RootingBridgeAudit CurvatureProof ParentConstruction

theorem split_curvature_budget (k h q x y : Int) (hk : 1≤k) (hq : 0≤q)
 (hh : q≤h) (hx : 2*k*h≤(4*k+1)*x) (hy : 2*k*q≤(4*k-1)*y) : q≤x+y := by
 have hc := Int.mul_le_mul_of_nonneg_left hh (show 0≤2*k by omega)
 have h1 := Int.mul_le_mul_of_nonneg_left (show 2*k*q≤(4*k+1)*x by omega) (show 0≤4*k-1 by omega)
 have h2 := Int.mul_le_mul_of_nonneg_left hy (show 0≤4*k+1 by omega)
 have hh : ((4*k+1)*(4*k-1))*q≤((4*k+1)*(4*k-1))*(x+y) := by grind
 exact Int.le_of_mul_le_mul_left hh (Int.mul_pos (by omega) (by omega))

theorem low_curvature_budget (k h q x y : Int) (hk : 1≤k) (hq : 0≤q)
 (hh : 5*q≤4*h) (hx : 2*k*h≤(4*k+1)*x) (hy : 2*k*q≤4*k*y) : q≤x+y := by
 have h1 := Int.mul_le_mul_of_nonneg_left hx (show 0≤(4:Int) by omega)
 have h2 := Int.mul_le_mul_of_nonneg_left hh (show 0≤2*k by omega)
 have h3 := Int.mul_nonneg (show 0≤k-1 by omega) hq
 have h4 : (2*(4*k+1))*q≤(2*(4*k+1))*(2*x) := by grind
 have h5 : q≤2*x := Int.le_of_mul_le_mul_left h4 (by omega)
 have h6 : (2*k)*q≤(2*k)*(2*y) := by grind
 have h7 : q≤2*y := Int.le_of_mul_le_mul_left h6 (by omega)
 omega

/-- At order 4k+1, the sum of the rank-k slopes of a forest and any
 one-vertex deletion is nonnegative. This is an actual graph theorem. -/
theorem forest_root_slope {n : Nat} (G : Graph n) (hf : IsForest G)
 (v : Fin n) (k : Nat) (hk : 1≤k) (hn : n=4*k+1) :
 coefficient G k+coefficient (deleteVertex G v) k≤
 coefficient G (k+1)+coefficient (deleteVertex G v) (k+1) := by
 classical
 have hc := forest_curvature_bound G hf k
 have hd := forest_curvature_bound (deleteVertex G v) (deleteVertex_isForest G hf v) k
 have hi := VertexIncidence.incidence_deletion_partition G v k
 have horder : ((deleteVertices v).length:Int)=4*(k:Int) := by
   rw [deleteVertices_length]; omega
 have hni : (n:Int)=4*(k:Int)+1 := by omega
 have hc' : 2*(k:Int)*(coefficient G k:Int)≤(4*(k:Int)+1)*curvature G k := by
   rw [hni] at hc; exact hc
 have hd' : 2*(k:Int)*(coefficient (deleteVertex G v) k:Int)≤
     4*(k:Int)*curvature (deleteVertex G v) k := by
   rw [horder] at hd; exact hd
 have hb : (coefficient (deleteVertex G v) k:Int)≤curvature G k+curvature (deleteVertex G v) k := by
   by_cases he : ∃u w,G.adj v u=true ∧ G.adj v w=true ∧ u≠w
   · obtain ⟨u,w,hu,hw,huw⟩ := he
     have huv : u≠v := by intro h; subst u; rw [G.loopless] at hu; contradiction
     have hwv : w≠v := by intro h; subst w; rw [G.loopless] at hw; contradiction
     let iu := oldIndex v u huv
     let iw := oldIndex v w hwv
     have hiu : embed v iu=u := embed_oldIndex v u huv
     have hiw : embed v iw=w := embed_oldIndex v w hwv
     have ht := DeletionSeparation.deletion_cut_curvature G hf v iu iw
       (by rw [hiu]; exact hu) (by rw [hiw]; exact hw)
       (by intro h; exact huw (hiu.symm.trans ((congrArg (embed v) h).trans hiw))) k
     rw [horder] at ht
     exact split_curvature_budget (k:Int) _ _ _ _ (by omega) (Int.natCast_nonneg _)
       (by omega) hc' ht
   · have hl : ∀u w,G.adj v u=true → G.adj v w=true → u=w := by
       intro u w hu hw
       by_cases hh : u=w
       · exact hh
       · exact False.elim (he ⟨u,w,hu,hw,hh⟩)
     have ht := LeafIncidence.low_degree_quarter_ratio G v k hk hn hl
     have hti := Int.ofNat_le.mpr ht
     exact low_curvature_budget (k:Int) _ _ _ _ (by omega) (Int.natCast_nonneg _)
       (by simpa only [Int.natCast_mul] using hti) hc' hd'
 have hg := graph_curvature_growth G k
 have hq := graph_curvature_growth (deleteVertex G v) k
 rw [hni] at hg
 rw [horder] at hq
 have hh : ((k:Int)+1)*((coefficient G k:Int)+(coefficient (deleteVertex G v) k:Int))≤
     ((k:Int)+1)*((coefficient G (k+1):Int)+(coefficient (deleteVertex G v) (k+1):Int)) := by grind
 have ht := Int.le_of_mul_le_mul_left hh (by omega)
 omega

end Erdos993.InteriorRootSlope
