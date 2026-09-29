import SmallComponentCurvature
namespace Erdos993.TwoLeafPayment
open Counting Structure PaddingCounts CurvatureProof

theorem two_leaf_algebra (k q q1 h x y : Int) (hk : 2≤k) (hq : 0≤q)
 (hback : q≤3*q1) (hpad : q+q1≤h)
 (hb : 2*k*h+2*(4*k-1)*q1≤4*k*x) (hsmall : 3*q≤4*y) : 2*q≤x+y := by
 have h1 := Int.mul_le_mul_of_nonneg_left hpad (show 0≤2*k by omega)
 have h2 := Int.mul_le_mul_of_nonneg_left hback (show 0≤10*k-2 by omega)
 have h3 := Int.mul_le_mul_of_nonneg_left hsmall (show 0≤3*k by omega)
 have h4 := Int.mul_nonneg (show 0≤k-2 by omega) hq
 have ht : (12*k)*(2*q)≤(12*k)*(x+y) := by grind
 exact Int.le_of_mul_le_mul_left ht (by omega)

theorem two_leaf_slope_certificate {nh nq : Nat} (H : Graph nh) (Q : Graph nq)
 (k : Nat) (hk : 2≤k)
 (hn : nh=4*k+1) (hq : nq+1=4*k)
 (hp : coefficient Q k+coefficient Q (k-1)≤coefficient H k)
 (hb : 2*(k:Int)*(coefficient H k:Int)+2*(4*(k:Int)-1)*(coefficient Q (k-1):Int)≤
     4*(k:Int)*curvature H k)
 (hsmall : 3*(coefficient Q k:Int)≤4*curvature Q k) :
 coefficient H k+coefficient Q k≤coefficient H (k+1)+coefficient Q (k+1) := by
 have he := graph_extension_upper_add Q (k-1)
 have hi : k-1+1=k := by omega
 rw [hi] at he
 have hei := Int.ofNat_le.mpr he
 have hki : ((k-1:Nat):Int)=(k:Int)-1 := by omega
 have hnqi : (nq:Int)=4*(k:Int)-1 := by omega
 simp only [Int.natCast_add,Int.natCast_mul,hki,hnqi] at hei
 have hback : (coefficient Q k:Int)≤3*(coefficient Q (k-1):Int) := by
   have ht : (k:Int)*(coefficient Q k:Int)≤(k:Int)*(3*(coefficient Q (k-1):Int)) := by grind
   exact Int.le_of_mul_le_mul_left ht (by omega)
 have hpi := Int.ofNat_le.mpr hp
 simp only [Int.natCast_add] at hpi
 have hbudget := two_leaf_algebra (k:Int) _ _ _ _ _ (by omega) (Int.natCast_nonneg _) hback hpi hb hsmall
 have hg := graph_curvature_growth H k
 have hqg := graph_curvature_growth Q k
 have hnhi : (nh:Int)=4*(k:Int)+1 := by omega
 rw [hnhi] at hg
 rw [hnqi] at hqg
 have ht : ((k:Int)+1)*((coefficient H k:Int)+(coefficient Q k:Int))≤
     ((k:Int)+1)*((coefficient H (k+1):Int)+(coefficient Q (k+1):Int)) := by grind
 have htt := Int.le_of_mul_le_mul_left ht (by omega)
 omega

end Erdos993.TwoLeafPayment
