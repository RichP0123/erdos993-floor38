import InteriorIsolateAlgebra
namespace Erdos993.InteriorPadding
open Counting Structure PaddingCounts CurvatureProof

/-- A numerical certificate fed by actual isolate-count and curvature
 identities. Its explicit premises are discharged by the end-support wrapper. -/
theorem interior_padding_certificate {nh nq : Nat} (H : Graph nh) (Q : Graph nq)
 (hf : IsForest H) (qf : IsForest Q) (k s : Nat) (hk : 2≤k) (hs : 2≤s)
 (hn : nh=4*k+1) (hq : nq+s=4*k)
 (hp : ∀j,pad s (coefficient Q) j≤coefficient H j)
 (hb : 2*(k:Int)*(coefficient H k:Int)+2*(4*(k:Int)-(s:Int))*(s:Int)*
     (pad (s-1) (coefficient Q) (k-1):Int)≤
     (4*(k:Int)+1-(s:Int))*curvature H k) :
 coefficient H k+coefficient Q k≤coefficient H (k+1)+coefficient Q (k+1) := by
 by_cases hz : coefficient Q k=0
 · have hh := LeafBoundary.forest_prefix_step H hf k (by omega)
   omega
 · have hsupport : k≤nq := by
     by_cases ht : k≤nq
     · exact ht
     · exact False.elim (hz (coefficient_above_order Q (by omega)))
   have hsk : s≤3*k := by omega
   have he1 := graph_extension_upper_add Q (k-1)
   have he2 := graph_extension_upper_add Q (k-2)
   have hi1 : k-1+1=k := by omega
   have hi2 : k-2+1=k-1 := by omega
   have hi3 : k-2+2=k := by omega
   rw [hi1] at he1
   rw [hi2] at he2
   have h1i := Int.ofNat_le.mpr he1
   have h2i := Int.ofNat_le.mpr he2
   have hki1 : ((k-1:Nat):Int)=(k:Int)-1 := by omega
   have hki2 : ((k-2:Nat):Int)=(k:Int)-2 := by omega
   have hsi : ((s-1:Nat):Int)=(s:Int)-1 := by omega
   have hnqi : (nq:Int)=4*(k:Int)-(s:Int) := by omega
   simp only [Int.natCast_add,Int.natCast_mul,hki1,hki2,hnqi] at h1i h2i
   have hpad := pad_second_order s (coefficient Q) (k-2)
   rw [hi2,hi3] at hpad
   have hpad' := Nat.le_trans hpad (Nat.mul_le_mul_left 2 (hp k))
   have hpi := Int.ofNat_le.mpr hpad'
   simp only [Int.natCast_add,Int.natCast_mul,hsi] at hpi
   have hmass := pad_first_order (s-1) (coefficient Q) (k-2)
   rw [hi2] at hmass
   have hmi := Int.ofNat_le.mpr hmass
   simp only [Int.natCast_add,Int.natCast_mul,hsi] at hmi
   have hscale := Int.mul_le_mul_of_nonneg_left hmi
     (show 0≤2*(4*(k:Int)-(s:Int))*(s:Int) by
       exact Int.mul_nonneg (by omega) (by omega))
   have hbudget := InteriorIsolateAlgebra.curvature_budget (k:Int) (s:Int)
     (coefficient Q k:Int) (coefficient Q (k-1):Int) (coefficient Q (k-2):Int)
     (coefficient H k:Int) (curvature H k) (by omega) (by omega) (by omega)
     (Int.natCast_nonneg _) (by grind) (by grind) hpi (by grind)
   have hqc := forest_curvature_bound Q qf k
   have hqn := forest_curvature_nonnegative Q qf k
   have hqscale := Int.mul_le_mul_of_nonneg_right (show (nq:Int)≤4*(k:Int) by omega) hqn
   have hqhalf : (coefficient Q k:Int)≤2*curvature Q k := by
     have ht : (2*(k:Int))*(coefficient Q k:Int)≤(2*(k:Int))*(2*curvature Q k) := by grind
     exact Int.le_of_mul_le_mul_left ht (by omega)
   have hg := graph_curvature_growth H k
   have hqg := graph_curvature_growth Q k
   have hnhi : (nh:Int)=4*(k:Int)+1 := by omega
   rw [hnhi] at hg
   rw [hnqi] at hqg
   have ht : ((k:Int)+1)*((coefficient H k:Int)+(coefficient Q k:Int))≤
       ((k:Int)+1)*((coefficient H (k+1):Int)+(coefficient Q (k+1):Int)) := by grind
   have htt := Int.le_of_mul_le_mul_left ht (by omega)
   omega

end Erdos993.InteriorPadding
