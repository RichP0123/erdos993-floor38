import QuarterEndBudget
namespace Erdos993.QuarterCertificate
open Counting Structure LeafBoundary PaddingCounts CurvatureProof QuarterBudget

/-- Uniform quarter-boundary certificate from actual graph curvature and
 an actual isolate-padding count bound. The latter is supplied by EndSupportPadding. -/
theorem quarter_padding_certificate {nh nq : Nat} (H : Graph nh) (Q : Graph nq)
 (hf : IsForest H) (qf : IsForest Q) (M s : Nat)
 (hn : nh+2=4*M) (hqn : nq+s+3=4*M) (hs : 2≤s)
 (padding : ∀ r, pad s (coefficient Q) r≤coefficient H r) :
 coefficient H (M-1)+coefficient Q (M-1)≤coefficient H M+coefficient Q M := by
 have hM : 2≤M := by omega
 have ik : M-1+1=M := by omega
 have ij : M-2+1=M-1 := by omega
 have ck : (((M-1:Nat):Int)+1)=(M:Int) := by omega
 let h : Int := (coefficient H (M-1):Int)
 let q : Int := (coefficient Q (M-1):Int)
 let p : Int := (coefficient Q (M-2):Int)
 let kh := curvature H (M-1)
 let kq := curvature Q (M-1)
 have hq0 : 0≤q := Int.natCast_nonneg _
 have hp0 : 0≤p := Int.natCast_nonneg _
 have hh0 : 0≤h := Int.natCast_nonneg _
 have kh0 : 0≤kh := forest_curvature_nonnegative H hf _
 have kq0 : 0≤kq := forest_curvature_nonnegative Q qf _
 have hcb := forest_curvature_bound H hf (M-1)
 have qcb := forest_curvature_bound Q qf (M-1)
 have hk : h≤3*kh := curvature_scaled (2*((M-1:Nat):Int)) nh 3 h kh
   (by omega) kh0 (by omega) hcb
 have qk : q≤2*kq := curvature_scaled (2*((M-1:Nat):Int)) nq 2 q kq
   (by omega) kq0 (by omega) qcb
 have bud : (s:Int)*q≤h+kh+kq := by
   by_cases hz : coefficient Q (M-1)=0
   · have he : q=0 := by simp [q,hz]
     rw [he]
     omega
   · have ns : M-1≤nq := by
       by_cases he : M-1≤nq
       · exact he
       · exact False.elim (hz (coefficient_above_order Q (by omega)))
     have gu := graph_extension_upper_int Q (M-2)
     rw [ij] at gu
     have cm : (((M-2:Nat):Int)+1)=((M-1:Nat):Int) := by omega
     rw [cm] at gu
     have gu' : ((M-1:Nat):Int)*q≤((nq:Int)-((M-1:Nat):Int)+1)*p := by
       have ce : (nq:Int)-((M-2:Nat):Int)=(nq:Int)-((M-1:Nat):Int)+1 := by omega
       simpa only [ce] using gu
     have ratio : q≤3*p := first_ratio _ _ q p (by omega) hp0 (by omega) gu'
     have pg := pad_first_order s (coefficient Q) (M-2)
     rw [ij] at pg
     have pn := padding (M-1)
     have pint : q+(s:Int)*p≤h := by
       have ht := Int.ofNat_le.mpr (Nat.le_trans pg pn)
       simpa only [Int.natCast_add,Int.natCast_mul] using ht
     by_cases small : s≤3
     · exact budget_two_three s h q kh kq (by omega) hq0 hk qk
         (first_padding_ratio s h q p (by omega) ratio pint)
     · by_cases four : s=4
       · subst s
         have cast4 : ((4:Nat):Int)=4 := by decide
         rw [cast4] at pint
         have ga : ((M:Int)-1)*q≤(3*(M:Int)-5)*p := by
           have c1 : ((M-1:Nat):Int)=(M:Int)-1 := by omega
           have c2 : (nq:Int)-((M-1:Nat):Int)+1=3*(M:Int)-5 := by omega
           rw [c2,c1] at gu'
           exact gu'
         have pm := Int.mul_le_mul_of_nonneg_left pint (show 0≤3*(M:Int)-5 by omega)
         have pr : (7*(M:Int)-9)*q≤(3*(M:Int)-5)*h := by
           have he : (3*(M:Int)-5)*(q+4*p)=
               (3*(M:Int)-5)*q+4*((3*(M:Int)-5)*p) := by grind
           rw [he] at pm
           have ht := Int.mul_le_mul_of_nonneg_left ga (show (0:Int)≤4 by decide)
           have hi : (7*(M:Int)-9)*q=(3*(M:Int)-5)*q+4*(((M:Int)-1)*q) := by grind
           rw [hi]
           omega
         have ch : 2*((M:Int)-1)*h≤(4*(M:Int)-2)*kh := by
           have c1 : ((M-1:Nat):Int)=(M:Int)-1 := by omega
           have c2 : (nh:Int)=4*(M:Int)-2 := by omega
           simpa only [c1,c2] using hcb
         exact budget_four M h q kh kq (by omega) hq0 ch qk pr
       · have hs5 : 5≤s := by omega
         have hm3 : 3≤M := by omega
         have ii : M-3+1=M-2 := by omega
         have ii2 : M-3+2=M-1 := by omega
         let z : Int := (coefficient Q (M-3):Int)
         have gz := graph_extension_upper_int Q (M-3)
         rw [ii] at gz
         have gz' : (((M-1:Nat):Int)-1)*p≤
             ((nq:Int)-((M-1:Nat):Int)+1+1)*z := by
           have c1 : ((M-3:Nat):Int)+1=((M-1:Nat):Int)-1 := by omega
           have c2 : (nq:Int)-((M-3:Nat):Int)=(nq:Int)-((M-1:Nat):Int)+1+1 := by omega
           simpa only [c1,c2] using gz
         have r2 : q≤12*z := second_ratio _ _ q p z (by omega) (by omega)
           (Int.natCast_nonneg _) (by omega) gu' gz'
         have p2 := pad_second_order s (coefficient Q) (M-3)
         rw [ii,ii2] at p2
         have p2h := Nat.le_trans p2 (Nat.mul_le_mul_left 2 (padding (M-1)))
         have pi : 2*q+2*(s:Int)*p+(s:Int)*((s:Int)-1)*z≤2*h := by
           have ht := Int.ofNat_le.mpr p2h
           have cs : ((s-1:Nat):Int)=(s:Int)-1 := by omega
           simpa only [Int.natCast_add,Int.natCast_mul,cs] using ht
         exact budget_large s h q kh kq (by omega) hq0 hk qk
           (second_padding_ratio s h q p z (by omega) ratio r2 pi)
 have gh := graph_curvature_growth H (M-1)
 have gq := graph_curvature_growth Q (M-1)
 rw [ik,ck] at gh gq
 have ch : (nh:Int)-3*((M-1:Nat):Int)=(M:Int)+1 := by omega
 have cq : (nq:Int)-3*((M-1:Nat):Int)=(M:Int)-(s:Int) := by omega
 rw [ch] at gh
 rw [cq] at gq
 change ((M:Int)+1)*h+kh≤(M:Int)*(coefficient H M:Int) at gh
 change ((M:Int)-(s:Int))*q+kq≤(M:Int)*(coefficient Q M:Int) at gq
 have hz : 0≤(M:Int)*((coefficient H M:Int)+(coefficient Q M:Int)-h-q) := by
   simp only [Int.add_mul,Int.sub_mul,Int.one_mul] at gh gq
   simp only [Int.mul_sub,Int.mul_add]
   omega
 have hh := Int.nonneg_of_mul_nonneg_right hz (show 0<(M:Int) by omega)
 change (coefficient H (M-1):Nat)+(coefficient Q (M-1):Nat)≤_
 dsimp [h,q] at hh
 omega

end Erdos993.QuarterCertificate
