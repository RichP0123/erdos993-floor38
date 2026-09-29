import InducedIsolateBudget
namespace Erdos993.InteriorIsolateAlgebra

def surplus (k s : Int) : Int :=
 (4*k-(4*k+1-s)*(2*s+1))*(3*k-s+1)*(3*k-s+2)+
 4*s*(5*k-s)*k*(3*k-s+2)+2*s*(s-1)*(9*k-2*s)*k*(k-1)

theorem surplus_nonnegative (k s : Int) (hk : 2≤k) (hs : 2≤s) (hsk : s≤3*k) :
 0≤surplus k s := by
 by_cases he : s=2
 · rw [he]
   have h : surplus k 2=k*(3*k-1)*(4*k-1) := by unfold surplus; grind
   rw [h]
   exact Int.mul_nonneg (Int.mul_nonneg (by omega) (by omega)) (by omega)
 · let t := s-3
   let z := 3*k-s
   have ht : 0≤t := by dsimp [t]; omega
   have hz : 0≤z := by dsimp [z]; omega
   have hp : 0≤6*t^5+30*t^4*z+66*t^4+42*t^3*z^2+282*t^3*z+318*t^3+
       18*t^2*z^3+348*t^2*z^2+1104*t^2*z+882*t^2+78*t*z^3+885*t*z^2+
       2025*t*z+1350*t+72*z^3+630*z^2+1242*z+756 := by
     repeat' (first | omega | apply Int.add_nonneg | apply Int.mul_nonneg | apply Int.pow_nonneg)
   have hid : 27*surplus k s=6*t^5+30*t^4*z+66*t^4+42*t^3*z^2+282*t^3*z+318*t^3+
       18*t^2*z^3+348*t^2*z^2+1104*t^2*z+882*t^2+78*t*z^3+885*t*z^2+
       2025*t*z+1350*t+72*z^3+630*z^2+1242*z+756 := by
     dsimp [t,z,surplus]
     grind
   omega

theorem curvature_budget (k s q q1 q2 h x : Int)
 (hk : 2≤k) (hs : 2≤s) (hsk : s≤3*k) (hq : 0≤q)
 (h1 : k*q≤(3*k-s+1)*q1)
 (h2 : (k-1)*q1≤(3*k-s+2)*q2)
 (hp : 2*q+2*s*q1+s*(s-1)*q2≤2*h)
 (hc : 2*k*h+2*(4*k-s)*s*(q1+(s-1)*q2)≤(4*k+1-s)*x) :
 (2*s+1)*q≤2*x := by
 have hd : 0<3*k-s+1 := by omega
 have he : 0<3*k-s+2 := by omega
 have hm : 0<4*k+1-s := by omega
 have hp' := Int.mul_le_mul_of_nonneg_left hp (show 0≤k by omega)
 have hc' : 2*k*q+2*s*(5*k-s)*q1+s*(s-1)*(9*k-2*s)*q2≤(4*k+1-s)*x := by grind
 have h12 := Int.mul_le_mul_of_nonneg_left h1 (show 0≤k-1 by omega)
 have h22 := Int.mul_le_mul_of_nonneg_left h2 (show 0≤3*k-s+1 by omega)
 have hqq : k*(k-1)*q≤(3*k-s+1)*(3*k-s+2)*q2 := by grind
 have hcscale := Int.mul_le_mul_of_nonneg_left hc'
   (show 0≤2*(3*k-s+1)*(3*k-s+2) by exact Int.mul_nonneg (by omega) (by omega))
 have h1scale := Int.mul_le_mul_of_nonneg_left h1
   (show 0≤4*s*(5*k-s)*(3*k-s+2) by
     exact Int.mul_nonneg (Int.mul_nonneg (by omega) (by omega)) (by omega))
 have h2scale := Int.mul_le_mul_of_nonneg_left hqq
   (show 0≤2*s*(s-1)*(9*k-2*s) by
     exact Int.mul_nonneg (Int.mul_nonneg (by omega) (by omega)) (by omega))
 have hsur := Int.mul_nonneg (surplus_nonnegative k s hk hs hsk) hq
 have ht : ((4*k+1-s)*(3*k-s+1)*(3*k-s+2))*((2*s+1)*q)≤
     ((4*k+1-s)*(3*k-s+1)*(3*k-s+2))*(2*x) := by
   unfold surplus at hsur
   grind
 exact Int.le_of_mul_le_mul_left ht (Int.mul_pos (Int.mul_pos hm hd) he)

end Erdos993.InteriorIsolateAlgebra
