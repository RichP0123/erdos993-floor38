import EndSupportPadding
namespace Erdos993.QuarterBudget

theorem budget_two_three (s h q kh kq : Int) (hs : s=2 ∨ s=3)
 (hq : 0≤q) (hh : h≤3*kh) (hk : q≤2*kq)
 (hp : (s+3)*q≤3*h) : s*q≤h+kh+kq := by
 rcases hs with hs | hs <;> subst s <;> omega

theorem large_polynomial_positive (s : Int) (hs : 5≤s) :
 0≤s*s-11*s+33 := by
 by_cases he : s=5
 · subst s; decide
 · have hp := Int.mul_nonneg (show 0≤s-5 by omega) (show 0≤s-6 by omega)
   have hh : (s-5)*(s-6)+3=s*s-11*s+33 := by grind
   omega

theorem budget_large (s h q kh kq : Int) (hs : 5≤s)
 (hq : 0≤q) (hh : h≤3*kh) (hk : q≤2*kq)
 (hp : (s*s+7*s+24)*q≤24*h) : s*q≤h+kh+kq := by
 have hb := Int.mul_nonneg (large_polynomial_positive s hs) hq
 have he : (s*s+7*s+24)*q=18*(s*q)-9*q+(s*s-11*s+33)*q := by grind
 rw [he] at hp
 omega

theorem budget_four_ratio (M h q : Int) (hM : 2≤M) (hq : 0≤q)
 (hp : (7*M-9)*q≤(3*M-5)*h) : 7*(2*M-1)*q≤2*(3*M-2)*h := by
 have hmul := Int.mul_le_mul_of_nonneg_left hp (show 0≤2*(3*M-2) by omega)
 have hn := Int.mul_nonneg (show 0≤9*M+1 by omega) hq
 have he : 2*(3*M-2)*((7*M-9)*q)=
     (3*M-5)*(7*(2*M-1)*q)+(9*M+1)*q := by grind
 have he' : 2*(3*M-2)*((3*M-5)*h)=(3*M-5)*(2*(3*M-2)*h) := by grind
 rw [he,he'] at hmul
 have hd : 0≤(3*M-5)*(2*(3*M-2)*h-7*(2*M-1)*q) := by
   rw [Int.mul_sub]
   omega
 have hc := Int.nonneg_of_mul_nonneg_right hd (show 0<3*M-5 by omega)
 omega

theorem budget_four (M h q kh kq : Int) (hM : 2≤M)
 (hq : 0≤q) (hh : 2*(M-1)*h≤(4*M-2)*kh) (hk : q≤2*kq)
 (hp : (7*M-9)*q≤(3*M-5)*h) : 4*q≤h+kh+kq := by
 have hr := budget_four_ratio M h q hM hq hp
 have hm := Int.mul_le_mul_of_nonneg_left hk (show 0≤2*M-1 by omega)
 have he : 2*(3*M-2)*h=(4*M-2)*h+2*(M-1)*h := by grind
 have he' : (2*M-1)*(2*kq)=(4*M-2)*kq := by grind
 have he'' : 7*(2*M-1)*q+(2*M-1)*q=(4*M-2)*(4*q) := by grind
 rw [he] at hr
 rw [he'] at hm
 have hb : (4*M-2)*(4*q)≤(4*M-2)*(h+kh+kq) := by
   rw [←he'',Int.mul_add,Int.mul_add]
   omega
 have hz : 0≤(4*M-2)*(h+kh+kq-4*q) := by rw [Int.mul_sub]; omega
 have ht := Int.nonneg_of_mul_nonneg_right hz (show 0<4*M-2 by omega)
 omega

theorem curvature_scaled (m L t h c : Int) (hm : 0<m) (hc : 0≤c)
 (hL : L≤t*m) (hb : m*h≤L*c) : h≤t*c := by
 have hl := Int.mul_le_mul_of_nonneg_right hL hc
 have he : (t*m)*c=m*(t*c) := by grind
 rw [he] at hl
 have hz : 0≤m*(t*c-h) := by rw [Int.mul_sub]; omega
 have hh := Int.nonneg_of_mul_nonneg_right hz hm
 omega

theorem first_ratio (k A q p : Int) (hk : 0<k) (hp : 0≤p)
 (ha : A≤3*k) (he : k*q≤A*p) : q≤3*p := by
 have hh := Int.mul_le_mul_of_nonneg_right ha hp
 have hi : (3*k)*p=k*(3*p) := by grind
 rw [hi] at hh
 have hz : 0≤k*(3*p-q) := by rw [Int.mul_sub]; omega
 have hc := Int.nonneg_of_mul_nonneg_right hz hk
 omega

theorem second_ratio (k A q p z : Int) (hk : 2≤k) (ha : 0≤A)
 (hz : 0≤z) (hA : A≤3*(k-1))
 (he : k*q≤A*p) (he' : (k-1)*p≤(A+1)*z) : q≤12*z := by
 have e1 := Int.mul_le_mul_of_nonneg_left he (show 0≤k-1 by omega)
 have e2 := Int.mul_le_mul_of_nonneg_left he' ha
 have hA' : A+1≤4*k := by omega
 have e3 := Int.mul_le_mul_of_nonneg_right hA (show 0≤A+1 by omega)
 have e4 := Int.mul_le_mul_of_nonneg_left hA' (show 0≤3*(k-1) by omega)
 have ep : A*(A+1)≤12*(k*(k-1)) := by
   have hh : 3*(k-1)*(4*k)=12*(k*(k-1)) := by grind
   omega
 have e5 := Int.mul_le_mul_of_nonneg_right ep hz
 have ei : (k-1)*(A*p)=A*((k-1)*p) := by grind
 have ej : A*((A+1)*z)=(A*(A+1))*z := by grind
 have ek : (k-1)*(k*q)=(k*(k-1))*q := by grind
 have el : (12*(k*(k-1)))*z=(k*(k-1))*(12*z) := by grind
 rw [ei,ek] at e1
 rw [ej] at e2
 rw [el] at e5
 have hh : 0≤(k*(k-1))*(12*z-q) := by rw [Int.mul_sub]; omega
 have hp := Int.mul_pos (show 0<k by omega) (show 0<k-1 by omega)
 have hc := Int.nonneg_of_mul_nonneg_right hh hp
 omega

theorem first_padding_ratio (s h q p : Int) (hs : 0≤s)
 (hp : q≤3*p) (hh : q+s*p≤h) : (s+3)*q≤3*h := by
 have hm := Int.mul_le_mul_of_nonneg_left hp hs
 have he : (s+3)*q=s*q+3*q := by grind
 have he' : s*(3*p)=3*(s*p) := by grind
 rw [he'] at hm
 rw [he]
 omega

theorem second_padding_ratio (s h q p z : Int) (hs : 1≤s)
 (hp : q≤3*p) (hz : q≤12*z)
 (hh : 2*q+2*s*p+s*(s-1)*z≤2*h) : (s*s+7*s+24)*q≤24*h := by
 have h1 := Int.mul_le_mul_of_nonneg_left hp (show 0≤8*s by omega)
 have h2 := Int.mul_le_mul_of_nonneg_left hz
   (Int.mul_nonneg (show 0≤s by omega) (show 0≤s-1 by omega))
 have h3 := Int.mul_le_mul_of_nonneg_left hh (show (0:Int)≤12 by decide)
 have e1 : (8*s)*(3*p)=12*(2*s*p) := by grind
 have e2 : (s*(s-1))*(12*z)=12*(s*(s-1)*z) := by grind
 have e3 : (s*s+7*s+24)*q=24*q+(8*s)*q+(s*(s-1))*q := by grind
 rw [e1] at h1
 rw [e2] at h2
 simp only [Int.mul_add] at h3
 rw [e3]
 omega

end Erdos993.QuarterBudget
