import KernelSlopeComparison

namespace Erdos993.BinomialKernel

def binom : Nat → Nat → Nat
 | 0,0 => 1
 | 0,_+1 => 0
 | _+1,0 => 1
 | q+1,i+1 => binom q i+binom q (i+1)

theorem zero_rank (q : Nat) : binom q 0=1 := by cases q <;> rfl

theorem above (q i : Nat) (hi : q<i) : binom q i=0 := by
 induction q generalizing i with
 | zero => cases i <;> simp_all [binom]
 | succ q ih =>
   cases i with
   | zero => omega
   | succ i => simp [binom,ih i (by omega),ih (i+1) (by omega)]

theorem positive (q i : Nat) (hi : i≤q) : 0<binom q i := by
 induction q generalizing i with
 | zero =>
   have he : i=0 := by omega
   subst i
   decide
 | succ q ih =>
   cases i with
   | zero => simp [binom]
   | succ i => have hh := ih i (by omega); simp only [binom]; omega

theorem balance (q i : Nat) :
 (i+1)*binom q (i+1)+i*binom q i=q*binom q i := by
 induction q generalizing i with
 | zero => cases i <;> simp [binom]
 | succ q ih =>
   cases i with
   | zero =>
     have hh := ih 0
     simp only [binom,zero_rank,Nat.zero_add,Nat.one_mul,Nat.add_zero,Nat.mul_one] at *
     omega
   | succ i =>
     have h0 := ih i
     have h1 := ih (i+1)
     simp only [binom]
     grind

theorem first_rank (q : Nat) : binom q 1=q := by
 have hh := balance q 0
 simpa [zero_rank] using hh

theorem deletion_balance (q i : Nat) :
 (q+1)*binom q i+i*binom (q+1) i=(q+1)*binom (q+1) i := by
 cases i with
 | zero => simp [zero_rank]
 | succ i =>
   have hh := balance q i
   simp only [binom]
   grind

def star (q i : Nat) : Nat := binom q i+(if i=1 then 1 else 0)

theorem star_zero (q : Nat) : star q 0=1 := by simp [star,zero_rank]

theorem star_one (q : Nat) : star q 1=q+1 := by simp [star,first_rank]

theorem star_above (q i : Nat) (hq : 1≤q) (hi : q<i) : star q i=0 := by
 have hn : i≠1 := by omega
 simp [star,above q i hi,hn]

theorem star_positive (q i : Nat) (hi : i≤q) : 0<star q i := by
 have hh := positive q i hi
 unfold star
 omega

theorem cross_trans (a b c x y z : Nat) (hy : 0<y)
 (h1 : b*x≤a*y) (h2 : c*y≤b*z) : c*x≤a*z := by
 have h3 := Nat.mul_le_mul_right z h1
 have h4 := Nat.mul_le_mul_right x h2
 have hh : y*(c*x)≤y*(a*z) := by
   calc
    y*(c*x)=(c*y)*x := by grind
    _≤(b*z)*x := h4
    _=(b*x)*z := by grind
    _≤(a*y)*z := h3
    _=y*(a*z) := by grind
 exact Nat.le_of_mul_le_mul_left hh hy

theorem cross_of_adjacent (K L : Nat → Nat) (lo hi : Nat)
 (pos : ∀ i, lo≤i → i≤hi → 0<K i)
 (adj : ∀ i, lo≤i → i<hi → L (i+1)*K i≤L i*K (i+1))
 (i j : Nat) (hli : lo≤i) (hij : i≤j) (hjh : j≤hi) :
 L j*K i≤L i*K j := by
 induction j with
 | zero =>
   have he : i=0 := by omega
   subst i
   exact Nat.le_refl _
 | succ j ih =>
   by_cases he : i=j+1
   · subst i; exact Nat.le_refl _
   · have hj : i≤j := by omega
     exact cross_trans (L i) (L j) (L (j+1)) (K i) (K j) (K (j+1))
       (pos j (by omega) (by omega)) (ih hj (by omega)) (adj j (by omega) hjh)

theorem strong_lc (q i : Nat) :
 (i+1)*(binom q (i+1)*binom q (i+1))=
 (i+1)*(binom q i*binom q (i+2))+binom q i*binom q (i+2)+
 binom q i*binom q (i+1) := by
 have h0 := congrArg (fun x => x*binom q (i+1)) (balance q i)
 have h1 := congrArg (fun x => x*binom q i) (balance q (i+1))
 grind

theorem log_concave (q i : Nat) : binom q i*binom q (i+2)≤binom q (i+1)*binom q (i+1) := by
 have hh := strong_lc q i
 have he : (i+1)*(binom q i*binom q (i+2))≤(i+1)*(binom q (i+1)*binom q (i+1)) := by omega
 exact Nat.le_of_mul_le_mul_left he (by omega)

theorem star_log_concave (q i : Nat) : star q i*star q (i+2)≤star q (i+1)*star q (i+1) := by
 cases i with
 | zero =>
   have hh := balance q 1
   rw [first_rank] at hh
   simp only [Nat.zero_add,star_zero,star_one]
   have he : star q 2=binom q 2 := by simp [star]
   rw [he]
   grind
 | succ i =>
   cases i with
   | zero =>
     have hh := strong_lc q 1
     rw [first_rank] at hh
     have he2 : star q 2=binom q 2 := by simp [star]
     have he3 : star q 3=binom q 3 := by simp [star]
     simp only [Nat.zero_add,Nat.reduceAdd,star_one,he2,he3]
     by_cases hq : q<2
     · rw [above q 3 (by omega)]; omega
     · have hm := Nat.mul_le_mul_right (binom q 3) (show 2≤q by omega)
       have hle : 2*((q+1)*binom q 3)≤2*(binom q 2*binom q 2) := by grind
       exact Nat.le_of_mul_le_mul_left hle (by omega)
   | succ i =>
     have hn0 : i+1+1≠1 := by omega
     have hn1 : i+1+1+1≠1 := by omega
     have hn2 : i+1+1+2≠1 := by omega
     simpa only [star,if_neg hn0,if_neg hn1,if_neg hn2,Nat.add_zero] using log_concave q (i+1+1)

end Erdos993.BinomialKernel
