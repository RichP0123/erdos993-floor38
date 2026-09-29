import BinomialProduct

namespace Erdos993.LeafBalanceKernel
open BinomialKernel Counting

/-- Zero-extended coefficients of x^k (1+x)^e. -/
def atom (k e r : Nat) : Nat := if k ≤ r then binom e (r-k) else 0

theorem binom_rising (e i : Nat) (h : 2*i+1 ≤ e) :
 binom e i ≤ binom e (i+1) := by
 have hb := balance e i
 have hm := Nat.mul_le_mul_right (binom e i) h
 have hh : (i+1)*binom e i ≤ (i+1)*binom e (i+1) := by grind
 exact Nat.le_of_mul_le_mul_left hh (by omega)

theorem binom_falling (e i : Nat) (h : e ≤ 2*i+1) :
 binom e (i+1) ≤ binom e i := by
 have hb := balance e i
 have hm := Nat.mul_le_mul_right (binom e i) h
 have hh : (i+1)*binom e (i+1) ≤ (i+1)*binom e i := by grind
 exact Nat.le_of_mul_le_mul_left hh (by omega)

theorem atom_rising (k e r : Nat) (h : 2*r+1 ≤ 2*k+e) :
 atom k e r ≤ atom k e (r+1) := by
 by_cases hr : k≤r
 · have hr1 : k≤r+1 := by omega
   have he : r+1-k=(r-k)+1 := by omega
   simp only [atom,hr,hr1,if_true,he]
   exact binom_rising e (r-k) (by omega)
 · simp only [atom,hr,if_false]
   exact Nat.zero_le _

theorem atom_falling (k e r : Nat) (h : 2*k+e ≤ 2*r+1) :
 atom k e (r+1) ≤ atom k e r := by
 have hr : k≤r := by omega
 have hr1 : k≤r+1 := by omega
 have he : r+1-k=(r-k)+1 := by omega
 simp only [atom,hr,hr1,if_true,he]
 exact binom_falling e (r-k) (by omega)

/-- Twice every center lies in [lo,hi]. This is a coefficient theorem;
 actual leafy graph correspondence is a separate obligation. -/
def mixture (xs : List (Nat × Nat)) (r : Nat) : Nat :=
 sumBy xs (fun p => atom p.1 p.2 r)

theorem mixture_rising (xs : List (Nat × Nat)) (lo r : Nat)
 (bounds : ∀ p∈xs, lo≤2*p.1+p.2) (hr : 2*r+1≤lo) :
 mixture xs r ≤ mixture xs (r+1) := by
 induction xs with
 | nil => simp [mixture,sumBy]
 | cons p xs ih =>
   have h1 := atom_rising p.1 p.2 r (by have := bounds p (by simp); omega)
   have h2 := ih (by intro q hq; exact bounds q (by simp [hq]))
   simp only [mixture,sumBy,List.map_cons,List.sum_cons] at *
   omega

theorem mixture_falling (xs : List (Nat × Nat)) (hi r : Nat)
 (bounds : ∀ p∈xs, 2*p.1+p.2≤hi) (hr : hi≤2*r+1) :
 mixture xs (r+1) ≤ mixture xs r := by
 induction xs with
 | nil => simp [mixture,sumBy]
 | cons p xs ih =>
   have h1 := atom_falling p.1 p.2 r (by have := bounds p (by simp); omega)
   have h2 := ih (by intro q hq; exact bounds q (by simp [hq]))
   simp only [mixture,sumBy,List.map_cons,List.sum_cons] at *
   omega

/-- A fall and later rise force center spread at least four, with a
 quantitative bound by the return gap. Plateaus and point masses are allowed. -/
theorem return_requires_spread (xs : List (Nat × Nat)) (lo hi M b : Nat)
 (lower : ∀ p∈xs, lo≤2*p.1+p.2)
 (upper : ∀ p∈xs, 2*p.1+p.2≤hi)
 (hb : M<b) (fall : mixture xs (M+1)<mixture xs M)
 (rise : mixture xs b<mixture xs (b+1)) : lo+2*(b-M+1)≤hi := by
 have hm : lo<2*M+1 := by
   by_cases h : 2*M+1≤lo
   · have := mixture_rising xs lo M lower h; omega
   · omega
 have ht : 2*b+1<hi := by
   by_cases h : hi≤2*b+1
   · have := mixture_falling xs hi b upper h; omega
   · omega
 omega

theorem width_three_no_return (xs : List (Nat × Nat)) (lo hi : Nat)
 (lower : ∀ p∈xs, lo≤2*p.1+p.2)
 (upper : ∀ p∈xs, 2*p.1+p.2≤hi) (width : hi≤lo+3)
 (M b : Nat) (hb : M<b) (fall : mixture xs (M+1)<mixture xs M) :
 mixture xs (b+1)≤mixture xs b := by
 by_cases h : mixture xs (b+1)≤mixture xs b
 · exact h
 · have := return_requires_spread xs lo hi M b lower upper hb fall (by omega)
   omega

end Erdos993.LeafBalanceKernel
