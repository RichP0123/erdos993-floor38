import KernelUnimodality
import IsolatePaddingCounts

namespace Erdos993.BinomialProduct
open Counting KernelSlopeComparison BinomialKernel PaddingCounts

theorem sum_range_succ (q : Nat) (f : Nat → Nat) :
 sumBy (List.range (q+1)) f=sumBy (List.range q) f+f q := by
 rw [List.range_succ,sumBy_append]
 simp [sumBy]

theorem sum_range_shift (q : Nat) (f : Nat → Nat) :
 sumBy (List.range (q+1)) f=f 0+sumBy (List.range q) (fun i => f (i+1)) := by
 induction q with
 | zero => simp [sumBy]
 | succ q ih => rw [sum_range_succ,ih,sum_range_succ]; omega

theorem product_base (K a : Nat → Nat) (r : Nat) : product 0 K a r=K 0*a r := by
 simp [product,sumBy]

theorem product_cons (q : Nat) (K a : Nat → Nat) (r : Nat) :
 product (q+1) K a (r+1)=K 0*a (r+1)+product q (fun i => K (i+1)) a r := by
 unfold product
 rw [sum_range_shift]
 simp only [Nat.zero_le,Nat.sub_zero,if_true]
 congr 1
 apply sumBy_congr
 intro i _
 by_cases hi : i≤r
 · have hi1 : i+1≤r+1 := by omega
   simp [hi,hi1]
 · have hi1 : ¬i+1≤r+1 := by omega
   simp [hi,hi1]

theorem product_zero (q : Nat) (K a : Nat → Nat) : product q K a 0=K 0*a 0 := by
 cases q with
 | zero => exact product_base K a 0
 | succ q =>
   unfold product
   rw [sum_range_shift]
   simp only [Nat.le_refl,Nat.sub_zero,if_true]
   have hz : sumBy (List.range (q+1)) (fun i => K (i+1)*(if i+1≤0 then a (0-(i+1)) else 0))=0 := by
     have he : ∀ i, K (i+1)*(if i+1≤0 then a (0-(i+1)) else 0)=0 := by intro i; simp
     simp only [he]
     simp only [sumBy,List.map_const',List.sum_replicate_nat,Nat.mul_zero]
   rw [hz]
   omega

theorem product_extend (q : Nat) (K a : Nat → Nat) (r : Nat) (hz : K (q+1)=0) :
 product (q+1) K a r=product q K a r := by
 unfold product
 rw [sum_range_succ,hz]
 simp

theorem product_add (q : Nat) (K L a : Nat → Nat) (r : Nat) :
 product q (fun i => K i+L i) a r=product q K a r+product q L a r := by
 unfold product
 simp only [Nat.add_mul]
 exact sumBy_add _ _ _

def shift (K : Nat → Nat) : Nat → Nat
 | 0 => 0
 | i+1 => K i

theorem product_shift (q : Nat) (K a : Nat → Nat) (r : Nat) :
 product (q+1) (shift K) a (r+1)=product q K a r := by
 rw [product_cons]
 simp only [shift,Nat.zero_mul,Nat.zero_add]

theorem pascal_kernel (q : Nat) : binom (q+1)=(fun i => binom q i+shift (binom q) i) := by
 funext i
 cases i with
 | zero => simp [zero_rank,shift]
 | succ i => simp [binom,shift,Nat.add_comm]

theorem binomial_product (q : Nat) (a : Nat → Nat) (r : Nat) :
 product q (binom q) a r=pad q a r := by
 induction q generalizing r with
 | zero => rw [product_base]; simp [binom,pad]
 | succ q ih =>
   cases r with
   | zero => rw [product_zero]; simp [zero_rank,pad_zero_rank]
   | succ r =>
     rw [pascal_kernel,product_add,product_extend q (binom q) a (r+1) (above q (q+1) (by omega)),product_shift]
     rw [ih,ih]
     rfl

def delta (i : Nat) : Nat := if i=0 then 1 else 0

theorem delta_product (q : Nat) (a : Nat → Nat) (r : Nat) : product q delta a r=a r := by
 induction q with
 | zero => rw [product_base]; simp [delta]
 | succ q ih => rw [product_extend q delta a r (by simp [delta]),ih]

theorem star_product_zero (q : Nat) (a : Nat → Nat) : product q (star q) a 0=a 0 := by
 rw [product_zero,star_zero]
 omega

theorem star_product (q : Nat) (hq : 1≤q) (a : Nat → Nat) (r : Nat) :
 product q (star q) a (r+1)=pad q a (r+1)+a r := by
 have he : star q=(fun i => binom q i+shift delta i) := by
   funext i
   cases i with
   | zero => simp [star,shift]
   | succ i => simp [star,shift,delta]
 rw [he,product_add,binomial_product]
 obtain ⟨s,hs⟩ : ∃ s, q=s+1 := ⟨q-1,by omega⟩
 subst q
 rw [product_shift,delta_product]

end Erdos993.BinomialProduct
