import BinomialKernel

namespace Erdos993.KernelUnimodality
open KernelSlopeComparison DeletionFirstFall

theorem isum_append {α : Type} (xs ys : List α) (f : α → Int) :
 isum (xs++ys) f=isum xs f+isum ys f := by simp [isum,List.map_append,List.sum_append]

theorem isum_range_succ (q : Nat) (f : Nat → Int) :
 isum (List.range (q+1)) f=isum (List.range q) f+f q := by
 rw [List.range_succ,isum_append]
 simp [isum]

theorem isum_range_shift (q : Nat) (f : Nat → Int) :
 isum (List.range (q+1)) f=f 0+isum (List.range q) (fun i => f (i+1)) := by
 induction q with
 | zero => simp [isum]
 | succ q ih => rw [isum_range_succ,ih,isum_range_succ]; omega

theorem isum_congr {α : Type} (xs : List α) (f g : α → Int)
 (h : ∀ x∈xs, f x=g x) : isum xs f=isum xs g := by
 induction xs with
 | nil => rfl
 | cons x xs ih =>
   have hh := h x (by simp)
   have ht := ih (by intro y hy; exact h y (by simp [hy]))
   simp only [isum,List.map_cons,List.sum_cons] at *
   omega

theorem next_slope (q : Nat) (K a : Nat → Nat) (r : Nat) (hzero : K (q+1)=0) :
 (product q K a (r+2):Int)-(product q K a (r+1):Int)=
 (K 0:Int)*slope a (r+1)+
 isum (List.range (q+1)) (fun i => (K (i+1):Int)*slope a ((r:Int)-i)) := by
 have hs := product_slope q K a (r+1)
 simp only [Nat.add_assoc,Nat.reduceAdd] at hs
 rw [hs,isum_range_shift]
 have h0 : ((r+1:Nat):Int)-(0:Nat)=(r+1:Int) := by omega
 rw [h0,isum_range_succ]
 have ht : isum (List.range q) (fun i => (K (i+1):Int)*slope a (((r+1:Nat):Int)-((i+1:Nat):Int)))=
   isum (List.range q) (fun i => (K (i+1):Int)*slope a ((r:Int)-i)) := by
   apply isum_congr
   intro i _
   have he : (((r+1:Nat):Int)-((i+1:Nat):Int))=(r:Int)-i := by omega
   rw [he]
 rw [ht,hzero]
 simp

theorem product_tail (q : Nat) (K a : Nat → Nat) (m r : Nat)
 (ua : Unimodal a) (ha : FirstFall a m) (hr : m+q≤r) :
 product q K a (r+1)≤product q K a r := by
 have ht : ∀ i∈List.range (q+1), (K i:Int)*slope a ((r:Int)-i)≤0 := by
   intro i hi
   have hii := List.mem_range.mp hi
   have hs := slope_after a m ha ua ((r:Int)-i) (by omega)
   exact Int.mul_nonpos_of_nonneg_of_nonpos (by omega) hs
 have hs := isum_le (List.range (q+1)) _ (fun _ => 0) ht
 have hz : isum (List.range (q+1)) (fun _ => (0:Int))=0 := by
   simp only [isum,List.map_const',List.sum_replicate_int,Int.mul_zero]
 rw [hz,←product_slope] at hs
 omega

theorem product_last_fall (q : Nat) (K a : Nat → Nat) (m : Nat)
 (ua : Unimodal a) (ha : FirstFall a m) (hKq : 0<K q) :
 product q K a (m+q+1)<product q K a (m+q) := by
 have ht : ∀ i∈List.range (q+1), (K i:Int)*slope a (((m+q:Nat):Int)-i)≤0 := by
   intro i hi
   have hii := List.mem_range.mp hi
   have hs := slope_after a m ha ua (((m+q:Nat):Int)-i) (by omega)
   exact Int.mul_nonpos_of_nonneg_of_nonpos (by omega) hs
 have he : ∃ i∈List.range (q+1), (K i:Int)*slope a (((m+q:Nat):Int)-i)<0 := by
   refine ⟨q,List.mem_range.mpr (by omega),?_⟩
   have heq : (((m+q:Nat):Int)-q)=(m:Int) := by omega
   rw [heq,slope_nat]
   exact Int.mul_neg_of_pos_of_neg (by omega) (by have hh:=ha.1; omega)
 have hs := isum_negative _ _ ht he
 rw [←product_slope] at hs
 omega

theorem product_no_early_fall (q : Nat) (K a : Nat → Nat) (m r : Nat)
 (ha : FirstFall a m) (hr : r<m) : product q K a r≤product q K a (r+1) := by
 have ht : ∀ i∈List.range (q+1), 0≤(K i:Int)*slope a ((r:Int)-i) := by
   intro i _
   have hs := slope_before a m ha ((r:Int)-i) (by omega)
   exact Int.mul_nonneg (by omega) hs
 have hs := isum_nonneg _ _ ht
 rw [←product_slope] at hs
 omega

theorem strict_step (q : Nat) (K a : Nat → Nat) (m r : Nat)
 (ua : Unimodal a) (ha : FirstFall a m)
 (pos : ∀ i, i≤q → 0<K i) (hzero : K (q+1)=0)
 (lc : ∀ i, K i*K (i+2)≤K (i+1)*K (i+1))
 (hlo : m≤r) (hhi : r<m+q)
 (hf : product q K a (r+1)<product q K a r) :
 product q K a (r+2)<product q K a (r+1) := by
 let t := r-m
 have htq : t<q := by dsimp [t]; omega
 have cross : ∀ i j, i≤j → j<q → K (j+1)*K i≤K (i+1)*K j := by
   intro i j hij hjq
   exact BinomialKernel.cross_of_adjacent K (fun z => K (z+1)) 0 (q-1)
     (by intro z _ hz; exact pos z (by omega))
     (by intro z _ _; simpa only [Nat.add_assoc,Nat.reduceAdd,Nat.mul_comm] using lc z)
     i j (by omega) hij (by omega)
 have left : ∀ i∈List.range (q+1), i≤t →
   slope a ((r:Int)-i)≤0 ∧ (K (t+1):Int)*K i≤(K t:Int)*K (i+1) := by
   intro i _ hit
   refine ⟨slope_after a m ha ua ((r:Int)-i) (by dsimp [t] at hit; omega),?_⟩
   have hh := cross i t hit htq
   have hc : (K (t+1):Int)*K i≤(K (i+1):Int)*K t := by exact_mod_cast hh
   simpa only [Int.mul_comm] using hc
 have right : ∀ i∈List.range (q+1), t<i →
   0≤slope a ((r:Int)-i) ∧ (K t:Int)*K (i+1)≤(K (t+1):Int)*K i := by
   intro i hi hit
   refine ⟨slope_before a m ha ((r:Int)-i) (by dsimp [t] at hit; omega),?_⟩
   have hii := List.mem_range.mp hi
   by_cases he : i=q
   · subst i; rw [hzero]; simp; exact Int.mul_nonneg (by omega) (by omega)
   · have hh := cross t i (by omega) (by omega)
     have hc : (K (i+1):Int)*K t≤(K (t+1):Int)*K i := by exact_mod_cast hh
     simpa only [Int.mul_comm] using hc
 have fall : isum (List.range (q+1)) (fun i => (K i:Int)*slope a ((r:Int)-i))<0 := by
   rw [←product_slope]; omega
 have hp0 := pos t (by omega)
 have hp1 := pos (t+1) (by omega)
 have hs := weighted_transfer (List.range (q+1)) (fun i => (K i:Int))
   (fun i => (K (i+1):Int)) (fun i => slope a ((r:Int)-i)) t
   (by change 0<(K t:Int); omega) (by change 0<(K (t+1):Int); omega) left right fall
 dsimp only at hs
 have ht := slope_after a m ha ua (r+1) (by omega)
 have hn := Int.mul_nonpos_of_nonneg_of_nonpos (show 0≤(K 0:Int) by omega) ht
 have hnext := next_slope q K a r hzero
 omega

/-- A finite log-concave kernel with no internal zeros preserves ordinary
 unimodality. The input may have plateaus; its first strict fall is explicit. -/
theorem preserves_unimodality (q : Nat) (K a : Nat → Nat) (m : Nat)
 (ua : Unimodal a) (ha : FirstFall a m)
 (pos : ∀ i, i≤q → 0<K i) (hzero : K (q+1)=0)
 (lc : ∀ i, K i*K (i+2)≤K (i+1)*K (i+1)) : Unimodal (product q K a) := by
 have hex := product_last_fall q K a m ua ha (pos q (by omega))
 obtain ⟨M,hM,hpre⟩ := Foundation.least_witness
   (fun r => product q K a (r+1)<product q K a r) ⟨m+q,hex⟩
 have hMm : m≤M := by
   by_cases hh : m≤M
   · exact hh
   · have h := product_no_early_fall q K a m M ha (by omega); omega
 have hstrict : ∀ j, M≤j → j≤m+q → product q K a (j+1)<product q K a j := by
   intro j
   induction j with
   | zero =>
     intro hj _
     have he : M=0 := by omega
     subst M
     exact hM
   | succ j ih =>
     intro hj hq
     by_cases he : j+1=M
     · subst M; exact hM
     · have hf := ih (by omega) (by omega)
       exact strict_step q K a m j ua ha pos hzero lc (by omega) (by omega) hf
 refine ⟨M,?_,?_⟩
 · intro i hi
   have hh := hpre i hi
   omega
 · intro i hi
   by_cases hh : m+q≤i
   · exact product_tail q K a m i ua ha hh
   · have hs := hstrict i hi (by omega); omega

theorem star_preserves (q : Nat) (hq : 1≤q) (a : Nat → Nat) (m : Nat)
 (ua : Unimodal a) (ha : FirstFall a m) :
 Unimodal (product q (BinomialKernel.star q) a) := by
 apply preserves_unimodality q (BinomialKernel.star q) a m ua ha
 · exact BinomialKernel.star_positive q
 · exact BinomialKernel.star_above q (q+1) hq (by omega)
 · exact BinomialKernel.star_log_concave q

end Erdos993.KernelUnimodality
