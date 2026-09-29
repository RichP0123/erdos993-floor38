import DeletionFirstFall

namespace Erdos993.KernelSlopeComparison
open DeletionFirstFall

def isum {α : Type} (xs : List α) (f : α → Int) : Int := (xs.map f).sum

theorem isum_le {α : Type} (xs : List α) (f g : α → Int)
 (h : ∀ x∈xs, f x≤g x) : isum xs f≤isum xs g := by
 induction xs with
 | nil => simp [isum]
 | cons x xs ih =>
   have hx := h x (by simp)
   have ht := ih (by intro y hy; exact h y (by simp [hy]))
   simp only [isum,List.map_cons,List.sum_cons] at *
   omega

theorem isum_mul {α : Type} (xs : List α) (c : Int) (f : α → Int) :
 isum xs (fun x => c*f x)=c*isum xs f := by
 induction xs with
 | nil => simp [isum]
 | cons x xs ih =>
   simp only [isum,List.map_cons,List.sum_cons] at *
   rw [Int.mul_add,ih]

/-- Cross-multiplied first-fall kernel comparison. The sign split and
 coefficient inequalities are explicit, including zero endpoint weights. -/
theorem weighted_transfer (xs : List Nat) (K L s : Nat → Int) (t : Nat)
 (hK : 0<K t) (hL : 0<L t)
 (left : ∀ i∈xs, i≤t → s i≤0 ∧ L t*K i≤K t*L i)
 (right : ∀ i∈xs, t<i → 0≤s i ∧ K t*L i≤L t*K i)
 (fall : isum xs (fun i => K i*s i)<0) :
 isum xs (fun i => L i*s i)<0 := by
 have hterm : ∀ i∈xs, K t*(L i*s i)≤L t*(K i*s i) := by
   intro i hi
   by_cases hit : i≤t
   · obtain ⟨hs,hw⟩ := left i hi hit
     have hm := Int.mul_le_mul_of_nonpos_right hw hs
     simpa only [Int.mul_assoc] using hm
   · obtain ⟨hs,hw⟩ := right i hi (by omega)
     have hm := Int.mul_le_mul_of_nonneg_right hw hs
     simpa only [Int.mul_assoc] using hm
 have hh := isum_le xs _ _ hterm
 rw [isum_mul,isum_mul] at hh
 have hn : L t*isum xs (fun i => K i*s i)<0 := Int.mul_neg_of_pos_of_neg hL fall
 have hneg : K t*isum xs (fun i => L i*s i)<0 := by omega
 have ht := Int.neg_of_mul_neg_right hneg (by omega)
 exact ht

/-- A zero-extended natural coefficient sequence. -/
def extended (a : Nat → Nat) (i : Int) : Int :=
 if i<0 then 0 else (a i.toNat : Int)

def slope (a : Nat → Nat) (i : Int) : Int := extended a (i+1)-extended a i

theorem slope_nat (a : Nat → Nat) (i : Nat) :
 slope a i=(a (i+1):Int)-(a i:Int) := by
 have h0 : ¬(i:Int)<0 := by omega
 have h1 : ¬(i:Int)+1<0 := by omega
 simp [slope,extended,h0,h1]

theorem slope_before (a : Nat → Nat) (m : Nat) (hm : FirstFall a m)
 (i : Int) (hi : i<m) : 0≤slope a i := by
 by_cases hn : i<0
 · by_cases hn1 : i+1<0
   · simp [slope,extended,hn,hn1]
   · have he : i=-1 := by omega
     subst i
     simp [slope,extended]
 · have he : i=(i.toNat:Int) := by omega
   rw [he,slope_nat]
   have hh := hm.2 i.toNat (by omega)
   omega

theorem slope_after (a : Nat → Nat) (m : Nat) (hm : FirstFall a m)
 (ua : Unimodal a) (i : Int) (hi : (m:Int)≤i) : slope a i≤0 := by
 have he : i=(i.toNat:Int) := by omega
 rw [he,slope_nat]
 have hh := LeafBoundary.unimodal_tail_of_fall a ua m hm.1 i.toNat (by omega)
 omega

theorem isum_nonneg {α : Type} (xs : List α) (f : α → Int)
 (h : ∀ x∈xs, 0≤f x) : 0≤isum xs f := by
 induction xs with
 | nil => simp [isum]
 | cons x xs ih =>
   have hx := h x (by simp)
   have ht := ih (by intro y hy; exact h y (by simp [hy]))
   simp only [isum,List.map_cons,List.sum_cons] at *
   omega

theorem isum_negative {α : Type} (xs : List α) (f : α → Int)
 (h : ∀ x∈xs, f x≤0) (he : ∃ x∈xs, f x<0) : isum xs f<0 := by
 induction xs with
 | nil => simp at he
 | cons x xs ih =>
   have hx := h x (by simp)
   have ht : ∀ y∈xs, f y≤0 := by intro y hy; exact h y (by simp [hy])
   by_cases he' : ∃ y∈xs, f y<0
   · have hn := ih ht he'
     simp only [isum,List.map_cons,List.sum_cons] at *
     omega
   · have hz : ∀ y∈xs, f y=0 := by
       intro y hy
       have hle := ht y hy
       have hge : ¬f y<0 := by intro hn; exact he' ⟨y,hy,hn⟩
       omega
     have hs : isum xs f=0 := by
       unfold isum
       have hm : xs.map f=xs.map (fun _ => (0:Int)) := List.map_congr_left hz
       rw [hm]
       simp only [List.map_const',List.sum_replicate_int,Int.mul_zero]
     obtain ⟨y,hy,hn⟩ := he
     have hxy : y=x := by
       rcases List.mem_cons.mp hy with hy | hy
       · exact hy
       · have hh := hz y hy; omega
     subst y
     simp only [isum,List.map_cons,List.sum_cons] at *
     omega

def product (q : Nat) (K a : Nat → Nat) (r : Nat) : Nat :=
 Counting.sumBy (List.range (q+1)) (fun i => K i*(if i≤r then a (r-i) else 0))

theorem extended_sub (a : Nat → Nat) (r i : Nat) :
 extended a ((r:Int)-i)=((if i≤r then a (r-i) else 0:Nat):Int) := by
 by_cases h : i≤r
 · have hn : ¬(r:Int)-i<0 := by omega
   simp [extended,h,hn]
 · have hn : (r:Int)-i<0 := by omega
   simp [extended,h,hn]

theorem product_cast (q : Nat) (K a : Nat → Nat) (r : Nat) :
 (product q K a r:Int)=isum (List.range (q+1))
   (fun i => (K i:Int)*extended a ((r:Int)-i)) := by
 unfold product
 generalize List.range (q+1)=xs
 induction xs with
 | nil => simp [Counting.sumBy,isum]
 | cons i xs ih =>
   simp only [Counting.sumBy,isum,List.map_cons,List.sum_cons,Int.natCast_add] at *
   rw [ih,extended_sub]
   simp only [Int.natCast_mul]

theorem product_slope (q : Nat) (K a : Nat → Nat) (r : Nat) :
 (product q K a (r+1):Int)-(product q K a r:Int)=
 isum (List.range (q+1)) (fun i => (K i:Int)*slope a ((r:Int)-i)) := by
 rw [product_cast,product_cast]
 generalize List.range (q+1)=xs
 induction xs with
 | nil => simp [isum]
 | cons i xs ih =>
   simp only [isum,List.map_cons,List.sum_cons] at *
   have he : ((r+1:Nat):Int)-i=((r:Int)-i)+1 := by omega
   simp only [slope,he,Int.mul_sub] at *
   omega

/-- Full plateau-sensitive first-fall comparison for finite kernels.
 The inequalities are coefficient cross-products, with no division.
 Kernel/graph correspondence is a separate obligation at applications. -/
theorem first_fall_comparison (q lo hi : Nat) (K L a : Nat → Nat)
 (hhiq : hi≤q) (hlow : ∀ i, i<lo → K i=0)
 (hhigh : ∀ i, hi<i → L i=0)
 (hpos : ∀ i, lo≤i → i≤hi → 0<K i ∧ 0<L i)
 (hLhi : 0<L hi)
 (ratio : ∀ i j, lo≤i → i≤j → j≤hi → L j*K i≤L i*K j)
 (ua : Unimodal a) (m M N : Nat)
 (ha : FirstFall a m) (hK : FirstFall (product q K a) M)
 (hL : FirstFall (product q L a) N) : N≤M := by
 have lower : m+lo≤M := by
   by_cases hh : m+lo≤M
   · exact hh
   · have ht : ∀ i∈List.range (q+1), 0≤(K i:Int)*slope a ((M:Int)-i) := by
       intro i _
       by_cases hil : i<lo
       · rw [hlow i hil]; simp
       · have hs := slope_before a m ha ((M:Int)-i) (by omega)
         exact Int.mul_nonneg (by omega) hs
     have hs := isum_nonneg _ _ ht
     rw [←product_slope] at hs
     have hf := hK.1
     omega
 have upper : N≤m+hi := by
   have ht : ∀ i∈List.range (q+1), (L i:Int)*slope a (((m+hi:Nat):Int)-i)≤0 := by
     intro i _
     by_cases hii : hi<i
     · rw [hhigh i hii]; simp
     · have hs := slope_after a m ha ua (((m+hi:Nat):Int)-i) (by omega)
       exact Int.mul_nonpos_of_nonneg_of_nonpos (by omega) hs
   have hex : ∃ i∈List.range (q+1), (L i:Int)*slope a (((m+hi:Nat):Int)-i)<0 := by
     refine ⟨hi,List.mem_range.mpr (by omega),?_⟩
     have he : (((m+hi:Nat):Int)-hi)=(m:Int) := by omega
     rw [he,slope_nat]
     exact Int.mul_neg_of_pos_of_neg (by omega) (by have hh:=ha.1; omega)
   have hs := isum_negative _ _ ht hex
   rw [←product_slope] at hs
   exact fall_after_first _ N (m+hi) hL (by omega)
 by_cases hbound : m+hi≤M
 · omega
 · let t := M-m
   have htl : lo≤t := by dsimp [t]; omega
   have hth : t≤hi := by dsimp [t]; omega
   have hp := hpos t htl hth
   have left : ∀ i∈List.range (q+1), i≤t →
       slope a ((M:Int)-i)≤0 ∧ (L t:Int)*K i≤(K t:Int)*L i := by
     intro i _ hit
     constructor
     · exact slope_after a m ha ua ((M:Int)-i) (by dsimp [t] at hit; omega)
     · by_cases hil : i<lo
       · rw [hlow i hil]; simp; exact Int.mul_nonneg (by omega) (by omega)
       · have hh := ratio i t (by omega) hit hth
         have hc : (L t:Int)*K i≤(L i:Int)*K t := by exact_mod_cast hh
         simpa only [Int.mul_comm] using hc
   have right : ∀ i∈List.range (q+1), t<i →
       0≤slope a ((M:Int)-i) ∧ (K t:Int)*L i≤(L t:Int)*K i := by
     intro i _ hit
     constructor
     · exact slope_before a m ha ((M:Int)-i) (by dsimp [t] at hit; omega)
     · by_cases hii : hi<i
       · rw [hhigh i hii]; simp; exact Int.mul_nonneg (by omega) (by omega)
       · have hh := ratio t i htl (by omega) (by omega)
         have hc : (L i:Int)*K t≤(L t:Int)*K i := by exact_mod_cast hh
         simpa only [Int.mul_comm] using hc
   have hf : isum (List.range (q+1)) (fun i => (K i:Int)*slope a ((M:Int)-i))<0 := by
     rw [←product_slope]
     have hh := hK.1
     omega
   have hs := weighted_transfer (List.range (q+1)) (fun i => (K i:Int))
     (fun i => (L i:Int)) (fun i => slope a ((M:Int)-i)) t
     (by change 0<(K t:Int); omega) (by change 0<(L t:Int); omega) left right hf
   rw [←product_slope] at hs
   exact fall_after_first _ N M hL (by omega)

end Erdos993.KernelSlopeComparison
