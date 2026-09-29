import RootedJointGrowth
namespace Erdos993.SeparatedRoot
open Counting CurvatureProof RootingBridgeAudit MarkedInjectionAudit ParentConstruction FiniteMarked

theorem parent_same_side {n : Nat} {G : Graph n} (R : ParentCertificate G)
 (p : Fin n → Bool) (hc : ∀u w,G.adj u w=true → p u=p w)
 (u w : Fin n) (h : R.parent u=some w) : p u=p w :=
 hc u w ((R.edges u w).mpr (Or.inl h))

def cutCertificate {n : Nat} {G : Graph n} (R T : ParentCertificate G)
 (p : Fin n → Bool) (hc : ∀u w,G.adj u w=true → p u=p w) : ParentCertificate G where
 parent := fun u => if p u then R.parent u else T.parent u
 edges := by
   intro u w
   by_cases he : p u=p w
   · cases hp : p u <;> have hw := he.symm.trans hp <;> simp only [hw,if_true]
     · exact T.edges u w
     · exact R.edges u w
   · have ha : G.adj u w=false := by
       cases hh : G.adj u w
       · rfl
       · exact False.elim (he (hc u w hh))
     have hRu : R.parent u≠some w := fun h => he (parent_same_side R p hc u w h)
     have hTu : T.parent u≠some w := fun h => he (parent_same_side T p hc u w h)
     have hRw : R.parent w≠some u := fun h => he (parent_same_side R p hc w u h).symm
     have hTw : T.parent w≠some u := fun h => he (parent_same_side T p hc w u h).symm
     cases p u <;> cases p w <;> simp [ha,hRu,hTu,hRw,hTw]
 noTwoCycle := by
   intro u w ⟨hu,hw⟩
   cases hp : p u
   · simp only [hp] at hu
     have he := parent_same_side T p hc u w hu
     have hq := he.symm.trans hp
     simp only [hq] at hw
     exact T.noTwoCycle u w ⟨hu,hw⟩
   · simp only [hp,if_true] at hu
     have he := parent_same_side R p hc u w hu
     have hq := he.symm.trans hp
     simp only [hq,if_true] at hw
     exact R.noTwoCycle u w ⟨hu,hw⟩

theorem pointed_two_roots {n : Nat} {G : Graph n} (R : ParentCertificate G)
 (u v : Fin n) (hu : R.parent u=none) (hv : R.parent v=none) (hne : u≠v) (r : Nat) :
 2*((inc G u r+inc G v r):Int)≤curvature G r := by
 have hb := sumBy_le (independentSets G r)
   (fun s => sumBy s (nonroot R)+(if u∈s then 1 else 0)+(if v∈s then 1 else 0))
   (fun _ => r) ?_
 · have hi (w : Fin n) : sumBy (independentSets G r) (fun s => if w∈s then 1 else 0)=inc G w r := by
     simpa [inc] using sumBy_indicator (independentSets G r) (fun s => s.contains w)
   rw [sumBy_add,sumBy_add,←target_length,hi,hi,sumBy_const,independentSets_length] at hb
   have hd := selected_degree_partition R r
   have hs := sources_le_targets R r
   have hn : sumBy (independentSets G r) (selectedDegree G)+2*(inc G u r+inc G v r)≤
       2*(r*coefficient G r) := by
     rw [Nat.mul_comm (coefficient G r) r] at hb
     omega
   have hh := Int.ofNat_le.mpr hn
   simp only [Int.natCast_add,Int.natCast_mul] at hh
   unfold curvature
   simp only [Int.mul_assoc]
   omega
 · intro s hs
   have hm := (mem_independentSets G r s).mp hs
   have hd := List.Sublist.nodup ((mem_subsets _ _).mp hm.1) (finRange_nodup n)
   have ht := sumBy_le s
     (fun w => nonroot R w+(if w=u then 1 else 0)+(if w=v then 1 else 0)) (fun _ => 1) ?_
   · rw [sumBy_add,sumBy_add,sumBy_equal_indicator s hd u,sumBy_equal_indicator s hd v,sumBy_const,hm.2.1] at ht
     simpa using ht
   · intro w hw
     by_cases heu : w=u
     · subst w; simp [nonroot,hu,hne]
     · by_cases hev : w=v
       · subst w; simp [nonroot,hv,Ne.symm hne]
       · simp only [heu,hev,if_false,Nat.add_zero,nonroot]
         split <;> omega

theorem forest_separated_pointed {n : Nat} (G : Graph n) (hf : IsForest G)
 (p : Fin n → Bool) (hc : ∀u w,G.adj u w=true → p u=p w)
 (u v : Fin n) (hu : p u=true) (hv : p v=false) (r : Nat) :
 2*((inc G u r+inc G v r):Int)≤curvature G r := by
 obtain ⟨R,hR⟩ := forest_parent_certificate G hf u
 obtain ⟨T,hT⟩ := forest_parent_certificate G hf v
 apply pointed_two_roots (cutCertificate R T p hc) u v
 · simp [cutCertificate,hu,hR]
 · simp [cutCertificate,hv,hT]
 · intro he; rw [he,hv] at hu; contradiction

theorem sum_scaled_bound {α : Type} (xs : List α) (f : α → Nat) (t c k : Int)
 (h : ∀x∈xs,t*(f x:Int)+c≤k) :
 t*(sumBy xs f:Int)+(xs.length:Int)*c≤(xs.length:Int)*k := by
 induction xs with
 | nil => simp
 | cons x xs ih =>
   have hx := h x (by simp)
   have ht := ih (by intro y hy; exact h y (by simp [hy]))
   simp only [sumBy_cons,List.length_cons,Int.natCast_add,Int.natCast_one,Int.add_mul,Int.mul_add,Int.one_mul]
   omega

theorem separation_budget (a b i j k : Int) (ha : 1≤a) (hb : 1≤b)
 (hi : 0≤i) (hj : 0≤j) (hk : 0≤k)
 (h : 2*b*i+2*a*j≤a*b*k) : 2*(i+j)≤(a+b-1)*k := by
 have half (a b i j : Int) (ha : 1≤a) (hab : a≤b) (hi : 0≤i)
     (h : 2*b*i+2*a*j≤a*b*k) : 2*(i+j)≤(a+b-1)*k := by
   have h1 := Int.mul_nonneg (show 0≤b-a by omega) hi
   have h2 := Int.mul_nonneg (show 0≤a-1 by omega) hk
   have h3 := Int.mul_le_mul_of_nonneg_left (show b*k≤(a+b-1)*k by grind) (show 0≤a by omega)
   have hh : a*(2*(i+j))≤a*((a+b-1)*k) := by grind
   exact Int.le_of_mul_le_mul_left hh (by omega)
 by_cases hab : a≤b
 · exact half a b i j ha hab hi h
 · have h' : 2*a*j+2*b*i≤b*a*k := by grind
   have ht := half b a j i hb (by omega) hj h'
   grind

theorem forest_cut_curvature {n : Nat} (G : Graph n) (hf : IsForest G)
 (p : Fin n → Bool) (hc : ∀u w,G.adj u w=true → p u=p w)
 (hyes : ∃u,p u=true) (hno : ∃v,p v=false) (r : Nat) :
 2*(r:Int)*(coefficient G r:Int)≤((n:Int)-1)*curvature G r := by
 let a := (List.finRange n).filter p
 let b := (List.finRange n).filter (fun v => !(p v))
 have hab : a.length+b.length=n := by
   simpa [a,b] using LeafBoundary.filter_complement_lengths (List.finRange n) p
 have ha : 1≤a.length := by
   obtain ⟨u,hu⟩ := hyes
   have hm : u∈a := by simp [a,hu]
   exact List.length_pos_of_mem hm
 have hb : 1≤b.length := by
   obtain ⟨v,hv⟩ := hno
   have hm : v∈b := by simp [b,hv]
   exact List.length_pos_of_mem hm
 have hp : ∀u∈a,2*(b.length:Int)*(inc G u r:Int)+2*(sumBy b (fun v => inc G v r):Int)≤
     (b.length:Int)*curvature G r := by
   intro u hu
   have hh := sum_scaled_bound b (fun v => inc G v r) 2 (2*(inc G u r:Int)) (curvature G r) ?_
   · grind
   · intro v hv
     have hu' : p u=true := (List.mem_filter.mp hu).2
     have hv' : p v=false := by simpa using (List.mem_filter.mp hv).2
     have hh := forest_separated_pointed G hf p hc u v hu' hv' r
     grind
 have hh := sum_scaled_bound a (fun u => inc G u r) (2*(b.length:Int))
   (2*(sumBy b (fun v => inc G v r):Int)) ((b.length:Int)*curvature G r) hp
 have he : sumBy a (fun u => inc G u r)+sumBy b (fun v => inc G v r)=r*coefficient G r := by
   rw [IsolateCurvature.sum_inc_filter,IsolateCurvature.sum_inc_filter]
   exact IsolateCurvature.isolated_inc_partition G p r
 have ht := separation_budget (a.length:Int) (b.length:Int)
   (sumBy a (fun u => inc G u r):Int) (sumBy b (fun v => inc G v r):Int) (curvature G r)
   (by omega) (by omega) (Int.natCast_nonneg _) (Int.natCast_nonneg _) (forest_curvature_nonnegative G hf r)
   (by grind)
 have hei := congrArg Int.ofNat he
 have habi := congrArg Int.ofNat hab
 grind

end Erdos993.SeparatedRoot
