import LeafContinuationPayment
namespace Erdos993.StarSupport
open Counting Structure CurvatureProof LeafBoundary EndPadding PaddingCounts

theorem twice_isolate_payment (k h q x : Int) (hk : 2≤k) (hq : 0≤q)
 (hh : 4*q≤3*h) (hx : 6*k*h≤(4*k+1)*x) : 3*q≤2*x := by
 have h1 := Int.mul_le_mul_of_nonneg_left hh (show 0≤12*k by omega)
 have h2 := Int.mul_le_mul_of_nonneg_left hx (show 0≤(6:Int) by omega)
 have h3 := Int.mul_nonneg (show 0≤12*k-9 by omega) hq
 have ht : (3*(4*k+1))*(3*q)≤(3*(4*k+1))*(2*x) := by grind
 exact Int.le_of_mul_le_mul_left ht (by omega)

theorem critical_star_support (w : Closure.CriticalWitness)
 (hn : w.n+1=4*w.M) (l v z : Fin w.n) (hlv : l≠v)
 (hl : ∀u,w.graph.adj l u=true ↔ u=v)
 (hz : z∈leafPairVertices l v) (ha : w.graph.adj v z=true)
 (he : ∀u,w.graph.adj v u=true → ∀x y,w.graph.adj u x=true → w.graph.adj u y=true → x=y)
 (hs : (supportLeaves w.graph l v z).length=1) : False := by
 let xs := leafPairVertices l v
 let H := inducedOn w.graph xs
 let Q := inducedOn w.graph (xs.filter (fun u => !(w.graph.adj v u)))
 let k := w.M-1
 let p := fun i : Fin xs.length => w.graph.adj v xs[i.val]
 have hmin := InteriorDegreeTwo.critical_order_above_half w
 have hk : 2≤k := by dsimp [k]; omega
 have hh := leafPair_length l v hlv
 have hq := leaf_closed_residual_length w.graph l v hlv hl
 have hd := support_leaves_length w.graph l v z hlv hl hz ha
 have hf : IsForest H := inducedOn_isForest w.graph w.forest xs (leafPair_nodup l v)
 have qf : IsForest Q := inducedOn_isForest w.graph w.forest _ (List.Sublist.nodup List.filter_sublist (leafPair_nodup l v))
 have hp2 : ((List.finRange xs.length).filter p).length=2 := by
   rw [InducedIsolate.induced_filter_length xs (fun u => w.graph.adj v u)]
   have ht := filter_complement_lengths xs (fun u => w.graph.adj v u)
   dsimp [xs] at ht
   dsimp [xs]
   omega
 have hpi : ∀i,p i=true → ∀j,H.adj i j=false := by
   intro i hi j
   have hj : xs[j.val]≠v := ((List.Nodup.mem_erase_iff (deleteVertices_nodup l)).mp (List.getElem_mem _)).1
   cases h : w.graph.adj xs[i.val] xs[j.val]
   · exact h
   · exact False.elim (hj (he xs[i.val] hi xs[j.val] v h (by rw [w.graph.symm]; exact hi)))
 have hcurv := MultipleIsolate.forest_multiple_isolate_bound H hf p hpi (by rw [hp2]; dsimp [xs]; dsimp [k] at hk; omega) k
 rw [hp2] at hcurv
 have hp := support_padding_lower w.graph l v z (fun u hu _ => he u hu) k
 rw [hs] at hp
 have hidx : k-1+1=k := by omega
 have hpad := pad_first_order 1 (coefficient Q) (k-1)
 rw [hidx] at hpad
 have hhpad := Nat.le_trans hpad hp
 have hext := graph_extension_upper_add Q (k-1)
 rw [hidx] at hext
 have hei := Int.ofNat_le.mpr hext
 have hki : ((k-1:Nat):Int)=(k:Int)-1 := by omega
 have hnqi : ((xs.filter (fun u => !(w.graph.adj v u))).length:Int)=4*(k:Int)-1 := by dsimp [xs,k]; omega
 have hnhi : (xs.length:Int)=4*(k:Int)+1 := by dsimp [xs,k]; omega
 simp only [Int.natCast_add,Int.natCast_mul,hki,hnqi] at hei
 have hback : (coefficient Q k:Int)≤3*(coefficient Q (k-1):Int) := by
   have ht : (k:Int)*(coefficient Q k:Int)≤(k:Int)*(3*(coefficient Q (k-1):Int)) := by grind
   exact Int.le_of_mul_le_mul_left ht (by omega)
 have hpadint := Int.ofNat_le.mpr hhpad
 have hx := twice_isolate_payment (k:Int) (coefficient H k:Int) (coefficient Q k:Int) (curvature H k)
   (by omega) (Int.natCast_nonneg _) (by grind) (by rw [hnhi] at hcurv; grind)
 have hqc := forest_curvature_bound Q qf k
 have hqn := forest_curvature_nonnegative Q qf k
 have hqscale := Int.mul_le_mul_of_nonneg_right (show ((xs.filter (fun u => !(w.graph.adj v u))).length:Int)≤4*(k:Int) by omega) hqn
 have hy : (coefficient Q k:Int)≤2*curvature Q k := by
   have ht : (2*(k:Int))*(coefficient Q k:Int)≤(2*(k:Int))*(2*curvature Q k) := by grind
   exact Int.le_of_mul_le_mul_left ht (by omega)
 have cert := LeafContinuation.curvature_sum_slope H Q k (by omega) (by omega) (by omega)
 have pre := forest_prefix_step H hf k (by omega)
 have hM : k+1=w.M := by dsimp [k]; omega
 rw [hM] at cert pre
 exact critical_leaf_certificate_impossible w l v hlv hl pre cert

end Erdos993.StarSupport
