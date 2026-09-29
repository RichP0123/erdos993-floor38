import TwoLeafPayment
namespace Erdos993.SupportBudget
open Counting Structure LeafBoundary EndPadding PaddingCounts

theorem support_curvature_budget {n : Nat} (G : Graph n) (hf : IsForest G)
 (l v z : Fin n) (hlv : l≠v) (hl : ∀u,G.adj l u=true ↔ u=v)
 (hz : z∈leafPairVertices l v) (ha : G.adj v z=true)
 (he : ∀u,G.adj v u=true → u≠z → ∀x y,G.adj u x=true → G.adj u y=true → x=y)
 (hs : 1≤(supportLeaves G l v z).length) (r : Nat) :
 2*((r:Int)+1)*(coefficient (inducedOn G (leafPairVertices l v)) (r+1):Int)+
 2*(((leafPairVertices l v).filter (fun u => !(G.adj v u))).length:Int)*
   ((supportLeaves G l v z).length:Int)*
   (pad ((supportLeaves G l v z).length-1)
     (coefficient (inducedOn G ((leafPairVertices l v).filter (fun u => !(G.adj v u))))) r:Int)≤
 ((((leafPairVertices l v).filter (fun u => !(G.adj v u))).length:Int)+1)*
   curvature (inducedOn G (leafPairVertices l v)) (r+1) := by
 let xs := leafPairVertices l v
 let p := fun u => G.adj v u && decide (u≠z)
 let s := (supportLeaves G l v z).length
 have hi : ∀u∈xs.filter p,∀x∈xs,G.adj u x=false := by
   intro u hu x hx
   have hp : G.adj v u=true ∧ u≠z := by simpa [p] using (List.mem_filter.mp hu).2
   have hxv : x≠v := ((List.Nodup.mem_erase_iff (deleteVertices_nodup l)).mp hx).1
   cases hh : G.adj u x
   · rfl
   · exact False.elim (hxv (he u hp.1 hp.2 x v hh (by rw [G.symm]; exact hp.1)))
 have hm : 1≤(xs.filter (fun u => !(p u))).length := by
   have hzm : z∈xs.filter (fun u => !(p u)) := by simp [xs,p,hz]
   exact List.length_pos_of_mem hzm
 have hsp : (xs.filter p).length=s := rfl
 have hb := InducedIsolate.induced_isolate_budget G hf xs (leafPair_nodup l v) p
   (fun u => !(G.adj v u)) hi (s-1) (by omega) hm r
 have hid : (xs.filter (fun u => !(p u))).filter (fun u => !(G.adj v u))=
     xs.filter (fun u => !(G.adj v u)) := by
   rw [List.filter_filter]
   apply List.filter_congr
   intro u hu
   dsimp [p]
   cases G.adj v u <;> simp
 rw [hid] at hb
 have hlen := filter_complement_lengths xs p
 have htotal := leafPair_length l v hlv
 have hq := leaf_closed_residual_length G l v hlv hl
 have hsl := support_leaves_length G l v z hlv hl hz ha
 have hmi : ((xs.filter (fun u => !(p u))).length:Int)=
     (((leafPairVertices l v).filter (fun u => !(G.adj v u))).length:Int)+1 := by
   dsimp [xs,s] at hsp hlen
   dsimp [xs]
   omega
 have hsi : ((s-1:Nat):Int)+1=(s:Int) := by omega
 rw [hmi,hsi] at hb
 dsimp [xs,s] at hb
 grind

theorem critical_two_leaf_small_curvature (w : Closure.CriticalWitness)
 (hn : w.n+1=4*w.M) (l v z : Fin w.n) (hlv : l≠v)
 (hl : ∀u,w.graph.adj l u=true ↔ u=v)
 (hz : z∈leafPairVertices l v) (ha : w.graph.adj v z=true)
 (he : ∀u,w.graph.adj v u=true → u≠z → ∀x y,w.graph.adj u x=true → w.graph.adj u y=true → x=y)
 (hs : (supportLeaves w.graph l v z).length=1)
 (hsmall : 3*(coefficient (inducedOn w.graph ((leafPairVertices l v).filter (fun u => !(w.graph.adj v u)))) (w.M-1):Int)≤
   4*curvature (inducedOn w.graph ((leafPairVertices l v).filter (fun u => !(w.graph.adj v u)))) (w.M-1)) : False := by
 let H := inducedOn w.graph (leafPairVertices l v)
 let Q := inducedOn w.graph ((leafPairVertices l v).filter (fun u => !(w.graph.adj v u)))
 let k := w.M-1
 have hmin := InteriorDegreeTwo.critical_order_above_half w
 have hk : 2≤k := by dsimp [k]; omega
 have hidx : k+1=w.M := by dsimp [k]; omega
 have hh := leafPair_length l v hlv
 have hq := leaf_closed_residual_length w.graph l v hlv hl
 have hsl := support_leaves_length w.graph l v z hlv hl hz ha
 have hf : IsForest H := inducedOn_isForest w.graph w.forest _ (leafPair_nodup l v)
 have hp := support_padding_lower w.graph l v z he k
 rw [hs] at hp
 have hback : k-1+1=k := by omega
 have hp' : coefficient Q k+coefficient Q (k-1)≤coefficient H k := by
   have hpp := pad_first_order 1 (coefficient Q) (k-1)
   rw [hback] at hpp
   have ht := Nat.le_trans hpp hp
   simpa using ht
 have hb := support_curvature_budget w.graph w.forest l v z hlv hl hz ha he (by omega) (k-1)
 rw [hs,hback] at hb
 simp only [pad] at hb
 have hqi : (((leafPairVertices l v).filter (fun u => !(w.graph.adj v u))).length:Int)=4*(k:Int)-1 := by dsimp [k]; omega
 have hki : ((k-1:Nat):Int)+1=(k:Int) := by omega
 rw [hqi,hki] at hb
 have hb' : 2*(k:Int)*(coefficient H k:Int)+2*(4*(k:Int)-1)*(coefficient Q (k-1):Int)≤4*(k:Int)*curvature H k := by grind
 have cert := TwoLeafPayment.two_leaf_slope_certificate H Q k hk (by dsimp [k]; omega)
   (by dsimp [k]; omega) hp' hb' hsmall
 have pre := forest_prefix_step H hf k (by dsimp [k]; omega)
 rw [hidx] at cert pre
 exact critical_leaf_certificate_impossible w l v hlv hl pre cert

end Erdos993.SupportBudget
