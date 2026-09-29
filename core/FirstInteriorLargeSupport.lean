import InteriorPaddingCertificate
namespace Erdos993.InteriorLargeSupport
open Counting Structure LeafBoundary EndPadding PaddingCounts

theorem critical_first_interior_large_support (w : Closure.CriticalWitness)
 (hn : w.n+1=4*w.M) (l v z : Fin w.n) (hlv : l≠v)
 (hl : ∀u,w.graph.adj l u=true ↔ u=v)
 (hz : z∈leafPairVertices l v) (ha : w.graph.adj v z=true)
 (he : ∀u,w.graph.adj v u=true → u≠z →
   ∀x y,w.graph.adj u x=true → w.graph.adj u y=true → x=y)
 (hs : 2≤(supportLeaves w.graph l v z).length) : False := by
 let xs := leafPairVertices l v
 let p := fun u => w.graph.adj v u && decide (u≠z)
 let s := (supportLeaves w.graph l v z).length
 let k := w.M-1
 let H := inducedOn w.graph xs
 let Q := inducedOn w.graph (xs.filter (fun u => !(w.graph.adj v u)))
 have hx : xs.Nodup := leafPair_nodup l v
 have hf : IsForest H := inducedOn_isForest w.graph w.forest xs hx
 have qf : IsForest Q := inducedOn_isForest w.graph w.forest _ (List.Sublist.nodup List.filter_sublist hx)
 have horder := leafPair_length l v hlv
 have hqorder := leaf_closed_residual_length w.graph l v hlv hl
 have hsorder := support_leaves_length w.graph l v z hlv hl hz ha
 have hmin := InteriorDegreeTwo.critical_order_above_half w
 have hk : 2≤k := by dsimp [k]; omega
 have hkidx : k+1=w.M := by dsimp [k]; omega
 have hnH : xs.length=4*k+1 := by dsimp [xs,k]; omega
 have hnQ : (xs.filter (fun u => !(w.graph.adj v u))).length+s=4*k := by dsimp [xs,s,k]; omega
 have hsp : (xs.filter p).length=s := rfl
 have hi : ∀u∈xs.filter p,∀x∈xs,w.graph.adj u x=false := by
   intro u hu x hx'
   have hp' : w.graph.adj v u=true ∧ u≠z := by simpa [p] using (List.mem_filter.mp hu).2
   have hxv : x≠v := ((List.Nodup.mem_erase_iff (deleteVertices_nodup l)).mp hx').1
   cases hh : w.graph.adj u x
   · rfl
   · exact False.elim (hxv (he u hp'.1 hp'.2 x v hh (by rw [w.graph.symm]; exact hp'.1)))
 have hm : 1≤(xs.filter (fun u => !(p u))).length := by
   have hz' : z∈xs.filter (fun u => !(p u)) := by simp [xs,p,hz]
   exact List.length_pos_of_mem hz'
 have hid : (xs.filter (fun u => !(p u))).filter (fun u => !(w.graph.adj v u))=
     xs.filter (fun u => !(w.graph.adj v u)) := by
   rw [List.filter_filter]
   apply List.filter_congr
   intro u hu
   dsimp [p]
   cases w.graph.adj v u <;> simp
 have hb := InducedIsolate.induced_isolate_budget w.graph w.forest xs hx p
     (fun u => !(w.graph.adj v u)) hi (s-1) (by omega) hm (k-1)
 rw [hid] at hb
 have hmorder := filter_complement_lengths xs p
 have hmi : ((xs.filter (fun u => !(p u))).length:Int)=4*(k:Int)+1-(s:Int) := by omega
 have hki : ((k-1:Nat):Int)+1=(k:Int) := by omega
 have hsi : ((s-1:Nat):Int)+1=(s:Int) := by omega
 have hkr : k-1+1=k := by omega
 rw [hkr,hmi,hki,hsi] at hb
 have hb' : 2*(k:Int)*(coefficient H k:Int)+2*(4*(k:Int)-(s:Int))*(s:Int)*
     (pad (s-1) (coefficient Q) (k-1):Int)≤(4*(k:Int)+1-(s:Int))*curvature H k := by grind
 have hcert := InteriorPadding.interior_padding_certificate H Q hf qf k s hk hs hnH hnQ
   (support_padding_lower w.graph l v z he) hb'
 have hpre := forest_prefix_step H hf k (by omega)
 rw [hkidx] at hcert hpre
 exact critical_leaf_certificate_impossible w l v hlv hl hpre hcert

end Erdos993.InteriorLargeSupport
