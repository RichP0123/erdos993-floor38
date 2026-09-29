import DegreeNeighborTools
namespace Erdos993.InteriorLongPath
open Counting Structure LeafBoundary EndPadding EndSupport ActualComponents NeighborTools

theorem critical_long_path_impossible {j : Nat} (w : Closure.CriticalWitness)
 (hn : w.n+1=4*w.M) (p : SimplePath w.graph (j+3))
 (hmax : ∀k,Nonempty (SimplePath w.graph k) → k≤j+3) : False := by
 classical
 let l := p.vertex ⟨0,by omega⟩
 let v := p.vertex ⟨1,by omega⟩
 let z := p.vertex ⟨2,by omega⟩
 let t := p.vertex ⟨3,by omega⟩
 have hdif (a b : Fin (j+3+1)) (h : a.val≠b.val) : p.vertex a≠p.vertex b := by
   intro he; exact h (congrArg Fin.val (p.injective a b he))
 have hlv : l≠v := hdif _ _ (by dsimp; omega)
 have hzl : z≠l := hdif _ _ (by dsimp; omega)
 have hzv : z≠v := hdif _ _ (by dsimp; omega)
 have htl : t≠l := hdif _ _ (by dsimp; omega)
 have htv : t≠v := hdif _ _ (by dsimp; omega)
 have hzt : z≠t := hdif _ _ (by dsimp; omega)
 have hal : w.graph.adj l v=true := p.consecutive ⟨0,by omega⟩
 have haz : w.graph.adj v z=true := p.consecutive ⟨1,by omega⟩
 have hat : w.graph.adj z t=true := p.consecutive ⟨2,by omega⟩
 have hend := longest_path_endpoint_leaf w.forest p hmax
 have hl : ∀u,w.graph.adj l u=true ↔ u=v := by
   intro u; exact ⟨fun hu => hend u v hu hal,fun hu => hu ▸ hal⟩
 have hz : z∈leafPairVertices l v := by
   simp [leafPairVertices,deleteVertices,List.mem_erase_of_ne hzv,List.mem_erase_of_ne hzl]
 have he : ∀u,w.graph.adj v u=true → u≠z → ∀x y,w.graph.adj u x=true → w.graph.adj u y=true → x=y :=
   fun u hu hne => longest_path_end_support w.forest p hmax u hu hne
 have hdv : degree w.graph v=3 := NextSupport.critical_longest_end_degree_three w hn p hmax
 have hs : (supportLeaves w.graph l v z).length=1 := by
   have hh := support_leaves_length w.graph l v z hlv hl hz haz
   omega
 let qs := (leafPairVertices l v).filter (fun u => !(w.graph.adj v u))
 have qnd : qs.Nodup := List.Sublist.nodup List.filter_sublist (leafPair_nodup l v)
 have hqorder : qs.length+1=4*(w.M-1) := by
   have hh := leaf_closed_residual_length w.graph l v hlv hl
   have hm := w.positiveFallIndex
   dsimp [qs]; omega
 have hk : 2≤w.M-1 := by have hh := InteriorDegreeTwo.critical_order_above_half w; omega
 have hzout : z∉qs := by simp [qs,haz]
 by_cases hdz : degree w.graph z≤2
 · have hneigh := degree_two_neighbors w.graph z v t (by rw [w.graph.symm]; exact haz) hat (Ne.symm htv) hdz
   let cs := SupportCore.coreVertices w.graph l v z
   have hzcs : z∈cs := SupportCore.core_contains_continuation w.graph l v z hz
   have hvt : w.graph.adj v t=false := forest_no_triangle w.graph w.forest v z t haz hat (Ne.symm htv)
   have htcs : t∈cs := by
     simp [cs,SupportCore.coreVertices,leafPairVertices,deleteVertices,List.mem_erase_of_ne htv,List.mem_erase_of_ne htl,hvt]
   have cnd : cs.Nodup := List.Sublist.nodup List.filter_sublist (leafPair_nodup l v)
   let iz := index cs z hzcs
   let it := index cs t htcs
   have hiz : cs[iz.val]=z := index_label cs z hzcs
   have hit : cs[it.val]=t := index_label cs t htcs
   apply LeafContinuation.critical_two_leaf_leaf_core w hn l v z hlv hl hz haz he hs iz it hiz
   · intro hi
     exact hzt (hiz.symm.trans ((congrArg (fun a : Fin cs.length => cs[a.val]) hi).trans hit))
   · intro u
     change w.graph.adj cs[iz.val] cs[u.val]=true ↔ u=it
     rw [hiz,hneigh]
     have huv : cs[u.val]≠v := by
       have hu : cs[u.val]∈leafPairVertices l v := (List.mem_filter.mp (List.getElem_mem u.isLt)).1
       exact ((List.Nodup.mem_erase_iff (deleteVertices_nodup l)).mp hu).1
     simp only [huv,false_or]
     exact label_eq_index cs cnd t htcs u
 · obtain ⟨u,hu,huv,hut⟩ : ∃u,w.graph.adj z u=true ∧ u≠v ∧ u≠t := by
     by_cases hh : ∃u,w.graph.adj z u=true ∧ u≠v ∧ u≠t
     · exact hh
     · have hd := degree_bound_by_list w.graph z [v,t] (by simp [Ne.symm htv]) ?_
       · simp only [List.length_cons,List.length_nil] at hd
         exact False.elim (hdz hd)
       · intro u hu
         by_cases huv : u=v
         · simp [huv]
         · by_cases hut : u=t
           · simp [hut]
           · exact False.elim (hh ⟨u,hu,huv,hut⟩)
   have huz : u≠z := by intro hh; subst u; rw [w.graph.loopless] at hu; contradiction
   have hvu : w.graph.adj v u=false := forest_no_triangle w.graph w.forest v z u haz hu (Ne.symm huv)
   have hul : u≠l := by
     intro hh; subst u
     have ht := (hl z).mp (by rw [w.graph.symm]; exact hu)
     exact hzv ht
   have hum : u∈qs := by
     simp [qs,leafPairVertices,deleteVertices,List.mem_erase_of_ne huv,List.mem_erase_of_ne hul,hvu]
   have hsmall : 3*(coefficient (inducedOn w.graph qs) (w.M-1):Int)≤4*curvature (inducedOn w.graph qs) (w.M-1) := by
     by_cases hex : ∃a,w.graph.adj u a=true ∧ a≠z
     · obtain ⟨a0,ha0,ha0z⟩ := hex
       have hsup := NextSupport.critical_next_support w hn p hmax u a0 hu hut ha0 ha0z
       obtain ⟨a,b,hab,haz',hbz,hun⟩ := degree_three_neighbors w.graph u z (by rw [w.graph.symm]; exact hu) hsup.1
       have hal' : w.graph.adj u a=true := (hun a).mpr (Or.inr (Or.inl rfl))
       have hbl' : w.graph.adj u b=true := (hun b).mpr (Or.inr (Or.inr rfl))
       have leaf_exact (a : Fin w.n) (haa : w.graph.adj u a=true) (haz' : a≠z) :
           ∀x,w.graph.adj a x=true ↔ x=u := by
         intro x
         exact ⟨fun h => hsup.2 a haa haz' x u h (by rw [w.graph.symm]; exact haa),fun h => by rw [h,w.graph.symm]; exact haa⟩
       have hla := leaf_exact a hal' haz'
       have hlb := leaf_exact b hbl' hbz
       have leaf_mem (a : Fin w.n) (hla : ∀x,w.graph.adj a x=true ↔ x=u) : a∈qs := by
         have hav : a≠v := by
           intro hh; subst a
           exact huz ((hla z).mp haz).symm
         have hal : a≠l := by
           intro hh; subst a
           exact huv ((hla v).mp hal).symm
         have hno : w.graph.adj v a=false := by
           cases hh : w.graph.adj v a
           · rfl
           · exact False.elim (huv ((hla v).mp (by rw [w.graph.symm]; exact hh)).symm)
         simp [qs,leafPairVertices,deleteVertices,List.mem_erase_of_ne hav,List.mem_erase_of_ne hal,hno]
       have hau : a≠u := by intro hh; subst a; rw [w.graph.loopless] at hal'; contradiction
       have hub : u≠b := by intro hh; subst b; rw [w.graph.loopless] at hbl'; contradiction
       apply induced_p3_curvature w.graph w.forest qs qnd a u b (leaf_mem a hla) hum (leaf_mem b hlb) hau hab hub
       · intro x hx; exact hla x
       · intro x hx; exact hlb x
       · intro x hx
         rw [hun]
         have hxz : x≠z := by intro hh; subst x; exact hzout hx
         simp [hxz]
       · exact hk
       · exact hqorder
     · apply induced_isolate_curvature w.graph w.forest qs qnd u hum
       · intro x hx
         cases hh : w.graph.adj u x
         · rfl
         · have hxz : x≠z := by intro ht; subst x; exact hzout hx
           exact False.elim (hex ⟨x,hh,hxz⟩)
       · exact hk
       · exact hqorder
   exact SupportBudget.critical_two_leaf_small_curvature w hn l v z hlv hl hz haz he hs hsmall

end Erdos993.InteriorLongPath

