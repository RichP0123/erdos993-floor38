import FirstInteriorLongPath
namespace Erdos993.InteriorExclusion
open Counting Structure LeafBoundary EndPadding EndSupport

theorem critical_first_interior_excluded (w : Closure.CriticalWitness) : w.n+1≠4*w.M := by
 intro hn
 have hnpos : 0<w.n := by
   have hh := InteriorDegreeTwo.critical_order_above_half w
   omega
 obtain ⟨L,p,hmax⟩ := exists_longest_path w.graph hnpos
 cases L with
 | zero =>
   let v : Fin w.n := ⟨0,hnpos⟩
   apply LinearFactor.critical_has_no_isolate w v
   intro u
   cases he : w.graph.adj v u
   · rfl
   · obtain ⟨i,hi⟩ := longest_path_neighbor_present (singletonPath w.graph v) hmax u he
     have huv : u=v := hi
     rw [huv,w.graph.loopless] at he
     contradiction
 | succ L =>
   cases L with
   | zero =>
     let l := p.vertex ⟨0,by omega⟩
     let v := p.vertex ⟨1,by omega⟩
     have hlv : l≠v := by
       intro hh
       have hh := congrArg Fin.val (p.injective _ _ hh)
       contradiction
     have ha : w.graph.adj l v=true := p.consecutive ⟨0,by omega⟩
     have he := longest_path_endpoint_leaf w.forest p hmax
     have hv := longest_path_endpoint_leaf w.forest (reversePath p) hmax
     have hv' : ∀u z,w.graph.adj v u=true → w.graph.adj v z=true → u=z := by
       simpa [reversePath,Fin.rev,v] using hv
     apply LinearFactor.critical_has_no_edge_component w l v hlv
     · intro u; exact ⟨fun hu => he u v hu ha,fun hu => hu ▸ ha⟩
     · intro u
       have hh : w.graph.adj v l=true := by rw [w.graph.symm]; exact ha
       exact ⟨fun hu => hv' u l hu hh,fun hu => hu ▸ hh⟩
   | succ L =>
     cases L with
     | zero =>
       let l := p.vertex ⟨0,by omega⟩
       let v := p.vertex ⟨1,by omega⟩
       let z := p.vertex ⟨2,by omega⟩
       have hdif (a b : Fin 3) (h : a.val≠b.val) : p.vertex a≠p.vertex b := by
         intro he; exact h (congrArg Fin.val (p.injective a b he))
       have hlv : l≠v := hdif _ _ (by dsimp; omega)
       have hzl : z≠l := hdif _ _ (by dsimp; omega)
       have hzv : z≠v := hdif _ _ (by dsimp; omega)
       have hal : w.graph.adj l v=true := p.consecutive ⟨0,by omega⟩
       have haz : w.graph.adj v z=true := p.consecutive ⟨1,by omega⟩
       have hend := longest_path_endpoint_leaf w.forest p hmax
       have hl : ∀u,w.graph.adj l u=true ↔ u=v := by
         intro u; exact ⟨fun hu => hend u v hu hal,fun hu => hu ▸ hal⟩
       have hz : z∈leafPairVertices l v := by
         simp [leafPairVertices,deleteVertices,List.mem_erase_of_ne hzv,List.mem_erase_of_ne hzl]
       have hzend := longest_path_endpoint_leaf w.forest (reversePath p) hmax
       have hzleaf : ∀x y,w.graph.adj z x=true → w.graph.adj z y=true → x=y := by
         simpa [reversePath,Fin.rev,z] using hzend
       have he : ∀u,w.graph.adj v u=true → ∀x y,w.graph.adj u x=true → w.graph.adj u y=true → x=y := by
         intro u hu
         by_cases huz : u=z
         · rw [huz]; exact hzleaf
         · exact longest_path_end_support w.forest p hmax u hu huz
       have hdv : degree w.graph v=3 := NextSupport.critical_longest_end_degree_three w hn p hmax
       have hs : (supportLeaves w.graph l v z).length=1 := by
         have hh := support_leaves_length w.graph l v z hlv hl hz haz
         omega
       exact StarSupport.critical_star_support w hn l v z hlv hl hz haz he hs
     | succ j => exact InteriorLongPath.critical_long_path_impossible w hn p hmax

theorem critical_size_bound_verified : Extraction.CriticalSizeBound := by
 intro w
 have hq := QuarterExclusion.critical_after_quarter w
 have hi := critical_first_interior_excluded w
 omega

theorem critical_classification_verified : Closure.CriticalClassification :=
 Extraction.classification_of_size_bound critical_size_bound_verified

end Erdos993.InteriorExclusion

