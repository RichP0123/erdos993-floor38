import QuarterPaddingCertificate
namespace Erdos993.QuarterExclusion
open Counting Structure LeafBoundary EndSupport EndPadding QuarterCertificate CurvatureProof

theorem critical_edgeless_quarter_impossible (w : Closure.CriticalWitness)
 (hn : w.n=4*w.M) (he : ∀ u v, w.graph.adj u v=false) : False := by
 have hg := graph_degree_growth w.graph w.M
 have hz : sumBy (independentSets w.graph w.M) (selectedDegree w.graph)=0 := by
   have hd : degree w.graph=(fun _ => 0) := by funext v; simp [degree,he]
   have hs : selectedDegree w.graph=(fun _ => 0) := by
     funext s
     unfold selectedDegree
     rw [hd,sumBy_zero]
   rw [hs,sumBy_zero]
 rw [hz,Nat.add_zero] at hg
 have hm := Nat.mul_lt_mul_of_pos_left w.firstFall (show 0<w.M+1 by omega)
 have hb := Nat.mul_le_mul_right (coefficient w.graph w.M)
   (show w.M+1+w.M≤w.n by have := w.positiveFallIndex; omega)
 simp only [Nat.add_mul,Nat.one_mul] at hb hm hg
 omega

/-- Complete actual-graph exclusion of the quarter boundary. The proof uses
 global curvature, a longest path and actual isolate counts, including forests
 consisting only of star components. No component-product U theorem is assumed. -/
theorem critical_quarter_boundary_excluded (w : Closure.CriticalWitness) : w.n≠4*w.M := by
 intro hn
 have hpos : 0<w.n := by have := w.positiveFallIndex; omega
 obtain ⟨L,p,hmax⟩ := exists_longest_path w.graph hpos
 cases L with
 | zero =>
   apply critical_edgeless_quarter_impossible w hn
   intro u v
   cases he : w.graph.adj u v with
   | false => rfl
   | true =>
     obtain ⟨i,hi⟩ := longest_path_neighbor_present (singletonPath w.graph u) hmax v he
     change v=u at hi
     rw [hi,w.graph.loopless] at he
     contradiction
 | succ L =>
   let l := p.vertex ⟨0,by omega⟩
   let v := p.vertex ⟨1,by omega⟩
   have hlv : l≠v := by
     intro he
     have hh := congrArg Fin.val (p.injective _ _ he)
     simp at hh
   have ha : w.graph.adj l v=true := p.consecutive ⟨0,by omega⟩
   have hend := longest_path_endpoint_leaf w.forest p hmax
   have hl : ∀ u, w.graph.adj l u=true ↔ u=v := by
     intro u
     constructor
     · intro hu; exact hend u v hu ha
     · intro hu; rw [hu]; exact ha
   by_cases hd : degree w.graph v≤3
   · exact critical_quarter_leaf_degree_three_impossible w hn l v hlv hl hd
   · cases L with
     | zero =>
       have hv : degree w.graph v≤1 := by
         have ht := longest_path_endpoint_leaf w.forest (reversePath p) hmax
         have hh := degree_le_one w.graph ((reversePath p).vertex ⟨0,by omega⟩) ht
         exact hh
       omega
     | succ L =>
       let z := p.vertex ⟨2,by omega⟩
       have hzv : z≠v := by
         intro he
         have hh := congrArg Fin.val (p.injective _ _ he)
         simp at hh
       have hzl : z≠l := by
         intro he
         have hh := congrArg Fin.val (p.injective _ _ he)
         simp at hh
       have hz : z∈leafPairVertices l v := by
         unfold leafPairVertices
         rw [List.mem_erase_of_ne hzv]
         simp [deleteVertices,List.mem_erase_of_ne hzl]
       have haz : w.graph.adj v z=true := p.consecutive ⟨1,by omega⟩
       have hs := support_leaves_length w.graph l v z hlv hl hz haz
       have hp := support_padding_lower w.graph l v z
         (fun u hu hne => longest_path_end_support w.forest p hmax u hu hne)
       let H := inducedOn w.graph (leafPairVertices l v)
       let Q := inducedOn w.graph ((leafPairVertices l v).filter (fun u => !(w.graph.adj v u)))
       have hf : IsForest H := inducedOn_isForest w.graph w.forest _ (leafPair_nodup l v)
       have qf : IsForest Q := inducedOn_isForest w.graph w.forest _
         (List.Sublist.nodup List.filter_sublist (leafPair_nodup l v))
       have hh := leafPair_length l v hlv
       have hq := leaf_closed_residual_length w.graph l v hlv hl
       have cert := quarter_padding_certificate H Q hf qf w.M (supportLeaves w.graph l v z).length
         (by omega) (by omega) (by omega) hp
       have pref := forest_prefix_step H hf (w.M-1) (by have := w.positiveFallIndex; omega)
       have hi : w.M-1+1=w.M := by have := w.positiveFallIndex; omega
       rw [hi] at pref
       exact critical_leaf_certificate_impossible w l v hlv hl pref cert

theorem critical_after_quarter (w : Closure.CriticalWitness) : w.n+1≤4*w.M := by
 have h1 := critical_quarter_bound w
 have h2 := critical_quarter_boundary_excluded w
 omega

end Erdos993.QuarterExclusion
