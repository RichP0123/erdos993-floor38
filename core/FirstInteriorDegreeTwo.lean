import NestedVertexDeletion
namespace Erdos993.InteriorDegreeTwo
open Counting Structure LeafBoundary

theorem graph_half_tail {n : Nat} (G : Graph n) (r : Nat) (hn : n≤2*r+1) :
 coefficient G (r+1)≤coefficient G r := by
 have h := graph_extension_upper_add G r
 have hb := Nat.mul_le_mul_right (coefficient G r) hn
 have ht : (r+1)*coefficient G (r+1)≤(r+1)*coefficient G r := by grind
 exact Nat.le_of_mul_le_mul_left ht (by omega)

theorem critical_order_above_half (w : Closure.CriticalWitness) : 2*w.M+4≤w.n := by
 by_cases hn : w.n≤2*w.b+1
 · have h := graph_half_tail w.graph w.b hn
   have hr := w.returningRise
   omega
 · have hb := w.returnAfterFall
   omega

theorem short_list_members_eq {α : Type} (xs : List α) (h : xs.length≤1)
 (u v : α) (hu : u∈xs) (hv : v∈xs) : u=v := by
 cases xs with
 | nil => simp at hu
 | cons a xs =>
   have hz : xs=[] := by cases xs <;> simp_all
   subst xs
   simp only [List.mem_singleton] at hu hv
   exact hu.trans hv.symm

theorem residual_neighbor_unique {n : Nat} (G : Graph n) (l v z : Fin n)
 (hl : G.adj v l=true) (hz : G.adj v z=true) (hzl : z≠l) (hd : degree G v≤2) :
 ∀u,u∈leafPairVertices l v → (G.adj v u=true ↔ u=z) := by
 let ns := ((List.finRange n).filter (fun u => G.adj v u)).erase l
 have hlm : l∈(List.finRange n).filter (fun u => G.adj v u) := by simp [hl]
 have hlen : ns.length≤1 := by
   have h := List.length_erase_of_mem hlm
   change (((List.finRange n).filter (fun u => G.adj v u)).erase l).length≤1
   unfold degree at hd
   omega
 have hzm : z∈ns := by simp [ns,List.mem_erase_of_ne hzl,hz]
 intro u hu
 constructor
 · intro hau
   have hul : u≠l := by
     intro he
     have hm : l∈deleteVertices l := by
       subst u; exact List.mem_of_mem_erase hu
     exact (List.Nodup.not_mem_erase (finRange_nodup n)) hm
   have hum : u∈ns := by simp [ns,List.mem_erase_of_ne hul,hau]
   exact short_list_members_eq ns hlen u z hum hzm
 · intro he; rw [he]; exact hz

theorem critical_first_interior_degree_two (w : Closure.CriticalWitness)
 (hn : w.n+1=4*w.M) (l v : Fin w.n) (hlv : l≠v)
 (hl : ∀u,w.graph.adj l u=true ↔ u=v) (hd : degree w.graph v≤2) : False := by
 classical
 have hal : w.graph.adj v l=true := by rw [w.graph.symm]; exact (hl v).mpr rfl
 by_cases he : ∃z,w.graph.adj v z=true ∧ z≠l
 · obtain ⟨z,hz,hzl⟩ := he
   have hzv : z≠v := by intro hh; subst z; rw [w.graph.loopless] at hz; contradiction
   have hzm : z∈leafPairVertices l v := by
     simp [leafPairVertices,deleteVertices,List.mem_erase_of_ne hzv,List.mem_erase_of_ne hzl]
   obtain ⟨j,hj,hje⟩ := List.getElem_of_mem hzm
   let i : Fin (leafPairVertices l v).length := ⟨j,hj⟩
   have hie : (leafPairVertices l v)[i.val]=z := hje
   have hxs := leafPair_nodup l v
   have hres : (leafPairVertices l v).filter (fun u => !(w.graph.adj v u))=
       (leafPairVertices l v).erase z := by
     rw [List.Nodup.erase_eq_filter hxs]
     apply List.filter_congr
     intro u hu
     have hh := residual_neighbor_unique w.graph l v z hal hz hzl hd u hu
     cases ha : w.graph.adj v u <;> simp_all
   have hq (r : Nat) : coefficient (deleteVertex (inducedOn w.graph (leafPairVertices l v)) i) r=
       coefficient (inducedOn w.graph ((leafPairVertices l v).filter (fun u => !(w.graph.adj v u)))) r := by
     rw [NestedDeletion.coefficient_delete_inducedOn w.graph _ hxs i r,hie,hres]
   have hm := critical_order_above_half w
   have hs := leafPair_length l v hlv
   have hf := inducedOn_isForest w.graph w.forest _ hxs
   have hcert := InteriorRootSlope.forest_root_slope (inducedOn w.graph (leafPairVertices l v)) hf i
       (w.M-1) (by omega) (by omega)
   rw [hq,hq] at hcert
   have hpre := forest_prefix_step (inducedOn w.graph (leafPairVertices l v)) hf (w.M-1) (by omega)
   have hidx : w.M-1+1=w.M := by omega
   rw [hidx] at hcert hpre
   exact critical_leaf_certificate_impossible w l v hlv hl hpre hcert
 · apply LinearFactor.critical_has_no_edge_component w l v hlv hl
   intro u
   constructor
   · intro hu
     by_cases hh : u=l
     · exact hh
     · exact False.elim (he ⟨u,hu,hh⟩)
   · intro hu; rw [hu]; exact hal

end Erdos993.InteriorDegreeTwo
