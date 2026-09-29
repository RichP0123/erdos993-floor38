import NextEndSupport
namespace Erdos993.SupportCore
open Counting Structure LeafBoundary EndPadding PaddingCounts

def coreVertices {n : Nat} (G : Graph n) (l v z : Fin n) :=
 (leafPairVertices l v).filter (fun u => !(G.adj v u && decide (u≠z)))

theorem support_isolated {n : Nat} (G : Graph n) (l v z : Fin n)
 (he : ∀u,G.adj v u=true → u≠z → ∀x y,G.adj u x=true → G.adj u y=true → x=y) :
 ∀u∈supportLeaves G l v z,∀x∈leafPairVertices l v,G.adj u x=false := by
 intro u hu x hx
 have hp : G.adj v u=true ∧ u≠z := by simpa [supportLeaves] using (List.mem_filter.mp hu).2
 have hxv : x≠v := ((List.Nodup.mem_erase_iff (deleteVertices_nodup l)).mp hx).1
 cases hh : G.adj u x
 · rfl
 · exact False.elim (hxv (he u hp.1 hp.2 x v hh (by rw [G.symm]; exact hp.1)))

theorem core_contains_continuation {n : Nat} (G : Graph n) (l v z : Fin n)
 (hz : z∈leafPairVertices l v) : z∈coreVertices G l v z := by simp [coreVertices,hz]

theorem core_length {n : Nat} (G : Graph n) (l v z : Fin n) :
 (coreVertices G l v z).length+(supportLeaves G l v z).length=(leafPairVertices l v).length := by
 have h := filter_complement_lengths (leafPairVertices l v) (fun u => G.adj v u && decide (u≠z))
 exact (Nat.add_comm _ _).trans h

theorem core_delete_continuation {n : Nat} (G : Graph n) (l v z : Fin n)
 (hz : G.adj v z=true) :
 (coreVertices G l v z).erase z=(leafPairVertices l v).filter (fun u => !(G.adj v u)) := by
 have hn : (coreVertices G l v z).Nodup := List.Sublist.nodup List.filter_sublist (leafPair_nodup l v)
 rw [List.Nodup.erase_eq_filter hn]
 unfold coreVertices
 rw [List.filter_filter]
 apply List.filter_congr
 intro u hu
 by_cases he : u=z
 · subst u; simp [hz]
 · cases G.adj v u <;> simp [he]

theorem core_factor {n : Nat} (G : Graph n) (l v z : Fin n)
 (he : ∀u,G.adj v u=true → u≠z → ∀x y,G.adj u x=true → G.adj u y=true → x=y)
 (r : Nat) :
 coefficient (inducedOn G (leafPairVertices l v)) r=
 pad (supportLeaves G l v z).length (coefficient (inducedOn G (coreVertices G l v z))) r := by
 let p := fun u => G.adj v u && decide (u≠z)
 have h := rankCount_isolated_prefix G (supportLeaves G l v z) (coreVertices G l v z) ?_ r
 · have hp := rankCount_perm (List.filter_append_perm p (leafPairVertices l v)) (independent G)
     (independent_permInvariant G) r
   change rankCount (independent G) (supportLeaves G l v z++coreVertices G l v z) r=_ at hp
   rw [hp,←coefficient_inducedOn] at h
   have hf : rankCount (independent G) (coreVertices G l v z)=coefficient (inducedOn G (coreVertices G l v z)) := by
     funext j; exact (coefficient_inducedOn G _ j).symm
   rw [hf] at h
   exact h
 · intro u hu x hx
   apply support_isolated G l v z he u hu x
   rcases List.mem_append.mp hx with hx | hx <;> exact (List.mem_filter.mp hx).1

theorem core_curvature_budget {n : Nat} (G : Graph n) (hf : IsForest G)
 (l v z : Fin n) (hz : z∈leafPairVertices l v)
 (he : ∀u,G.adj v u=true → u≠z → ∀x y,G.adj u x=true → G.adj u y=true → x=y)
 (hs : (supportLeaves G l v z).length=1) (r : Nat) :
 2*((r:Int)+1)*(coefficient (inducedOn G (leafPairVertices l v)) (r+1):Int)+
 2*((coreVertices G l v z).length-1:Int)*(coefficient (inducedOn G (coreVertices G l v z)) r:Int)≤
 ((coreVertices G l v z).length:Int)*curvature (inducedOn G (leafPairVertices l v)) (r+1) := by
 have hm : 1≤(coreVertices G l v z).length := List.length_pos_of_mem (core_contains_continuation G l v z hz)
 have hb := InducedIsolate.induced_isolate_budget G hf (leafPairVertices l v) (leafPair_nodup l v)
   (fun u => G.adj v u && decide (u≠z)) (fun _ => true) (support_isolated G l v z he) 0 hs hm r
 have ht : (coreVertices G l v z).filter (fun _ => true)=coreVertices G l v z := by
   apply List.filter_eq_self.mpr
   intro u hu; rfl
 change _+_*(pad 0 (coefficient (inducedOn G ((coreVertices G l v z).filter (fun _ => true)))) r:Int)≤_ at hb
 rw [ht] at hb
 simpa [coreVertices,pad] using hb

end Erdos993.SupportCore
