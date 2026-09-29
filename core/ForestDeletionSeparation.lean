import SeparatedRootCurvature
namespace Erdos993.DeletionSeparation
open Counting Structure ParentConstruction

def prefixPath {n l : Nat} {G : Graph n} (p : SimplePath G l) (i : Fin (l+1)) :
 SimplePath G i.val where
 vertex := fun j => p.vertex ⟨j.val,by omega⟩
 injective := by
   intro j k h
   have he := p.injective _ _ h
   apply Fin.ext
   exact congrArg (fun z : Fin (l+1) => z.val) he
 consecutive := by
   intro j
   exact p.consecutive ⟨j.val,by omega⟩

def Reach {n : Nat} (G : Graph n) (a b : Fin n) : Prop :=
 ∃ l,∃ p : SimplePath G l,p.vertex ⟨0,by omega⟩=a ∧ p.vertex ⟨l,by omega⟩=b

theorem reach_self {n : Nat} (G : Graph n) (a : Fin n) : Reach G a a :=
 ⟨0,singletonPath G a,rfl,rfl⟩

theorem reach_step {n : Nat} (G : Graph n) (a u v : Fin n)
 (hr : Reach G a u) (he : G.adj u v=true) : Reach G a v := by
 classical
 obtain ⟨l,p,hfirst,hlast⟩ := hr
 by_cases hv : ∃i,p.vertex i=v
 · obtain ⟨i,hi⟩ := hv
   exact ⟨i.val,prefixPath p i,hfirst,hi⟩
 · have hn : ∀i,v≠(reversePath p).vertex i := by
     intro i hh
     exact hv ⟨i.rev,hh.symm⟩
   have hz : (reversePath p).vertex ⟨0,by omega⟩=u := by
     simpa [reversePath,Fin.rev] using hlast
   let q := prependPath (reversePath p) v hn (by rw [hz,G.symm]; exact he)
   refine ⟨l+1,reversePath q,?_,?_⟩
   · change q.vertex (⟨0,by omega⟩ : Fin (l+1+1)).rev=a
     have ht : (⟨0,by omega⟩ : Fin (l+1+1)).rev=(⟨l,by omega⟩ : Fin (l+1)).succ := by
       apply Fin.ext; simp [Fin.rev]
     rw [ht]
     change p.vertex (⟨l,by omega⟩ : Fin (l+1)).rev=a
     have ht : (⟨l,by omega⟩ : Fin (l+1)).rev=⟨0,by omega⟩ := by
       apply Fin.ext; simp [Fin.rev]
     rw [ht]; exact hfirst
   · change q.vertex (⟨l+1,by omega⟩ : Fin (l+1+1)).rev=v
     have ht : (⟨l+1,by omega⟩ : Fin (l+1+1)).rev=⟨0,by omega⟩ := by
       apply Fin.ext; simp [Fin.rev]
     rw [ht]
     rfl

theorem reach_edge_iff {n : Nat} (G : Graph n) (a u v : Fin n)
 (he : G.adj u v=true) : Reach G a u ↔ Reach G a v :=
 ⟨fun h => reach_step G a u v h he,fun h => reach_step G a v u h (by rw [G.symm]; exact he)⟩

def liftDeletedPath {n l : Nat} (G : Graph n) (v : Fin n)
 (p : SimplePath (deleteVertex G v) l) : SimplePath G l where
 vertex := fun i => embed v (p.vertex i)
 injective := by
   intro i j h
   exact p.injective i j (embed_injective v _ _ h)
 consecutive := p.consecutive

theorem deleted_neighbors_not_reach {n : Nat} (G : Graph n) (hf : IsForest G)
 (v : Fin n) (u w : Fin (deleteVertices v).length)
 (hu : G.adj v (embed v u)=true) (hw : G.adj v (embed v w)=true) (hne : u≠w) :
 ¬Reach (deleteVertex G v) u w := by
 intro hr
 obtain ⟨l,p,hfirst,hlast⟩ := hr
 have hl : 1≤l := by
   by_cases hh : l=0
   · subst l
     exact False.elim (hne (hfirst.symm.trans hlast))
   · omega
 let q := liftDeletedPath G v p
 have hn : ∀i,v≠q.vertex i := by
   intro i hh
   exact embed_ne_deleted v (p.vertex i) hh.symm
 have he : G.adj v (q.vertex ⟨0,by omega⟩)=true := by
   change G.adj v (embed v (p.vertex _))=true
   rw [hfirst]; exact hu
 let t := prependPath q v hn he
 have hh := path_no_endpoint_chord hf t (⟨l+1,by omega⟩ : Fin (l+1+1)) (by dsimp; omega)
 have ht : (⟨l+1,by omega⟩ : Fin (l+1+1))=(⟨l,by omega⟩ : Fin (l+1)).succ := rfl
 rw [ht] at hh
 change G.adj v (embed v (p.vertex ⟨l,by omega⟩))=false at hh
 rw [hlast,hw] at hh
 contradiction

theorem deletion_cut_curvature {n : Nat} (G : Graph n) (hf : IsForest G)
 (v : Fin n) (u w : Fin (deleteVertices v).length)
 (hu : G.adj v (embed v u)=true) (hw : G.adj v (embed v w)=true) (hne : u≠w) (r : Nat) :
 2*(r:Int)*(coefficient (deleteVertex G v) r:Int)≤
 (((deleteVertices v).length:Int)-1)*curvature (deleteVertex G v) r := by
 classical
 let p := fun z => decide (Reach (deleteVertex G v) u z)
 apply SeparatedRoot.forest_cut_curvature (deleteVertex G v) (deleteVertex_isForest G hf v) p
 · intro x y hxy
   simp only [p,reach_edge_iff (deleteVertex G v) u x y hxy]
 · exact ⟨u,by simp [p,reach_self]⟩
 · exact ⟨w,by simp [p,deleted_neighbors_not_reach G hf v u w hu hw hne]⟩

end Erdos993.DeletionSeparation
