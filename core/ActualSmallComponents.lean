import StarSupportExclusion
namespace Erdos993.ActualComponents
open Counting Structure CurvatureProof

theorem index_exists {n : Nat} (xs : List (Fin n)) (u : Fin n) (hu : u∈xs) :
 ∃i : Fin xs.length,xs[i.val]=u := by
 obtain ⟨j,hj,he⟩ := List.getElem_of_mem hu
 exact ⟨⟨j,hj⟩,he⟩

noncomputable def index {n : Nat} (xs : List (Fin n)) (u : Fin n) (hu : u∈xs) : Fin xs.length :=
 Classical.choose (index_exists xs u hu)

theorem index_label {n : Nat} (xs : List (Fin n)) (u : Fin n) (hu : u∈xs) :
 xs[(index xs u hu).val]=u := Classical.choose_spec (index_exists xs u hu)

theorem label_eq_index {n : Nat} (xs : List (Fin n)) (hx : xs.Nodup)
 (u : Fin n) (hu : u∈xs) (i : Fin xs.length) : xs[i.val]=u ↔ i=index xs u hu := by
 constructor
 · intro h
   exact list_vertex_injective xs hx _ _ (h.trans (index_label xs u hu).symm)
 · intro h
   rw [h,index_label]

theorem isolated_quarter_curvature {n : Nat} (G : Graph n) (hf : IsForest G)
 (u : Fin n) (hi : ∀v,G.adj u v=false) (k : Nat) (hk : 2≤k) (hn : n+1=4*k) :
 3*(coefficient G k:Int)≤4*curvature G k := by
 have h := SingleIsolate.forest_single_isolate_bound G hf (by omega) u hi k
 have hz := forest_curvature_nonnegative G hf k
 have hm := Int.mul_le_mul_of_nonneg_right (show (n:Int)≤4*(k:Int) by omega) hz
 have ht : (4*(k:Int))*(coefficient G k:Int)≤(4*(k:Int))*curvature G k := by grind
 have hh := Int.le_of_mul_le_mul_left ht (by omega)
 omega

theorem induced_isolate_curvature {n : Nat} (G : Graph n) (hf : IsForest G)
 (xs : List (Fin n)) (hx : xs.Nodup) (u : Fin n) (hu : u∈xs)
 (hi : ∀v∈xs,G.adj u v=false) (k : Nat) (hk : 2≤k) (hn : xs.length+1=4*k) :
 3*(coefficient (inducedOn G xs) k:Int)≤4*curvature (inducedOn G xs) k := by
 apply isolated_quarter_curvature (inducedOn G xs) (inducedOn_isForest G hf xs hx) (index xs u hu)
 · intro v
   change G.adj xs[(index xs u hu).val] xs[v.val]=false
   rw [index_label]
   exact hi xs[v.val] (List.getElem_mem _)
 · exact hk
 · exact hn

theorem induced_p3_curvature {n : Nat} (G : Graph n) (hf : IsForest G)
 (xs : List (Fin n)) (hx : xs.Nodup) (l v z : Fin n)
 (hlm : l∈xs) (hvm : v∈xs) (hzm : z∈xs) (hlv : l≠v) (hlz : l≠z) (hvz : v≠z)
 (hl : ∀u∈xs,G.adj l u=true ↔ u=v) (hz : ∀u∈xs,G.adj z u=true ↔ u=v)
 (hv : ∀u∈xs,G.adj v u=true ↔ u=l ∨ u=z)
 (k : Nat) (hk : 2≤k) (hn : xs.length+1=4*k) :
 3*(coefficient (inducedOn G xs) k:Int)≤4*curvature (inducedOn G xs) k := by
 apply SmallComponent.forest_p3_component_bound (inducedOn G xs) (inducedOn_isForest G hf xs hx)
   (index xs l hlm) (index xs v hvm) (index xs z hzm)
 · intro h
   have he := congrArg (fun i : Fin xs.length => xs[i.val]) h
   dsimp at he
   rw [index_label,index_label] at he
   exact hlv he
 · intro h
   have he := congrArg (fun i : Fin xs.length => xs[i.val]) h
   dsimp at he
   rw [index_label,index_label] at he
   exact hlz he
 · intro h
   have he := congrArg (fun i : Fin xs.length => xs[i.val]) h
   dsimp at he
   rw [index_label,index_label] at he
   exact hvz he
 · intro u
   change G.adj xs[(index xs l hlm).val] xs[u.val]=true ↔ _
   rw [index_label,hl xs[u.val] (List.getElem_mem _),label_eq_index xs hx v hvm]
 · intro u
   change G.adj xs[(index xs z hzm).val] xs[u.val]=true ↔ _
   rw [index_label,hz xs[u.val] (List.getElem_mem _),label_eq_index xs hx v hvm]
 · intro u
   change G.adj xs[(index xs v hvm).val] xs[u.val]=true ↔ _
   rw [index_label,hv xs[u.val] (List.getElem_mem _),label_eq_index xs hx l hlm,label_eq_index xs hx z hzm]
 · exact hk
 · exact hn

end Erdos993.ActualComponents
