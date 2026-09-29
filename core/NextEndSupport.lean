import SupportCurvatureBudget
namespace Erdos993.NextSupport
open Counting Structure EndSupport LeafBoundary EndPadding

theorem neighbor_outside_path {n l : Nat} {G : Graph n} (hf : IsForest G)
 (p : SimplePath G (l+1)) (u : Fin n)
 (ha : G.adj (p.vertex ⟨0,by omega⟩) u=true)
 (hne : u≠p.vertex ⟨1,by omega⟩) : ∀i,u≠p.vertex i := by
 intro i he
 have hi : G.adj (p.vertex ⟨0,by omega⟩) (p.vertex i)=true := by rw [←he]; exact ha
 by_cases hz : i.val=0
 · have ht : i=⟨0,by omega⟩ := by apply Fin.ext; exact hz
   rw [ht,G.loopless] at hi; contradiction
 · by_cases ho : i.val=1
   · have ht : i=⟨1,by omega⟩ := by apply Fin.ext; exact ho
     exact hne (by rw [he,ht])
   · rw [path_no_endpoint_chord hf p i (by omega)] at hi
     contradiction

theorem replace_two_prefix {n l : Nat} {G : Graph n} (hf : IsForest G)
 (p : SimplePath G (l+3)) (u x : Fin n)
 (hu : G.adj (p.vertex ⟨2,by omega⟩) u=true)
 (hun : u≠p.vertex ⟨3,by omega⟩)
 (hx : G.adj u x=true) (hxn : x≠p.vertex ⟨2,by omega⟩) :
 ∃q : SimplePath G (l+3),q.vertex ⟨0,by omega⟩=x ∧
   q.vertex ⟨1,by omega⟩=u ∧ q.vertex ⟨2,by omega⟩=p.vertex ⟨2,by omega⟩ := by
 let t := tailPath (tailPath p)
 have hut : G.adj (t.vertex ⟨0,by omega⟩) u=true := hu
 have hun' : u≠t.vertex ⟨1,by omega⟩ := hun
 let q := prependPath t u (neighbor_outside_path hf t u hut hun') (by rw [G.symm]; exact hut)
 have hxq : G.adj (q.vertex ⟨0,by omega⟩) x=true := hx
 have hxn' : x≠q.vertex ⟨1,by omega⟩ := hxn
 let q' := prependPath q x (neighbor_outside_path hf q x hxq hxn') (by rw [G.symm]; exact hxq)
 exact ⟨q',rfl,rfl,rfl⟩

theorem critical_longest_end_degree_three (w : Closure.CriticalWitness)
 (hn : w.n+1=4*w.M) {j : Nat} (p : SimplePath w.graph (j+2))
 (hmax : ∀k,Nonempty (SimplePath w.graph k) → k≤j+2) :
 degree w.graph (p.vertex ⟨1,by omega⟩)=3 := by
 let l := p.vertex ⟨0,by omega⟩
 let v := p.vertex ⟨1,by omega⟩
 let z := p.vertex ⟨2,by omega⟩
 have hlv : l≠v := by
   intro he; have ht := congrArg Fin.val (p.injective _ _ he); simp at ht
 have hzv : z≠v := by
   intro he; have ht := congrArg Fin.val (p.injective _ _ he); simp at ht
 have hzl : z≠l := by
   intro he; have ht := congrArg Fin.val (p.injective _ _ he); simp at ht
 have hal : w.graph.adj l v=true := p.consecutive ⟨0,by omega⟩
 have ha : w.graph.adj v z=true := p.consecutive ⟨1,by omega⟩
 have hend := longest_path_endpoint_leaf w.forest p hmax
 have hl : ∀u,w.graph.adj l u=true ↔ u=v := by
   intro u; exact ⟨fun hu => hend u v hu hal,fun hu => hu ▸ hal⟩
 have hz : z∈leafPairVertices l v := by
   simp [leafPairVertices,deleteVertices,List.mem_erase_of_ne hzv,List.mem_erase_of_ne hzl]
 have hs := support_leaves_length w.graph l v z hlv hl hz ha
 by_cases hd : degree w.graph v≤2
 · exact False.elim (InteriorDegreeTwo.critical_first_interior_degree_two w hn l v hlv hl hd)
 · by_cases hd' : 4≤degree w.graph v
   · exact False.elim (InteriorLargeSupport.critical_first_interior_large_support w hn l v z hlv hl hz ha
       (fun u hu hne => longest_path_end_support w.forest p hmax u hu hne) (by omega))
   · change degree w.graph v=3
     omega

theorem critical_next_support {j : Nat} (w : Closure.CriticalWitness)
 (hn : w.n+1=4*w.M) (p : SimplePath w.graph (j+3))
 (hmax : ∀k,Nonempty (SimplePath w.graph k) → k≤j+3)
 (u x : Fin w.n) (hu : w.graph.adj (p.vertex ⟨2,by omega⟩) u=true)
 (hun : u≠p.vertex ⟨3,by omega⟩) (hx : w.graph.adj u x=true)
 (hxn : x≠p.vertex ⟨2,by omega⟩) :
 degree w.graph u=3 ∧ ∀a,w.graph.adj u a=true → a≠p.vertex ⟨2,by omega⟩ →
   ∀b c,w.graph.adj a b=true → w.graph.adj a c=true → b=c := by
 obtain ⟨q,h0,h1,h2⟩ := replace_two_prefix w.forest p u x hu hun hx hxn
 have hd := critical_longest_end_degree_three w hn q hmax
 rw [h1] at hd
 refine ⟨hd,?_⟩
 intro a ha han
 exact longest_path_end_support w.forest q hmax a (by rw [h1]; exact ha) (by rw [h2]; exact han)

end Erdos993.NextSupport
