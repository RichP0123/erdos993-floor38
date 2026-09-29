import LeafBoundaryTransfer
namespace Erdos993.EndSupport
open Counting Structure LeafBoundary

def tailPath {n l : Nat} {G : Graph n} (p : SimplePath G (l+1)) : SimplePath G l where
 vertex := fun i => p.vertex i.succ
 injective := by
   intro i j h
   have hh := p.injective _ _ h
   apply Fin.ext
   have := congrArg Fin.val hh
   simp only [Fin.val_succ] at this
   omega
 consecutive := by
   intro i
   exact p.consecutive i.succ

/-- Every neighbour of the penultimate vertex except the next path vertex
 can replace the endpoint of a longest path, and is therefore a leaf. -/
theorem longest_path_end_support {n l : Nat} {G : Graph n} (hf : IsForest G)
 (p : SimplePath G (l+2))
 (hmax : ∀ k, Nonempty (SimplePath G k) → k≤l+2)
 (u : Fin n) (ha : G.adj (p.vertex ⟨1,by omega⟩) u=true)
 (hne : u≠p.vertex ⟨2,by omega⟩) :
 ∀ x y, G.adj u x=true → G.adj u y=true → x=y := by
 let t := tailPath p
 have hn : ∀ i, u≠t.vertex i := by
   intro i he
   have hi : G.adj (t.vertex ⟨0,by omega⟩) (t.vertex i)=true := by
     change G.adj (p.vertex ⟨1,by omega⟩) (t.vertex i)=true
     rw [←he]
     exact ha
   by_cases hz : i.val=0
   · have heq : i=⟨0,by omega⟩ := by apply Fin.ext; exact hz
     rw [heq,G.loopless] at hi
     contradiction
   · by_cases ho : i.val=1
     · apply hne
       rw [he]
       change p.vertex i.succ=p.vertex ⟨2,by omega⟩
       congr 1
       apply Fin.ext
       simp only [Fin.val_succ]
       omega
     · have hc := path_no_endpoint_chord hf t i (by omega)
       rw [hc] at hi
       contradiction
 let q := prependPath t u hn (by change G.adj u (p.vertex ⟨1,by omega⟩)=true; rw [G.symm]; exact ha)
 exact longest_path_endpoint_leaf hf q hmax

end Erdos993.EndSupport
