import SingleIsolateBound
namespace Erdos993.LinearFactor
open Counting Structure LeafBoundary VertexIncidence

def linearFactor (b : Nat) (a : Nat → Nat) : Nat → Nat
 | 0 => a 0
 | r+1 => a (r+1)+b*a r

/-- Multiplication by 1+b*x preserves ordinary U, with no log-concavity or MU
 hypothesis. This does not assert closure under arbitrary unimodal products. -/
theorem linearFactor_unimodal (b : Nat) (a : Nat → Nat) (hu : Unimodal a) :
 Unimodal (linearFactor b a) := by
 obtain ⟨m,up,down⟩ := hu
 have pre : ∀i,i<m → linearFactor b a i≤linearFactor b a (i+1) := by
   intro i hi
   cases i with
   | zero => have h := up 0 hi; simp only [linearFactor]; omega
   | succ i =>
     have h1 := up i (by omega)
     have h2 := up (i+1) hi
     simp only [Nat.add_assoc] at h2
     change a (i+1)≤a (i+2) at h2
     have hm := Nat.mul_le_mul_left b h1
     change a (i+1)+b*a i≤a (i+2)+b*a (i+1)
     omega
 have post : ∀i,m+1≤i → linearFactor b a (i+1)≤linearFactor b a i := by
   intro i hi
   cases i with
   | zero => omega
   | succ i =>
     have h1 := down i (by omega)
     have h2 := down (i+1) (by omega)
     simp only [Nat.add_assoc] at h2
     change a (i+2)≤a (i+1) at h2
     have hm := Nat.mul_le_mul_left b h1
     change a (i+2)+b*a (i+1)≤a (i+1)+b*a i
     omega
 by_cases middle : linearFactor b a (m+1)≤linearFactor b a m
 · refine ⟨m,pre,?_⟩
   intro i hi
   by_cases he : i=m
   · subst i; exact middle
   · exact post i (by omega)
 · refine ⟨m+1,?_,post⟩
   intro i hi
   by_cases he : i=m
   · subst i; omega
   · exact pre i (by omega)

theorem isolate_factor {n : Nat} (G : Graph n) (v : Fin n)
 (hi : ∀u,G.adj v u=false) :
 coefficient G=linearFactor 1 (coefficient (deleteVertex G v)) := by
 funext r
 cases r with
 | zero => simp [linearFactor,Extraction.coefficient_zero]
 | succ r =>
   have h1 := incidence_deletion_partition G v (r+1)
   rw [incidence_isolate G v hi r] at h1
   simp only [linearFactor,Nat.one_mul]
   omega

theorem critical_has_no_isolate (w : Closure.CriticalWitness) (v : Fin w.n) :
 ¬(∀u,w.graph.adj v u=false) := by
 intro hi
 have hu := critical_inducedOn_unimodal w (deleteVertices v) (deleteVertices_nodup v)
   (by have := deleteVertices_length v; have := v.isLt; omega)
 have hf := linearFactor_unimodal 1 (coefficient (deleteVertex w.graph v)) hu
 rw [←isolate_factor w.graph v hi] at hf
 have hb := unimodal_tail_of_fall _ hf w.M w.firstFall w.b (by have := w.returnAfterFall; omega)
 have hr := w.returningRise
 omega

theorem edge_component_factor {n : Nat} (G : Graph n) (l v : Fin n) (hlv : l≠v)
 (hl : ∀u,G.adj l u=true ↔ u=v) (hv : ∀u,G.adj v u=true ↔ u=l) :
 coefficient G=linearFactor 2 (coefficient (inducedOn G (leafPairVertices l v))) := by
 have he : (leafPairVertices l v).filter (fun u => !(G.adj v u))=leafPairVertices l v := by
   apply List.filter_eq_self.mpr
   intro u hu
   have hn : u≠l := ((List.Nodup.mem_erase_iff (finRange_nodup n)).mp
     (List.mem_of_mem_erase hu)).1
   have ha : G.adj v u=false := by
     cases hh : G.adj v u
     · rfl
     · exact False.elim (hn ((hv u).mp hh))
   simp [ha]
 have hq : ∀ r, coefficient (inducedOn G ((leafPairVertices l v).filter (fun u => !(G.adj v u)))) r=
     coefficient (inducedOn G (leafPairVertices l v)) r := by
   intro r
   simp only [coefficient_inducedOn]
   rw [he]
 funext r
 cases r with
 | zero => simp [linearFactor,Extraction.coefficient_zero]
 | succ r =>
   have hh := actual_leaf_recurrences G l v hlv hl r
   rw [hq r] at hh
   simp only [linearFactor]
   omega

theorem critical_has_no_edge_component (w : Closure.CriticalWitness) (l v : Fin w.n)
 (hlv : l≠v) (hl : ∀u,w.graph.adj l u=true ↔ u=v)
 (hv : ∀u,w.graph.adj v u=true ↔ u=l) : False := by
 have hu := critical_inducedOn_unimodal w (leafPairVertices l v) (leafPair_nodup l v)
   (by have := leafPair_length l v hlv; omega)
 have hf := linearFactor_unimodal 2 _ hu
 rw [←edge_component_factor w.graph l v hlv hl hv] at hf
 have hb := unimodal_tail_of_fall _ hf w.M w.firstFall w.b (by have := w.returnAfterFall; omega)
 have hr := w.returningRise
 omega

end Erdos993.LinearFactor
