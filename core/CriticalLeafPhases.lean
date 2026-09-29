import FirstInteriorBoundaryExclusion
namespace Erdos993.LeafPhases
open Counting Structure LeafBoundary

theorem unimodal_prefix_of_rise (a : Nat → Nat) (hu : Unimodal a)
 (r : Nat) (hr : a r<a (r+1)) : ∀i,i≤r → a i≤a (i+1) := by
 obtain ⟨m,up,down⟩ := hu
 have hm : r<m := by
   by_cases hh : r<m
   · exact hh
   · have ht := down r (by omega); omega
 intro i hi
 exact up i (by omega)

def Low (g h q : Nat → Nat) (M b : Nat) : Prop :=
 q M<q (M-1) ∧ h (b-1)<h b ∧ g (M+1)<g M

def High (g h q : Nat → Nat) (M b : Nat) : Prop :=
 h M<h (M-1) ∧ g b<g (b+1) ∧ q (b-1)<q b

theorem leaf_phase_partition (f g h q : Nat → Nat) (M b : Nat)
 (hM : 1≤M) (hb : M<b)
 (fg : ∀r,f (r+1)=g (r+1)+h r)
 (gh : ∀r,g (r+1)=h (r+1)+q r)
 (fall : f (M+1)<f M) (rise : f b<f (b+1))
 (ug : Unimodal g) (uh : Unimodal h) :
 Low g h q M b ∨ High g h q M b := by
 have hMi : M-1+1=M := by omega
 have hbi : b-1+1=b := by omega
 have fM := fg M
 have fprev := fg (M-1)
 have fb := fg b
 have fbprev := fg (b-1)
 have gM := gh M
 have gprev := gh (M-1)
 have gb := gh b
 have gbprev := gh (b-1)
 rw [hMi] at fprev gprev
 rw [hbi] at fbprev gbprev
 by_cases hp : h (M-1)≤h M
 · have gf : g (M+1)<g M := by omega
   have gt := unimodal_tail_of_fall g ug M gf b (by omega)
   have hr : h (b-1)<h b := by omega
   have hh := unimodal_prefix_of_rise h uh (b-1) (by rw [hbi]; exact hr) M (by omega)
   exact Or.inl ⟨by omega,hr,gf⟩
 · have hf : h M<h (M-1) := by omega
   have ht := unimodal_tail_of_fall h uh (M-1) (by rw [hMi]; exact hf) (b-1) (by omega)
   have ht' := unimodal_tail_of_fall h uh (M-1) (by rw [hMi]; exact hf) b (by omega)
   rw [hbi] at ht
   exact Or.inr ⟨hf,by omega,by omega⟩

theorem phases_disjoint (g h q : Nat → Nat) (M b : Nat) (hb : M<b)
 (uh : Unimodal h) : ¬(Low g h q M b ∧ High g h q M b) := by
 rintro ⟨hl,hh⟩
 have hM : 1≤M := by
   by_cases hz : M=0
   · subst M; have ht := hh.1; simp at ht
   · omega
 have he : M-1+1=M := by omega
 have ht := unimodal_tail_of_fall h uh (M-1) (by rw [he]; exact hh.1) (b-1) (by omega)
 have hb' : b-1+1=b := by omega
 rw [hb'] at ht
 have hr := hl.2.1
 omega

theorem critical_leaf_phases (w : Closure.CriticalWitness) (l v : Fin w.n)
 (hlv : l≠v) (hl : ∀u,w.graph.adj l u=true ↔ u=v) :
 let g := coefficient (deleteVertex w.graph l)
 let h := coefficient (inducedOn w.graph (leafPairVertices l v))
 let q := coefficient (inducedOn w.graph ((leafPairVertices l v).filter (fun u => !(w.graph.adj v u))))
 Low g h q w.M w.b ∨ High g h q w.M w.b := by
 have recs := actual_leaf_recurrences w.graph l v hlv hl
 have ug := critical_inducedOn_unimodal w (deleteVertices l) (deleteVertices_nodup l)
   (by have hh := deleteVertices_length l; have hh' := l.isLt; omega)
 have uh := critical_inducedOn_unimodal w (leafPairVertices l v) (leafPair_nodup l v)
   (by have hh := leafPair_length l v hlv; omega)
 exact leaf_phase_partition _ _ _ _ w.M w.b w.positiveFallIndex w.returnAfterFall
   (fun r => (recs r).1) (fun r => (recs r).2) w.firstFall w.returningRise ug uh

theorem target_iff_two_remaining_exclusions :
 Target ↔ Closure.Delta2Excluded ∧ Closure.DeeperExcluded :=
 Closure.target_iff_exclusions InteriorExclusion.critical_classification_verified

end Erdos993.LeafPhases
