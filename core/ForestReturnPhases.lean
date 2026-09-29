import RefinedForestPrefix
import CriticalLeafPhases
namespace Erdos993.ForestReturnPhases
open Counting Structure LeafBoundary LeafPhases

def P (d e : Nat → Nat) (M b : Nat) : Prop :=
 d (M+1)<d M ∧ e (b-1)<e b

def Q (d e : Nat → Nat) (M b : Nat) : Prop :=
 e M<e (M-1) ∧ d b<d (b+1)

/-- Exhaustive deletion phases, retaining strict signs and allowing plateaus. -/
theorem partition (f d e : Nat → Nat) (M b : Nat)
 (hM : 1≤M) (hb : M<b)
 (rec : ∀r,f (r+1)=d (r+1)+e r)
 (fall : f (M+1)<f M) (rise : f b<f (b+1))
 (ud : Unimodal d) (ue : Unimodal e) : P d e M b ∨ Q d e M b := by
 have hm : M-1+1=M := by omega
 have hbi : b-1+1=b := by omega
 have h1 := rec M
 have h2 := rec (M-1)
 have h3 := rec b
 have h4 := rec (b-1)
 rw [hm] at h2
 rw [hbi] at h4
 by_cases he : e (M-1)≤e M
 · have hd : d (M+1)<d M := by omega
   have ht := unimodal_tail_of_fall d ud M hd b (by omega)
   exact Or.inl ⟨hd,by omega⟩
 · have hf : e M<e (M-1) := by omega
   have ht := unimodal_tail_of_fall e ue (M-1) (by rw [hm]; exact hf) (b-1) (by omega)
   rw [hbi] at ht
   exact Or.inr ⟨hf,by omega⟩

theorem disjoint (d e : Nat → Nat) (M b : Nat) (hb : M<b)
 (ud : Unimodal d) : ¬(P d e M b ∧ Q d e M b) := by
 rintro ⟨hp,hq⟩
 have ht := unimodal_tail_of_fall d ud M hp.1 b (by omega)
 have hr := hq.2
 omega

def closedVertices {n : Nat} (G : Graph n) (v : Fin n) : List (Fin n) :=
 (deleteVertices v).filter (fun u => !(G.adj v u))

def VertexP (w : Closure.CriticalWitness) (v : Fin w.n) : Prop :=
 P (coefficient (deleteVertex w.graph v))
   (coefficient (inducedOn w.graph (closedVertices w.graph v))) w.M w.b

def VertexQ (w : Closure.CriticalWitness) (v : Fin w.n) : Prop :=
 Q (coefficient (deleteVertex w.graph v))
   (coefficient (inducedOn w.graph (closedVertices w.graph v))) w.M w.b

/-- Actual vertex deletion and closed-neighborhood deletion of the entire forest. -/
theorem critical_partition (w : Closure.CriticalWitness) (v : Fin w.n) :
 VertexP w v ∨ VertexQ w v := by
 have hl := deleteVertices_length v
 have hv := v.isLt
 have hd := critical_inducedOn_unimodal w (deleteVertices v) (deleteVertices_nodup v) (by omega)
 have hlen : (closedVertices w.graph v).length≤(deleteVertices v).length := List.length_filter_le _ _
 have he := critical_inducedOn_unimodal w (closedVertices w.graph v)
   ((deleteVertices_nodup v).filter _) (by omega)
 exact partition _ _ _ w.M w.b w.positiveFallIndex w.returnAfterFall
   (coefficient_vertex_recurrence w.graph v) w.firstFall w.returningRise hd he

theorem critical_disjoint (w : Closure.CriticalWitness) (v : Fin w.n) :
 ¬(VertexP w v ∧ VertexQ w v) := by
 have hl := deleteVertices_length v
 have hv := v.isLt
 exact disjoint _ _ w.M w.b w.returnAfterFall
   (critical_inducedOn_unimodal w (deleteVertices v) (deleteVertices_nodup v) (by omega))

theorem support_deletion_factor {n : Nat} (G : Graph n) (l v : Fin n)
 (hlv : l≠v) (hl : ∀u,G.adj l u=true ↔ u=v) (r : Nat) :
 coefficient (deleteVertex G v) (r+1)=
 coefficient (inducedOn G (leafPairVertices l v)) (r+1)+
 coefficient (inducedOn G (leafPairVertices l v)) r := by
 have hm : l∈deleteVertices v := by simp [deleteVertices,List.mem_erase_of_ne hlv]
 have hh := rankCount_vertex_recurrence G (deleteVertices v) l hm r
 have he : (deleteVertices v).erase l=leafPairVertices l v := by
   unfold leafPairVertices deleteVertices
   exact List.erase_comm _ _
 rw [he] at hh
 have hf : (leafPairVertices l v).filter (fun u => !(G.adj l u))=leafPairVertices l v := by
   apply List.filter_eq_self.mpr
   intro u hu
   have hne : u≠v := by
     have hn := List.Nodup.not_mem_erase (deleteVertices_nodup l) (a:=v)
     intro he
     subst u
     exact hn hu
   have hx : G.adj l u=false := by
     cases h : G.adj l u
     · rfl
     · exact False.elim (hne ((hl u).mp h))
   simp [hx]
 rw [hf] at hh
 simpa only [deleteVertex,coefficient_inducedOn] using hh

/-- Every actual pendant leaf and its support have opposite deletion phases. -/
theorem critical_leaf_support_opposite (w : Closure.CriticalWitness) (l v : Fin w.n)
 (hlv : l≠v) (hl : ∀u,w.graph.adj l u=true ↔ u=v) :
 (VertexP w l ∧ VertexQ w v) ∨ (VertexQ w l ∧ VertexP w v) := by
 let h := coefficient (inducedOn w.graph (leafPairVertices l v))
 have uh := critical_inducedOn_unimodal w (leafPairVertices l v) (leafPair_nodup l v)
   (by have hh := leafPair_length l v hlv; omega)
 have hm : w.M-1+1=w.M := by have hh := w.positiveFallIndex; omega
 have hb : w.b-1+1=w.b := by have hh := w.returnAfterFall; omega
 have el : coefficient (inducedOn w.graph (closedVertices w.graph l))=h := by
   unfold closedVertices
   rw [leaf_residual_eq w.graph l v hl]
 have recs := support_deletion_factor w.graph l v hlv hl
 have vm := recs w.M
 have vm' := recs (w.M-1)
 have vb := recs w.b
 have vb' := recs (w.b-1)
 rw [hm] at vm'
 rw [hb] at vb'
 rcases critical_partition w l with hp | hq
 · have hh : h (w.b-1)<h w.b := by
     have ht := hp.2
     rw [el] at ht
     exact ht
   have hu1 := unimodal_prefix_of_rise h uh (w.b-1) (by rw [hb]; exact hh)
     w.M (by have ht := w.returnAfterFall; omega)
   have hu2 := unimodal_prefix_of_rise h uh (w.b-1) (by rw [hb]; exact hh)
     (w.M-1) (by have ht := w.returnAfterFall; omega)
   rw [hm] at hu2
   rcases critical_partition w v with hv | hv
   · have hf := hv.1
     dsimp only [h] at hu1 hu2
     omega
   · exact Or.inl ⟨hp,hv⟩
 · have hh : h w.M<h (w.M-1) := by
     have ht := hq.1
     rw [el] at ht
     exact ht
   have ht1 := unimodal_tail_of_fall h uh (w.M-1) (by rw [hm]; exact hh) w.b
     (by have ht := w.returnAfterFall; omega)
   have ht2 := unimodal_tail_of_fall h uh (w.M-1) (by rw [hm]; exact hh) (w.b-1)
     (by have ht := w.returnAfterFall; omega)
   rw [hb] at ht2
   rcases critical_partition w v with hv | hv
   · exact Or.inr ⟨hq,hv⟩
   · have hr := hv.2
     dsimp only [h] at ht1 ht2
     omega

/-- An exact scalar reduction for pure TWO; recurrences and phase signs remain premises. -/
theorem pure_two_compensation (a c h f : Nat → Nat) (k : Nat)
 (hh : h (k+1)≤h (k+2)) (ha : a k≤a (k+1))
 (rec : (f (k+2):Int)-f (k+1)=
   ((h (k+2):Int)-h (k+1))+((a (k+1):Int)-a k)+
   ((a k:Int)-a (k-1))+((c (k+1):Int)-c k))
 (pay : (c k:Int)-c (k+1)≤(a k:Int)-a (k-1)) : f (k+1)≤f (k+2) := by
 omega

end Erdos993.ForestReturnPhases
