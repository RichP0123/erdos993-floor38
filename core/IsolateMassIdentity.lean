import MultipleIsolateBound
namespace Erdos993.IsolateMass
open Counting Structure PaddingCounts RootingBridgeAudit IsolateCurvature

theorem isolate_partition_coefficient {n : Nat} (G : Graph n) (p : Fin n → Bool)
 (hi : ∀v,p v=true → ∀u,G.adj v u=false) (r : Nat) :
 coefficient G r=pad ((List.finRange n).filter p).length
   (coefficient (inducedOn G ((List.finRange n).filter (fun u => !(p u))))) r := by
 have h := rankCount_isolated_prefix G ((List.finRange n).filter p)
   ((List.finRange n).filter (fun u => !(p u)))
   (by intro v hv u hu; exact hi v (List.mem_filter.mp hv).2 u) r
 rw [rankCount_perm (List.filter_append_perm p (List.finRange n)) (independent G)
     (independent_permInvariant G) r,rankCount_graph] at h
 have he : rankCount (independent G) ((List.finRange n).filter (fun u => !(p u)))=
     coefficient (inducedOn G ((List.finRange n).filter (fun u => !(p u)))) := by
   funext j; exact (coefficient_inducedOn G _ j).symm
 rw [he] at h
 exact h

theorem pad_one_injective (a b : Nat → Nat) (h : ∀r,pad 1 a r=pad 1 b r) : a=b := by
 funext r
 induction r with
 | zero => simpa [pad] using h 0
 | succ r ih =>
   have hh := h (r+1)
   simp only [pad] at hh
   omega

theorem isolate_pad_one {n : Nat} (G : Graph n) (v : Fin n)
 (hi : ∀u,G.adj v u=false) :
 coefficient G=pad 1 (coefficient (deleteVertex G v)) := by
 have h := LinearFactor.isolate_factor G v hi
 rw [h]
 funext r
 cases r <;> simp [LinearFactor.linearFactor,pad]

theorem isolate_deletions_equal {n : Nat} (G : Graph n) (u v : Fin n)
 (hu : ∀w,G.adj u w=false) (hv : ∀w,G.adj v w=false) :
 coefficient (deleteVertex G u)=coefficient (deleteVertex G v) := by
 apply pad_one_injective
 intro r
 rw [←isolate_pad_one G u hu,←isolate_pad_one G v hv]

theorem pad_next_one (s : Nat) (a : Nat → Nat) : pad (s+1) a=pad 1 (pad s a) := by
 funext r
 cases r <;> rfl

theorem isolate_mass_identity {n : Nat} (G : Graph n) (p : Fin n → Bool)
 (hi : ∀v,p v=true → ∀u,G.adj v u=false)
 (s : Nat) (hs : ((List.finRange n).filter p).length=s+1) (r : Nat) :
 isolatedInc G p (r+1)=(s+1)*pad s
   (coefficient (inducedOn G ((List.finRange n).filter (fun u => !(p u))))) r := by
 have hpos : 0<((List.finRange n).filter p).length := by omega
 obtain ⟨v,hv⟩ := List.exists_mem_of_length_pos hpos
 have hvp := (List.mem_filter.mp hv).2
 have hdel : coefficient (deleteVertex G v)=pad s
     (coefficient (inducedOn G ((List.finRange n).filter (fun u => !(p u))))) := by
   apply pad_one_injective
   intro j
   rw [←isolate_pad_one G v (hi v hvp)]
   rw [isolate_partition_coefficient G p hi j,hs,pad_next_one]
 rw [←sum_inc_filter]
 have he : sumBy ((List.finRange n).filter p) (fun u => inc G u (r+1))=
     sumBy ((List.finRange n).filter p) (fun _ => pad s
       (coefficient (inducedOn G ((List.finRange n).filter (fun u => !(p u))))) r) := by
   apply sumBy_congr
   intro u hu
   rw [VertexIncidence.incidence_isolate G u (hi u (List.mem_filter.mp hu).2) r,
       isolate_deletions_equal G u v (hi u (List.mem_filter.mp hu).2) (hi v hvp),hdel]
 rw [he,sumBy_const,hs]

end Erdos993.IsolateMass
