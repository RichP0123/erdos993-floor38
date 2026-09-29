import ForestReturnPhases
import VertexIncidence

namespace Erdos993.ValleyDeletionCover
open Counting Structure LeafBoundary RootingBridgeAudit
set_option maxHeartbeats 800000

theorem interval_up (a : Nat → Nat) (i d : Nat)
 (step : ∀ r, i≤r → r<i+d → a r≤a (r+1)) : a i≤a (i+d) := by
 induction d with
 | zero => simp
 | succ d ih =>
   have hp := ih (by intro r hr hs; apply step r hr; omega)
   have hq := step (i+d) (by omega) (by omega)
   have he : i+(d+1)=i+d+1 := by omega
   rw [he]; exact Nat.le_trans hp hq

theorem interval_down (a : Nat → Nat) (i d : Nat)
 (step : ∀ r, i≤r → r<i+d → a (r+1)≤a r) : a (i+d)≤a i := by
 induction d with
 | zero => simp
 | succ d ih =>
   have hp := ih (by intro r hr hs; apply step r hr; omega)
   have hq := step (i+d) (by omega) (by omega)
   have he : i+(d+1)=i+d+1 := by omega
   rw [he]; exact Nat.le_trans hq hp

theorem no_valley (a : Nat → Nat) (hu : Unimodal a) (p q t : Nat)
 (hpq : p<q) (hqt : q<t) : a p≤a q ∨ a t≤a q := by
 obtain ⟨m,asc,desc⟩ := hu
 by_cases hq : q≤m
 · left
   have hh := interval_up a p (q-p) (by intro r hr hs; apply asc; omega)
   have he : p+(q-p)=q := by omega
   simpa [he] using hh
 · right
   have hh := interval_down a q (t-q) (by intro r hr hs; apply desc; omega)
   have he : q+(t-q)=t := by omega
   simpa [he] using hh

/-- Counts are for the actual vertex deletion; no polynomial correspondence premise. -/
theorem vertex_covering {n : Nat} (G : Graph n) (v : Fin n)
 (p q t delta epsilon : Nat) (hpq : p<q) (hqt : q<t)
 (hd : coefficient G p=coefficient G q+delta)
 (he : coefficient G t=coefficient G q+epsilon)
 (hu : Unimodal (coefficient (deleteVertex G v))) :
 delta+inc G v q≤inc G v p ∨ epsilon+inc G v q≤inc G v t := by
 have h := no_valley _ hu p q t hpq hqt
 have h1 := VertexIncidence.incidence_deletion_partition G v p
 have h2 := VertexIncidence.incidence_deletion_partition G v q
 have h3 := VertexIncidence.incidence_deletion_partition G v t
 rcases h with h | h
 · left; omega
 · right; omega

theorem critical_covering (w : Closure.CriticalWitness) (v : Fin w.n)
 (p q t delta epsilon : Nat) (hpq : p<q) (hqt : q<t)
 (hd : coefficient w.graph p=coefficient w.graph q+delta)
 (he : coefficient w.graph t=coefficient w.graph q+epsilon) :
 delta+inc w.graph v q≤inc w.graph v p ∨
 epsilon+inc w.graph v q≤inc w.graph v t := by
 have hl := deleteVertices_length v
 have hv := v.isLt
 exact vertex_covering w.graph v p q t delta epsilon hpq hqt hd he
   (critical_inducedOn_unimodal w (deleteVertices v) (deleteVertices_nodup v) (by omega))

theorem local_payment (cp cq ct delta epsilon K : Nat)
 (hd : delta≤K) (he : epsilon≤K)
 (cover : delta+cq≤cp ∨ epsilon+cq≤ct) :
 delta*epsilon*K+cq*delta*epsilon≤cp*epsilon*K+ct*delta*K := by
 rcases cover with h | h
 · have h1 := Nat.mul_le_mul_right (epsilon*K) h
   have h2 := Nat.mul_le_mul_left (cq*epsilon) hd
   have h3 : 0≤ct*delta*K := Nat.zero_le _
   grind
 · have h1 := Nat.mul_le_mul_right (delta*K) h
   have h2 := Nat.mul_le_mul_left (cq*delta) he
   have h3 : 0≤cp*epsilon*K := Nat.zero_le _
   grind

theorem sum_payment {α : Type} (xs : List α) (cp cq ct : α → Nat)
 (delta epsilon K : Nat) (hd : delta≤K) (he : epsilon≤K)
 (cover : ∀ v∈xs, delta+cq v≤cp v ∨ epsilon+cq v≤ct v) :
 xs.length*delta*epsilon*K+sumBy xs cq*delta*epsilon≤
 sumBy xs cp*epsilon*K+sumBy xs ct*delta*K := by
 induction xs with
 | nil => simp
 | cons v xs ih =>
   have hv := local_payment (cp v) (cq v) (ct v) delta epsilon K hd he (cover v (by simp))
   have ht := ih (by intro u hu; exact cover u (by simp [hu]))
   simp only [sumBy_cons,List.length_cons]
   grind

/-- Denominator-cleared exact covering bound. With positive delta,epsilon
and K=max(delta,epsilon), division gives the reported rational inequality. -/
theorem graph_budget {n : Nat} (G : Graph n) (p q t delta epsilon K : Nat)
 (hpq : p<q) (hqt : q<t) (hdk : delta≤K) (hek : epsilon≤K)
 (hd : coefficient G p=coefficient G q+delta)
 (he : coefficient G t=coefficient G q+epsilon)
 (deletions : ∀ v, Unimodal (coefficient (deleteVertex G v))) :
 n*delta*epsilon*K+(q*coefficient G q)*delta*epsilon≤
 (p*coefficient G p)*epsilon*K+(t*coefficient G t)*delta*K := by
 have h := sum_payment (List.finRange n) (fun v => inc G v p)
   (fun v => inc G v q) (fun v => inc G v t) delta epsilon K hdk hek
   (by intro v hv; exact vertex_covering G v p q t delta epsilon hpq hqt hd he (deletions v))
 rw [sum_inc,sum_inc,sum_inc] at h
 simpa using h

/-- Exceeding the payment bound forces an actual deletion to keep the
SAME strict valley. It is not merely a scalar feasibility conclusion. -/
theorem preserving_deletion {n : Nat} (G : Graph n) (p q t delta epsilon K : Nat)
 (hdk : delta≤K) (hek : epsilon≤K)
 (hd : coefficient G p=coefficient G q+delta)
 (he : coefficient G t=coefficient G q+epsilon)
 (fail : (p*coefficient G p)*epsilon*K+(t*coefficient G t)*delta*K<
 n*delta*epsilon*K+(q*coefficient G q)*delta*epsilon) :
 ∃ v : Fin n, coefficient (deleteVertex G v) q<coefficient (deleteVertex G v) p ∧
 coefficient (deleteVertex G v) q<coefficient (deleteVertex G v) t := by
 by_cases hex : ∃ v : Fin n, coefficient (deleteVertex G v) q<coefficient (deleteVertex G v) p ∧
   coefficient (deleteVertex G v) q<coefficient (deleteVertex G v) t
 · exact hex
 · exfalso
   have hcover (v : Fin n) : delta+inc G v q≤inc G v p ∨ epsilon+inc G v q≤inc G v t := by
     have h1 := VertexIncidence.incidence_deletion_partition G v p
     have h2 := VertexIncidence.incidence_deletion_partition G v q
     have h3 := VertexIncidence.incidence_deletion_partition G v t
     have hn : ¬(coefficient (deleteVertex G v) q<coefficient (deleteVertex G v) p ∧
       coefficient (deleteVertex G v) q<coefficient (deleteVertex G v) t) := by
       intro h; exact hex ⟨v,h⟩
     omega
   have hs := sum_payment (List.finRange n) (fun v => inc G v p)
     (fun v => inc G v q) (fun v => inc G v t) delta epsilon K hdk hek
     (by intro v hv; exact hcover v)
   rw [sum_inc,sum_inc,sum_inc] at hs
   simp only [List.length_finRange] at hs
   omega

theorem critical_budget (w : Closure.CriticalWitness) (p q t delta epsilon K : Nat)
 (hpq : p<q) (hqt : q<t) (hdk : delta≤K) (hek : epsilon≤K)
 (hd : coefficient w.graph p=coefficient w.graph q+delta)
 (he : coefficient w.graph t=coefficient w.graph q+epsilon) :
 w.n*delta*epsilon*K+(q*coefficient w.graph q)*delta*epsilon≤
 (p*coefficient w.graph p)*epsilon*K+(t*coefficient w.graph t)*delta*K := by
 apply graph_budget w.graph p q t delta epsilon K hpq hqt hdk hek hd he
 intro v
 have hl := deleteVertices_length v
 have hv := v.isLt
 exact critical_inducedOn_unimodal w (deleteVertices v) (deleteVertices_nodup v) (by omega)

theorem preserving_nonunimodality {n : Nat} (G : Graph n) (p q t delta epsilon K : Nat)
 (hpq : p<q) (hqt : q<t) (hdk : delta≤K) (hek : epsilon≤K)
 (hd : coefficient G p=coefficient G q+delta)
 (he : coefficient G t=coefficient G q+epsilon)
 (fail : (p*coefficient G p)*epsilon*K+(t*coefficient G t)*delta*K<
 n*delta*epsilon*K+(q*coefficient G q)*delta*epsilon) :
 ∃ v : Fin n, ¬Unimodal (coefficient (deleteVertex G v)) := by
 obtain ⟨v,hv1,hv2⟩ := preserving_deletion G p q t delta epsilon K hdk hek hd he fail
 refine ⟨v,?_⟩
 intro hu
 have hh := no_valley _ hu p q t hpq hqt
 omega

end Erdos993.ValleyDeletionCover
