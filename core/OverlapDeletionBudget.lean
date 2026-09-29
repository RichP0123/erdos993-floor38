import ValleyDeletionCover
import GraphExtensionUpper

namespace Erdos993.OverlapDeletionBudget
open Counting Structure LeafBoundary RootingBridgeAudit
set_option maxHeartbeats 800000

/-- Corrects the return's rank-domain claim: at a consecutive return the
outer ranks always sum to less than the graph order. No forest hypothesis. -/
theorem return_rank_sum {n : Nat} (G : Graph n) (p b : Nat) (hp : p<b)
 (rise : coefficient G b<coefficient G (b+1)) : p+(b+1)<n := by
 have hu := graph_extension_upper_add G b
 have hs := Nat.mul_lt_mul_of_pos_left rise (Nat.zero_lt_succ b)
 have hn : 2*b+1<n := by
   by_cases hn0 : n≤2*b+1
   · have hm := Nat.mul_le_mul_right (coefficient G b) hn0
     simp only [Nat.add_mul,Nat.one_mul] at *
     grind
   · omega
 omega

/-- A deletion which removes a valley has its endpoint product bounded by
the larger original endpoint times its middle coefficient. -/
theorem local_product (x y z A C M : Nat) (hx : x≤A) (hy : y≤C)
 (ha : A≤M) (hc : C≤M) (cover : x≤z ∨ y≤z) : x*y≤M*z := by
 rcases cover with h | h
 · have h1 := Nat.mul_le_mul h (Nat.le_trans hy hc)
   grind
 · have h1 := Nat.mul_le_mul (Nat.le_trans hx ha) h
   exact h1

theorem deletion_product {n : Nat} (G : Graph n) (v : Fin n)
 (p q t M : Nat) (hp : coefficient G p≤M) (ht : coefficient G t≤M)
 (cover : coefficient (deleteVertex G v) p≤coefficient (deleteVertex G v) q ∨
   coefficient (deleteVertex G v) t≤coefficient (deleteVertex G v) q) :
 coefficient (deleteVertex G v) p*coefficient (deleteVertex G v) t≤
 M*coefficient (deleteVertex G v) q := by
 have h1 := VertexIncidence.incidence_deletion_partition G v p
 have h2 := VertexIncidence.incidence_deletion_partition G v t
 exact local_product _ _ _ _ _ M (by omega) (by omega) hp ht cover

/-- Keeps the product of the two actual vertex incidences instead of discarding it. -/
theorem local_overlap {n : Nat} (G : Graph n) (v : Fin n)
 (p q t M : Nat) (hp : coefficient G p≤M) (ht : coefficient G t≤M)
 (cover : coefficient (deleteVertex G v) p≤coefficient (deleteVertex G v) q ∨
   coefficient (deleteVertex G v) t≤coefficient (deleteVertex G v) q) :
 coefficient G p*coefficient G t + inc G v p*inc G v t + M*inc G v q ≤
 coefficient G t*inc G v p + coefficient G p*inc G v t + M*coefficient G q := by
 have hh := deletion_product G v p q t M hp ht cover
 have h1 := VertexIncidence.incidence_deletion_partition G v p
 have h2 := VertexIncidence.incidence_deletion_partition G v q
 have h3 := VertexIncidence.incidence_deletion_partition G v t
 rw [←h1,←h2,←h3]
 simp only [Nat.add_mul,Nat.mul_add]
 simp only [Nat.mul_comm] at *
 omega

theorem sum_overlap {α : Type} (xs : List α) (cp cq ct : α → Nat)
 (A B C M : Nat)
 (hlocal : ∀ v∈xs, A*C+cp v*ct v+M*cq v≤C*cp v+A*ct v+M*B) :
 xs.length*(A*C)+sumBy xs (fun v => cp v*ct v)+M*sumBy xs cq≤
 C*sumBy xs cp+A*sumBy xs ct+xs.length*(M*B) := by
 induction xs with
 | nil => simp
 | cons v xs ih =>
   have hv := hlocal v (by simp)
   have hh := ih (by intro u hu; exact hlocal u (by simp [hu]))
   simp only [sumBy_cons,List.length_cons]
   grind

theorem graph_budget {n : Nat} (G : Graph n) (p q t M : Nat)
 (hp : coefficient G p≤M) (ht : coefficient G t≤M)
 (cover : ∀ v, coefficient (deleteVertex G v) p≤coefficient (deleteVertex G v) q ∨
   coefficient (deleteVertex G v) t≤coefficient (deleteVertex G v) q) :
 n*(coefficient G p*coefficient G t) +
 sumBy (List.finRange n) (fun v => inc G v p*inc G v t) + M*(q*coefficient G q) ≤
 coefficient G t*(p*coefficient G p)+coefficient G p*(t*coefficient G t)+n*(M*coefficient G q) := by
 have hh := sum_overlap (List.finRange n) (fun v => inc G v p)
   (fun v => inc G v q) (fun v => inc G v t)
   (coefficient G p) (coefficient G q) (coefficient G t) M
   (by intro v hv; exact local_overlap G v p q t M hp ht (cover v))
 rw [sum_inc,sum_inc,sum_inc] at hh
 simpa using hh

/-- Actual minimum-forest endpoint. M can be chosen as max(a_p,a_t).
The graph and incidence correspondence are proved, not supplied as scalar premises. -/
theorem critical_budget (w : Closure.CriticalWitness) (p q t M : Nat)
 (hpq : p<q) (hqt : q<t) (hp : coefficient w.graph p≤M) (ht : coefficient w.graph t≤M) :
 w.n*(coefficient w.graph p*coefficient w.graph t) +
 sumBy (List.finRange w.n) (fun v => inc w.graph v p*inc w.graph v t) + M*(q*coefficient w.graph q) ≤
 coefficient w.graph t*(p*coefficient w.graph p)+coefficient w.graph p*(t*coefficient w.graph t)+w.n*(M*coefficient w.graph q) := by
 apply graph_budget w.graph p q t M hp ht
 intro v
 have hl := deleteVertices_length v
 have hv := v.isLt
 exact ValleyDeletionCover.no_valley _
   (critical_inducedOn_unimodal w (deleteVertices v) (deleteVertices_nodup v) (by omega)) p q t hpq hqt

theorem preserving_deletion {n : Nat} (G : Graph n) (p q t M : Nat)
 (hp : coefficient G p≤M) (ht : coefficient G t≤M)
 (fail : coefficient G t*(p*coefficient G p)+coefficient G p*(t*coefficient G t)+n*(M*coefficient G q) <
 n*(coefficient G p*coefficient G t) +
 sumBy (List.finRange n) (fun v => inc G v p*inc G v t) + M*(q*coefficient G q)) :
 ∃ v : Fin n, coefficient (deleteVertex G v) q<coefficient (deleteVertex G v) p ∧
 coefficient (deleteVertex G v) q<coefficient (deleteVertex G v) t := by
 by_cases hex : ∃ v : Fin n, coefficient (deleteVertex G v) q<coefficient (deleteVertex G v) p ∧
   coefficient (deleteVertex G v) q<coefficient (deleteVertex G v) t
 · exact hex
 · exfalso
   have hc (v : Fin n) : coefficient (deleteVertex G v) p≤coefficient (deleteVertex G v) q ∨
     coefficient (deleteVertex G v) t≤coefficient (deleteVertex G v) q := by
     have hn : ¬(coefficient (deleteVertex G v) q<coefficient (deleteVertex G v) p ∧
       coefficient (deleteVertex G v) q<coefficient (deleteVertex G v) t) := by
       intro h; exact hex ⟨v,h⟩
     omega
   have hb := graph_budget G p q t M hp ht hc
   omega

theorem preserving_nonunimodality {n : Nat} (G : Graph n) (p q t M : Nat)
 (hpq : p<q) (hqt : q<t) (hp : coefficient G p≤M) (ht : coefficient G t≤M)
 (fail : coefficient G t*(p*coefficient G p)+coefficient G p*(t*coefficient G t)+n*(M*coefficient G q) <
 n*(coefficient G p*coefficient G t) +
 sumBy (List.finRange n) (fun v => inc G v p*inc G v t) + M*(q*coefficient G q)) :
 ∃ v : Fin n, ¬Unimodal (coefficient (deleteVertex G v)) := by
 obtain ⟨v,hv1,hv2⟩ := preserving_deletion G p q t M hp ht fail
 refine ⟨v,?_⟩
 intro hu
 have hh := ValleyDeletionCover.no_valley _ hu p q t hpq hqt
 omega

end Erdos993.OverlapDeletionBudget
