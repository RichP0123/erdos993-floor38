import OverlapDeletionBudget
import LeafBalanceConcavity

namespace Erdos993.CentralWindowClosure
open Counting Structure LeafBoundary ForestReturnPhases
set_option maxHeartbeats 800000

def ModeAt (a : Nat → Nat) (m : Nat) : Prop :=
 (∀ r, r<m → a r≤a (r+1)) ∧ (∀ r, m≤r → a (r+1)≤a r)

/-- A local curvature hypothesis is sufficient only after BOTH witness
departures have been localized to its interval. -/
theorem concave_interval (a : Nat → Nat) (lo hi M b : Nat)
 (hlo : lo≤M) (hhi : b<hi) (hMb : M<b)
 (fall : a (M+1)<a M)
 (concave : ∀ r, lo≤r → r+1<hi → a (r+2)+a r≤2*a (r+1)) :
 a (b+1)<a b := by
 have step : ∀ d, M+d<hi → a (M+d+1)<a (M+d) := by
   intro d
   induction d with
   | zero => intro hh; simpa using fall
   | succ d ih =>
     intro hh
     have h1 := ih (by omega)
     have h2 := concave (M+d) (by omega) (by omega)
     have e1 : M+(d+1)=M+d+1 := by omega
     have e2 : M+(d+1)+1=M+d+2 := by omega
     rw [e2,e1]
     omega
 have h := step (b-M) (by omega)
 have he : M+(b-M)=b := by omega
 simpa only [he] using h

/-- Plateau-safe localization for f=d+x e. Neither a normal approximation
nor a statement about the mean is assumed to locate a mode automatically. -/
theorem split_localization (f d e : Nat → Nat) (M b lo hi md me : Nat)
 (hM : 1≤M) (hb : M<b)
 (rec : ∀ r, f (r+1)=d (r+1)+e r)
 (fall : f (M+1)<f M) (rise : f b<f (b+1))
 (hd : ModeAt d md) (he : ModeAt e me)
 (hmdlo : lo≤md) (hmdhi : md≤hi)
 (hmelo : lo≤me+1) (hmehi : me+1≤hi) : lo≤M ∧ b<hi := by
 have em : M-1+1=M := by omega
 have eb : b-1+1=b := by omega
 have rM := rec M
 have rM0 := rec (M-1)
 have rb := rec b
 have rb0 := rec (b-1)
 rw [em] at rM0
 rw [eb] at rb0
 constructor
 · by_cases hm : M<lo
   · have h1 := hd.1 M (by omega)
     have h2 := he.1 (M-1) (by omega)
     rw [em] at h2
     omega
   · omega
 · by_cases hbh : hi≤b
   · have h1 := hd.2 b (by omega)
     have h2 := he.2 (b-1) (by omega)
     rw [eb] at h2
     omega
   · omega

/-- Actual graph bridge. The analytic mode-localization and curvature
premises remain explicit; this is NOT an end-to-end analytic ceiling. -/
theorem critical_window_excluded (w : Closure.CriticalWitness) (v : Fin w.n)
 (lo hi md me : Nat)
 (hd : ModeAt (coefficient (deleteVertex w.graph v)) md)
 (he : ModeAt (coefficient (inducedOn w.graph (closedVertices w.graph v))) me)
 (hmdlo : lo≤md) (hmdhi : md≤hi)
 (hmelo : lo≤me+1) (hmehi : me+1≤hi)
 (concave : ∀ r, lo≤r → r+1<hi →
   coefficient w.graph (r+2)+coefficient w.graph r≤2*coefficient w.graph (r+1)) : False := by
 have hloc := split_localization (coefficient w.graph)
   (coefficient (deleteVertex w.graph v))
   (coefficient (inducedOn w.graph (closedVertices w.graph v)))
   w.M w.b lo hi md me w.positiveFallIndex w.returnAfterFall
   (coefficient_vertex_recurrence w.graph v) w.firstFall w.returningRise
   hd he hmdlo hmdhi hmelo hmehi
 have ht := concave_interval (coefficient w.graph) lo hi w.M w.b
   hloc.1 hloc.2 w.returnAfterFall w.firstFall concave
 have hr := w.returningRise
 omega

end Erdos993.CentralWindowClosure
