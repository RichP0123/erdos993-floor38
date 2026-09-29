import PrefixForkPacking
import VertexIncidence
namespace Erdos993.PrefixPairIncidence
open Counting Structure LeafBoundary PrefixForkPacking
set_option maxHeartbeats 8000000

theorem required_rank_zero {α : Type} [DecidableEq α] (P : List α → Bool)
 (a : α) (xs : List α) (ha : a∉xs) (r : Nat) :
 rankCount (fun s => P s && decide (a∈s)) xs r=0 := by
 unfold rankCount
 have he := sumBy_congr (subsets xs)
   (fun s => if s.length=r then (if P s && decide (a∈s) then 1 else 0) else 0)
   (fun _ => 0) ?_
 · rw [he]; simp
 · intro s hs
   have hh : a∉s := fun hm => ha (((mem_subsets s xs).mp hs).subset hm)
   simp [hh]

theorem required_rank_cons {α : Type} [DecidableEq α] (P : List α → Bool)
 (a : α) (xs : List α) (ha : a∉xs) (r : Nat) :
 rankCount (fun s => P s && decide (a∈s)) (a::xs) (r+1)=
 rankCount (fun s => P (a::s)) xs r := by
 rw [rankCount_cons_succ,required_rank_zero P a xs ha (r+1)]
 simp

theorem pairInc_as_rankCount {n : Nat} (G : Graph n) (u w : Fin n) (r : Nat) :
 pairInc G u w r=rankCount
   (fun s => (independent G s && decide (w∈s)) && decide (u∈s)) (List.finRange n) r := by
 unfold pairInc independentSets
 rw [sumBy_filter]
 unfold rankCount
 apply sumBy_congr
 intro s hs
 by_cases hr : s.length=r <;> by_cases hu : u∈s <;> by_cases hw : w∈s <;>
   cases hi : independent G s <;> simp [hr,hu,hw,hi]

def pairClosedVertices {n : Nat} (G : Graph n) (u w : Fin n) : List (Fin n) :=
 ((deleteVertices u).erase w).filter (fun z => !(G.adj u z) && !(G.adj w z))

theorem pairClosed_nodup {n : Nat} (G : Graph n) (u w : Fin n) :
 (pairClosedVertices G u w).Nodup :=
 ((deleteVertices_nodup u).erase w).filter _

theorem pairClosed_mem {n : Nat} (G : Graph n) (u w z : Fin n) :
 z∈pairClosedVertices G u w ↔ z≠u ∧ z≠w ∧ G.adj u z=false ∧ G.adj w z=false := by
 unfold pairClosedVertices deleteVertices
 rw [List.Nodup.erase_eq_filter (finRange_nodup n)]
 rw [List.Nodup.erase_eq_filter ((finRange_nodup n).filter _)]
 simp [and_assoc,and_comm]

theorem pair_predicate_restrict {n : Nat} (G : Graph n) (u w : Fin n)
 (hn : G.adj u w=false) (s : List (Fin n)) :
 independent G (u::w::s)=
 (independent G s && s.all (fun z => !(G.adj u z) && !(G.adj w z))) := by
 apply Bool.eq_iff_iff.mpr
 simp only [independent_cons_iff,List.mem_cons,forall_eq_or_imp,Bool.and_eq_true,
   List.all_eq_true]
 constructor
 · intro h
   exact ⟨h.1.1,fun z hz => ⟨by simpa using h.2.2 z hz,by simpa using h.1.2 z hz⟩⟩
 · intro h
   exact ⟨⟨h.1,fun z hz => by simpa using (h.2 z hz).2⟩,hn,fun z hz => by simpa using (h.2 z hz).1⟩

/-- Removing the two required independent vertices is an exact bijection. -/
theorem pairInc_closed_deletion {n : Nat} (G : Graph n) (u w : Fin n)
 (hne : u≠w) (hn : G.adj u w=false) (r : Nat) :
 pairInc G u w (r+2)=coefficient (inducedOn G (pairClosedVertices G u w)) r := by
 let rest := (deleteVertices u).erase w
 have hu : u∉deleteVertices u := List.Nodup.not_mem_erase (finRange_nodup n)
 have hw : w∈deleteVertices u := by
   unfold deleteVertices
   rw [List.Nodup.erase_eq_filter (finRange_nodup n)]
   simp [Ne.symm hne]
 have hwr : w∉rest := List.Nodup.not_mem_erase (deleteVertices_nodup u)
 have hur : u∉w::rest := by
   intro hh
   rcases List.mem_cons.mp hh with he | hh
   · exact hne he
   · exact hu (List.mem_of_mem_erase hh)
 have hp : (List.finRange n).Perm (u::w::rest) :=
   (List.perm_cons_erase (show u∈List.finRange n by simp)).trans
     ((List.perm_cons_erase hw).cons u)
 let P := fun s : List (Fin n) => (independent G s && decide (w∈s)) && decide (u∈s)
 have hP : PermInvariant P := by
   intro s t hst
   have hi := independent_permInvariant G s t hst
   simp only [P,hi,hst.mem_iff]
 rw [pairInc_as_rankCount,rankCount_perm hp P hP]
 rw [show r+2=(r+1)+1 by omega,required_rank_cons _ u (w::rest) hur]
 have he : (fun s : List (Fin n) => independent G (u::s) && decide (w∈u::s))=
   (fun s => independent G (u::s) && decide (w∈s)) := by
   funext s
   simp [Ne.symm hne]
 rw [he,required_rank_cons _ w rest hwr]
 have he2 : (fun s => independent G (u::w::s))=
   (fun s => independent G s && s.all (fun z => !(G.adj u z) && !(G.adj w z))) := by
   funext s
   exact pair_predicate_restrict G u w hn s
 rw [he2,rankCount_restrict,coefficient_inducedOn]
 rfl

end Erdos993.PrefixPairIncidence
