import PrefixPairIncidence
namespace Erdos993.PrefixPartitionCounting
open Counting Structure PrefixRootBudget
set_option maxHeartbeats 8000000

theorem sum_subsets_append {α : Type} (xs ys : List α) (f : List α → Nat) :
 sumBy (subsets (xs++ys)) f=
 sumBy (subsets xs) (fun s => sumBy (subsets ys) (fun t => f (s++t))) := by
 induction xs generalizing f with
 | nil => simp [subsets]
 | cons a xs ih =>
   simp only [List.cons_append,subsets,sumBy_append,sumBy_map]
   rw [ih f,ih (fun s => f (a::s))]

theorem independent_append_left {n : Nat} (G : Graph n) (s t : List (Fin n))
 (h : independent G (s++t)=true) : independent G s=true := by
 apply (independent_iff G s).mpr
 intro u hu v hv
 exact (independent_iff G (s++t)).mp h u (by simp [hu]) v (by simp [hv])

theorem independent_append_right {n : Nat} (G : Graph n) (s t : List (Fin n))
 (h : independent G (s++t)=true) : independent G t=true := by
 apply (independent_iff G t).mpr
 intro u hu v hv
 exact (independent_iff G (s++t)).mp h u (by simp [hu]) v (by simp [hv])

theorem append_cell_bound {n : Nat} (G : Graph n) (s t : List (Fin n)) (r : Nat) :
 (if (s++t).length=r then (if independent G (s++t) then 1 else 0) else 0)≤
 (if independent G s then (if s.length≤r then
   (if t.length=r-s.length then (if independent G t then 1 else 0) else 0) else 0) else 0) := by
 by_cases hi : independent G (s++t)=true
 · have hs := independent_append_left G s t hi
   have ht := independent_append_right G s t hi
   simp only [hi,hs,ht,if_true,List.length_append]
   split
   · rename_i he
     have hr : s.length≤r := by omega
     have he2 : t.length=r-s.length := by omega
     simp [hr,he2]
   · exact Nat.zero_le _
 · have hi0 : independent G (s++t)=false := Bool.eq_false_iff.mpr hi
   simp [hi0]

/-- Deleting cross edges only increases the number of independent sets. -/
theorem partition_upper {n : Nat} (G : Graph n) (xs ys : List (Fin n)) (r : Nat) :
 rankCount (independent G) (xs++ys) r≤
 sumBy (subsets xs) (fun s => if independent G s then
   (if s.length≤r then rankCount (independent G) ys (r-s.length) else 0) else 0) := by
 unfold rankCount
 rw [sum_subsets_append]
 apply sumBy_le
 intro s hs
 dsimp only
 have h := sumBy_le (subsets ys)
   (fun t => if (s++t).length=r then (if independent G (s++t) then 1 else 0) else 0)
   (fun t => if independent G s then (if s.length≤r then
     (if t.length=r-s.length then (if independent G t then 1 else 0) else 0) else 0) else 0)
   (by intro t ht; exact append_cell_bound G s t r)
 cases hi : independent G s <;> by_cases hr : s.length≤r <;> simpa [hi,hr] using h

theorem rankCount_predicate_le {α : Type} (xs : List α) (P Q : List α → Bool) (r : Nat)
 (h : ∀s∈subsets xs,P s=true → Q s=true) : rankCount P xs r≤rankCount Q xs r := by
 unfold rankCount
 apply sumBy_le
 intro s hs
 dsimp only
 by_cases hr : s.length=r
 · simp only [hr,if_true]
   cases hp : P s
   · simp
   · simp [h s hs hp]
 · simp [hr]

theorem full_partition_upper {n : Nat} (G : Graph n) (p : Fin n → Bool) (r : Nat) :
 coefficient G r≤
 sumBy (subsets ((List.finRange n).filter p)) (fun s => if independent G s then
   (if s.length≤r then coefficient (inducedOn G ((List.finRange n).filter (fun v => !(p v))))
     (r-s.length) else 0) else 0) := by
 have hp := List.filter_append_perm p (List.finRange n)
 have he := rankCount_perm hp (independent G) (independent_permInvariant G) r
 have hb := partition_upper G ((List.finRange n).filter p)
   ((List.finRange n).filter (fun v => !(p v))) r
 rw [he,rankCount_graph] at hb
 simpa [coefficient_inducedOn] using hb

end Erdos993.PrefixPartitionCounting
