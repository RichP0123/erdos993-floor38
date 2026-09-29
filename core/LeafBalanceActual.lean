import LeafBalanceKernel
import PrefixPartitionCounting

namespace Erdos993.LeafBalanceActual
open Counting Structure PrefixPartitionCounting LeafBalanceKernel

def free {n : Nat} (G : Graph n) (s ls : List (Fin n)) : List (Fin n) :=
 ls.filter (fun v => s.all (fun u => !(G.adj u v)))

theorem rank_true {α : Type} (xs : List α) (r : Nat) :
 rankCount (fun _ => true) xs r=BinomialKernel.binom xs.length r := by
 induction xs generalizing r with
 | nil => cases r <;> simp [rankCount,subsets,BinomialKernel.binom]
 | cons v xs ih =>
   cases r with
   | zero => simp [rankCount_zero,BinomialKernel.zero_rank]
   | succ r => rw [rankCount_cons_succ,ih,ih]; simp [BinomialKernel.binom,Nat.add_comm]

theorem fixed_core {n : Nat} (G : Graph n) (s ls : List (Fin n))
 (hl : ∀ u∈ls, ∀ v∈ls, G.adj u v=false) (r : Nat) :
 rankCount (fun t => independent G (s++t)) ls r=
 if independent G s then BinomialKernel.binom (free G s ls).length r else 0 := by
 by_cases hs : independent G s=true
 · have he : rankCount (fun t => independent G (s++t)) ls r=
       rankCount (fun t => true && t.all (fun v => s.all (fun u => !(G.adj u v)))) ls r := by
     unfold rankCount
     apply sumBy_congr
     intro t ht
     have hsub := ((mem_subsets t ls).mp ht).subset
     have hp : independent G (s++t)=t.all (fun v => s.all (fun u => !(G.adj u v))) := by
       apply Bool.eq_iff_iff.mpr
       constructor
       · intro hind
         apply List.all_eq_true.mpr
         intro v hv
         apply List.all_eq_true.mpr
         intro u hu
         have ha := (independent_iff G (s++t)).mp hind u (by simp [hu]) v (by simp [hv])
         simp [ha]
       · intro hall
         apply (independent_iff G (s++t)).mpr
         intro u hu v hv
         rcases List.mem_append.mp hu with hu | hu
         · rcases List.mem_append.mp hv with hv | hv
           · exact (independent_iff G s).mp hs u hu v hv
           · have hvall := List.all_eq_true.mp hall v hv
             have hh := List.all_eq_true.mp hvall u hu
             simpa using hh
         · rcases List.mem_append.mp hv with hv | hv
           · have huall := List.all_eq_true.mp hall u hu
             have hh := List.all_eq_true.mp huall v hv
             have ha : G.adj v u=false := by simpa using hh
             rw [G.symm u v]
             exact ha
           · exact hl u (hsub hu) v (hsub hv)
     simp only [hp,Bool.true_and]
   rw [he,rankCount_restrict,rank_true]
   simp [hs,free]
 · have hfalse : independent G s=false := Bool.eq_false_iff.mpr hs
   have he : rankCount (fun t => independent G (s++t)) ls r=0 := by
     unfold rankCount
     have hz : ∀ t, independent G (s++t)=false := by
       intro t
       apply Bool.eq_false_iff.mpr
       intro h
       exact hs (independent_append_left G s t h)
     simp [hz]
   simp [hfalse,he]

theorem split_rank {n : Nat} (G : Graph n) (s ls : List (Fin n)) (r : Nat) :
 sumBy (subsets ls) (fun t => if (s++t).length=r then
     (if independent G (s++t) then 1 else 0) else 0)=
 if s.length≤r then rankCount (fun t => independent G (s++t)) ls (r-s.length) else 0 := by
 by_cases hr : s.length≤r
 · simp only [hr,if_true,rankCount,List.length_append]
   apply sumBy_congr
   intro t ht
   have he : s.length+t.length=r ↔ t.length=r-s.length := by omega
   simp [he]
 · have he : ∀ t : List (Fin n), ¬s.length+t.length=r := by
     intro t; omega
   simp [hr,he]

def terms {n : Nat} (G : Graph n) (core ls : List (Fin n)) : List (Nat × Nat) :=
 ((subsets core).filter (independent G)).map (fun s => (s.length,(free G s ls).length))

/-- Actual independent-set correspondence for any vertex partition with
 independent complement. The kernel expansion is proved, not assumed. -/
theorem expansion {n : Nat} (G : Graph n) (core ls : List (Fin n))
 (partition : (core++ls).Perm (List.finRange n))
 (hl : ∀ u∈ls, ∀ v∈ls, G.adj u v=false) :
 coefficient G=mixture (terms G core ls) := by
 funext r
 have hp := rankCount_perm partition (independent G) (independent_permInvariant G) r
 rw [rankCount_graph] at hp
 rw [←hp]
 unfold rankCount
 rw [sum_subsets_append]
 change _=sumBy _ _
 rw [terms,sumBy_map,sumBy_filter]
 apply sumBy_congr
 intro s hs
 rw [split_rank,fixed_core G s ls hl (r-s.length)]
 cases hind : independent G s <;> by_cases hr : s.length≤r <;>
   simp [hr,atom]

/-- Graph-measurable center bounds over actual independent core sets. -/
theorem actual_return_spread {n : Nat} (G : Graph n) (core ls : List (Fin n))
 (partition : (core++ls).Perm (List.finRange n))
 (hl : ∀ u∈ls, ∀ v∈ls, G.adj u v=false) (lo hi M b : Nat)
 (lower : ∀ s∈subsets core, independent G s=true → lo≤2*s.length+(free G s ls).length)
 (upper : ∀ s∈subsets core, independent G s=true → 2*s.length+(free G s ls).length≤hi)
 (hb : M<b) (fall : coefficient G (M+1)<coefficient G M)
 (rise : coefficient G b<coefficient G (b+1)) : lo+2*(b-M+1)≤hi := by
 rw [expansion G core ls partition hl] at fall rise
 apply return_requires_spread (terms G core ls) lo hi M b _ _ hb fall rise
 · intro p hp
   obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hp
   exact lower s (List.mem_filter.mp hs).1 (List.mem_filter.mp hs).2
 · intro p hp
   obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hp
   exact upper s (List.mem_filter.mp hs).1 (List.mem_filter.mp hs).2

theorem actual_width_three_unimodal {n : Nat} (G : Graph n) (core ls : List (Fin n))
 (partition : (core++ls).Perm (List.finRange n))
 (hl : ∀ u∈ls, ∀ v∈ls, G.adj u v=false) (lo hi : Nat)
 (lower : ∀ s∈subsets core, independent G s=true → lo≤2*s.length+(free G s ls).length)
 (upper : ∀ s∈subsets core, independent G s=true → 2*s.length+(free G s ls).length≤hi)
 (width : hi≤lo+3) : Unimodal (coefficient G) := by
 apply (Foundation.graph_unimodal_iff_noRecovery G).mpr
 intro M b hb fall
 by_cases h : coefficient G (b+1)≤coefficient G b
 · exact h
 · have hh := actual_return_spread G core ls partition hl lo hi M b lower upper hb fall (by omega)
   omega

end Erdos993.LeafBalanceActual
