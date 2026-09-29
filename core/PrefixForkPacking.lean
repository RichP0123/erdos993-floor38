import PrefixRootBudget
import ForestOverlapCounting
namespace Erdos993.PrefixForkPacking
open Counting Structure PrefixRootBudget Overlap
set_option maxHeartbeats 8000000

theorem sumBy_weighted_indicator {α : Type} [DecidableEq α]
 (xs : List α) (hx : xs.Nodup) (v : α) (f : α → Nat) :
 sumBy xs (fun u => if u=v then f u else 0)=(if v∈xs then f v else 0) := by
 induction xs with
 | nil => simp
 | cons u xs ih =>
   obtain ⟨hu,hn⟩ := List.nodup_cons.mp hx
   rw [sumBy_cons,ih hn]
   by_cases he : u=v
   · subst u; simp [hu]
   · by_cases hv : v∈xs <;> simp [he,Ne.symm he,hv]

theorem sumBy_nodup_fin {n : Nat} (xs : List (Fin n)) (hx : xs.Nodup) (f : Fin n → Nat) :
 sumBy xs f=sumBy (List.finRange n) (fun v => if v∈xs then f v else 0) := by
 have he := sumBy_congr (List.finRange n)
   (fun v => if v∈xs then f v else 0)
   (fun v => sumBy xs (fun u => if u=v then f u else 0))
   (by intro v hv; exact (sumBy_weighted_indicator xs hx v f).symm)
 rw [he,sumBy_swap]
 symm
 apply sumBy_congr
 intro u hu
 have ht := sumBy_weighted_indicator (List.finRange n) (finRange_nodup n) u (fun _ => f u)
 simpa [eq_comm] using ht

theorem nodup_fin_length_le {n : Nat} (xs : List (Fin n)) (hx : xs.Nodup) : xs.length≤n := by
 have h := sumBy_le (List.finRange n) (fun v => if v∈xs then 1 else 0) (fun _ => 1)
   (by intro v hv; dsimp; split <;> omega)
 rw [←sumBy_nodup_fin xs hx (fun _ => 1),sumBy_const,sumBy_const] at h
 simpa using h

structure Fork (n : Nat) where
 left : Fin n
 right : Fin n
 center : Fin n

def endpoints {n : Nat} : List (Fork n) → List (Fin n)
 | [] => []
 | p::ps => p.left::p.right::endpoints ps

@[simp] theorem endpoints_length {n : Nat} (ps : List (Fork n)) :
 (endpoints ps).length=2*ps.length := by
 induction ps with
 | nil => rfl
 | cons p ps ih => simp [endpoints,ih]; omega

structure Packing {n : Nat} (G : Graph n) (ps : List (Fork n)) : Prop where
 nodup : (endpoints ps).Nodup
 adjacent : ∀p∈ps,G.adj p.center p.left=true ∧ G.adj p.center p.right=true
 low : ∀p∈ps,degree G p.left≤3 ∧ degree G p.right≤3

theorem packing_length {n : Nat} (G : Graph n) (ps : List (Fork n)) (hp : Packing G ps) :
 2*ps.length≤n := by simpa using nodup_fin_length_le (endpoints ps) hp.nodup

def UnusedLow {n : Nat} (G : Graph n) (ps : List (Fork n)) (v : Fin n) : Prop :=
 v∉endpoints ps ∧ degree G v≤3

/-- A maximal endpoint-disjoint family, on the actual vertex set. -/
theorem exists_maximal_packing {n : Nat} (G : Graph n) :
 ∃ps,Packing G ps ∧ ∀v u w,UnusedLow G ps u → UnusedLow G ps w →
   G.adj v u=true → G.adj v w=true → u=w := by
 classical
 obtain ⟨m,⟨ps,hp,hlen⟩,hmax⟩ := bounded_maximum
   (fun m => ∃ps,Packing G ps ∧ ps.length=m) n
   ⟨0,[],⟨by simp [endpoints],by simp,by simp⟩,rfl⟩
   (by intro m hm; obtain ⟨ps,hp,he⟩ := hm; have hh := packing_length G ps hp; omega)
 refine ⟨ps,hp,?_⟩
 intro v u w hu hw hvu hvw
 by_cases he : u=w
 · exact he
 have hne : u≠w := he
 exfalso
 let q : Fork n := ⟨u,w,v⟩
 have hn : Packing G (q::ps) := by
   refine ⟨?_,?_,?_⟩
   · simp only [endpoints,List.nodup_cons,List.mem_cons,not_or]
     exact ⟨⟨hne,hu.1⟩,hw.1,hp.nodup⟩
   · intro p hm
     rcases List.mem_cons.mp hm with he | hm
     · subst p; exact ⟨hvu,hvw⟩
     · exact hp.adjacent p hm
   · intro p hm
     rcases List.mem_cons.mp hm with he | hm
     · subst p; exact ⟨hu.2,hw.2⟩
     · exact hp.low p hm
 have hh := hmax (m+1) ⟨q::ps,hn,by simp [hlen]⟩
 omega

def selectedAt {n : Nat} (s : List (Fin n)) (v : Fin n) (p : Fork n) : Nat :=
 if p.center=v ∧ p.left∈s ∧ p.right∈s then 1 else 0

theorem packing_selected_charge {n : Nat} (G : Graph n) (ps : List (Fork n))
 (ha : ∀p∈ps,G.adj p.center p.left=true ∧ G.adj p.center p.right=true)
 (s : List (Fin n)) (v : Fin n) :
 2*sumBy ps (selectedAt s v)≤sumBy (endpoints ps)
   (fun u => if u∈s ∧ G.adj v u=true then 1 else 0) := by
 induction ps with
 | nil => simp [endpoints]
 | cons p ps ih =>
   have hp := ha p (by simp)
   have ht := ih (by intro q hq; exact ha q (by simp [hq]))
   simp only [sumBy_cons,endpoints]
   by_cases hh : p.center=v ∧ p.left∈s ∧ p.right∈s
   · have hl : G.adj v p.left=true := by rw [←hh.1]; exact hp.1
     have hr : G.adj v p.right=true := by rw [←hh.1]; exact hp.2
     simp only [selectedAt,hh,if_true,hl,hr,and_self]
     omega
   · simp only [selectedAt,hh,if_false,Nat.zero_add]
     omega

theorem packing_neighbors_bound {n : Nat} (G : Graph n) (ps : List (Fork n))
 (hp : Packing G ps) (s : List (Fin n)) (hs : s.Nodup) (v : Fin n) :
 2*sumBy ps (selectedAt s v)≤neighborsIn G s v := by
 have hc := packing_selected_charge G ps hp.adjacent s v
 have he := sumBy_nodup_fin (endpoints ps) hp.nodup
   (fun u => if u∈s ∧ G.adj v u=true then 1 else 0)
 have hh := sumBy_nodup_fin s hs (fun u => if G.adj v u then 1 else 0)
 have hb := sumBy_le (List.finRange n)
   (fun u => if u∈endpoints ps then (if u∈s ∧ G.adj v u=true then 1 else 0) else 0)
   (fun u => if u∈s then (if G.adj v u then 1 else 0) else 0) ?_
 · rw [←he,←hh] at hb
   exact Nat.le_trans hc hb
 · intro u hu
   by_cases hp : u∈endpoints ps <;> by_cases hs : u∈s <;> cases ha : G.adj v u <;> simp [hp,hs,ha]

theorem packing_overlap_at {n : Nat} (G : Graph n) (ps : List (Fork n))
 (hp : Packing G ps) (s : List (Fin n)) (hs : s.Nodup) (v : Fin n) :
 sumBy ps (selectedAt s v)≤overlapAt G s v := by
 have hh := packing_neighbors_bound G ps hp s hs v
 unfold overlapAt
 omega

def pairInc {n : Nat} (G : Graph n) (u w : Fin n) (r : Nat) : Nat :=
 sumBy (independentSets G r) (fun s => if u∈s ∧ w∈s then 1 else 0)

theorem selectedAt_sum {n : Nat} (s : List (Fin n)) (p : Fork n) :
 sumBy (List.finRange n) (fun v => selectedAt s v p)=
 (if p.left∈s ∧ p.right∈s then 1 else 0) := by
 by_cases hh : p.left∈s ∧ p.right∈s
 · have he := sumBy_congr (List.finRange n) (fun v => selectedAt s v p)
     (fun v => if v=p.center then 1 else 0) ?_
   · rw [he,sumBy_equal_indicator _ (finRange_nodup n)]; simp [hh]
   · intro v hv
     simp [selectedAt,hh.1,hh.2,eq_comm]
 · have he := sumBy_congr (List.finRange n) (fun v => selectedAt s v p) (fun _ => 0) ?_
   · rw [he]; simp [hh]
   · intro v hv
     simp only [selectedAt]
     split
     · rename_i h
       exact False.elim (hh h.2)
     · rfl

/-- Pair inclusion counts are paid by distinct overlap units at their centers. -/
theorem packing_overlap_rank {n : Nat} (G : Graph n) (ps : List (Fork n))
 (hp : Packing G ps) (r : Nat) :
 sumBy ps (fun p => pairInc G p.left p.right r)≤overlap G r := by
 have h := sumBy_le (independentSets G r)
   (fun s => sumBy (List.finRange n) (fun v => sumBy ps (selectedAt s v)))
   (overlapSet G) ?_
 · have he (s : List (Fin n)) :
     sumBy (List.finRange n) (fun v => sumBy ps (selectedAt s v))=
     sumBy ps (fun p => if p.left∈s ∧ p.right∈s then 1 else 0) := by
     rw [sumBy_swap]
     exact sumBy_congr ps _ _ (by intro p hp; exact selectedAt_sum s p)
   rw [sumBy_congr _ _ _ (by intro s hs; exact he s),sumBy_swap] at h
   exact h
 · intro s hs
   have hm := (mem_independentSets G r s).mp hs
   have hn := List.Sublist.nodup ((mem_subsets _ _).mp hm.1) (finRange_nodup n)
   exact sumBy_le (List.finRange n) _ _ (by intro v hv; exact packing_overlap_at G ps hp s hn v)

end Erdos993.PrefixForkPacking
