import IsolateCurvature
namespace Erdos993.VertexIncidence
open Counting Structure LeafBoundary RootingBridgeAudit

theorem rankCount_as_filter {α : Type} (P : List α → Bool) (xs : List α) (r : Nat) :
 rankCount P xs r=((subsets xs).filter (fun s => decide (s.length=r) && P s)).length := by
 unfold rankCount
 have he : (fun s : List α => if s.length=r then (if P s then 1 else 0) else 0)=
     (fun s => if decide (s.length=r) && P s then 1 else 0) := by
   funext s
   by_cases hr : s.length=r <;> simp [hr]
 rw [he,sumBy_indicator]

theorem all_avoid {n : Nat} (v : Fin n) (s : List (Fin n)) :
 s.all (fun u => u != v)= !(s.contains v) := by
 induction s with
 | nil => rfl
 | cons a s ih =>
   simp only [List.all_cons,List.contains_cons,ih]
   by_cases ha : a=v
   · subst a; simp
   · have hab : (a==v)=false := by simp [ha]
     have hba : (v==a)=false := by simp [Ne.symm ha]
     simp [bne,hab,hba]

theorem incidence_deletion_partition {n : Nat} (G : Graph n) (v : Fin n) (r : Nat) :
 inc G v r+coefficient (deleteVertex G v) r=coefficient G r := by
 change inc G v r+coefficient (inducedOn G (deleteVertices v)) r=coefficient G r
 rw [coefficient_inducedOn]
 unfold deleteVertices
 rw [List.Nodup.erase_eq_filter (finRange_nodup n),←rankCount_restrict,rankCount_as_filter]
 have he : ((subsets (List.finRange n)).filter
     (fun s => decide (s.length=r) && (independent G s && s.all (fun u => u != v))))=
     (independentSets G r).filter (fun s => !(s.contains v)) := by
   unfold independentSets
   rw [List.filter_filter]
   apply List.filter_congr
   intro s hs
   rw [all_avoid]
   cases (decide (s.length=r)) <;> cases (independent G s) <;> cases (s.contains v) <;> rfl
 rw [he]
 exact filter_complement_lengths (independentSets G r) (fun s => s.contains v)

theorem incidence_closed_deletion {n : Nat} (G : Graph n) (v : Fin n) (r : Nat) :
 inc G v (r+1)=coefficient (inducedOn G ((deleteVertices v).filter (fun u => !(G.adj v u)))) r := by
 have h1 := incidence_deletion_partition G v (r+1)
 have h2 := coefficient_vertex_recurrence G v r
 omega

theorem incidence_isolate {n : Nat} (G : Graph n) (v : Fin n)
 (hi : ∀u,G.adj v u=false) (r : Nat) :
 inc G v (r+1)=coefficient (deleteVertex G v) r := by
 rw [incidence_closed_deletion]
 have he : (deleteVertices v).filter (fun u => !(G.adj v u))=deleteVertices v := by simp [hi]
 simp only [coefficient_inducedOn]
 rw [he]
 exact (coefficient_inducedOn G (deleteVertices v) r).symm

end Erdos993.VertexIncidence
