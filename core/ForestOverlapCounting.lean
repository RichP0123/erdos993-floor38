import GraphExtensionUpper
namespace Erdos993.Overlap
open Counting
set_option maxHeartbeats 8000000

def neighborsIn {n : Nat} (G : Graph n) (s : List (Fin n)) (v : Fin n) : Nat :=
 sumBy s (fun u => if G.adj v u then 1 else 0)

def overlapAt {n : Nat} (G : Graph n) (s : List (Fin n)) (v : Fin n) : Nat :=
 neighborsIn G s v-1

def overlapSet {n : Nat} (G : Graph n) (s : List (Fin n)) : Nat :=
 sumBy (List.finRange n) (overlapAt G s)

def overlap {n : Nat} (G : Graph n) (r : Nat) : Nat :=
 sumBy (independentSets G r) (overlapSet G)

theorem neighborsIn_zero {n : Nat} (G : Graph n) (s : List (Fin n)) (v : Fin n)
 (h : ∀u∈s,G.adj v u=false) : neighborsIn G s v=0 := by
 unfold neighborsIn
 rw [sumBy_congr s _ (fun _ => 0) (by intro u hu; simp [h u hu])]
 simp

theorem selected_neighbors_zero {n : Nat} (G : Graph n) (s : List (Fin n))
 (hs : independent G s=true) (v : Fin n) (hv : v∈s) : neighborsIn G s v=0 :=
 neighborsIn_zero G s v (fun u hu => (independent_iff G s).mp hs v hv u hu)

theorem vertex_exact_charge {n : Nat} (G : Graph n) (s : List (Fin n))
 (hs : independent G s=true) (v : Fin n) :
 1+overlapAt G s v=
 (if decide (v∉s) && s.all (fun u => !(G.adj v u)) then 1 else 0)
 +(if v∈s then 1 else 0)+neighborsIn G s v := by
 by_cases hv : v∈s
 · have hz := selected_neighbors_zero G s hs v hv
   simp [overlapAt,hv,hz]
 · by_cases he : ∃u∈s,G.adj v u=true
   · obtain ⟨u,hu,ha⟩ := he
     have hn : 1≤neighborsIn G s v := by
       have h := sumBy_member_le s (fun w => if G.adj v w then 1 else 0) u hu
       simpa [neighborsIn,ha] using h
     have hh : s.all (fun u => !(G.adj v u))=false := by
       apply Bool.eq_false_iff.mpr
       intro ht
       have h := List.all_eq_true.mp ht u hu
       simp [ha] at h
     simp [hv,hh,overlapAt]
     omega
   · have hn : ∀u∈s,G.adj v u=false := by
       intro u hu
       apply Bool.eq_false_iff.mpr
       intro hh
       exact he ⟨u,hu,hh⟩
     have hz := neighborsIn_zero G s v hn
     have hh : s.all (fun u => !(G.adj v u))=true := by
       apply List.all_eq_true.mpr
       intro u hu
       simp [hn u hu]
     simp [hv,hh,overlapAt,hz]

/-- Exact overlap identity for an independent set in an actual graph. -/
theorem set_exact_count {n : Nat} (G : Graph n) (s : List (Fin n))
 (hn : s.Nodup) (hs : independent G s=true) :
 n+overlapSet G s=(freeVertices G s).length+s.length+selectedDegree G s := by
 have h := sumBy_congr (List.finRange n) (fun v => 1+overlapAt G s v)
   (fun v => (if decide (v∉s) && s.all (fun u => !(G.adj v u)) then 1 else 0)
     +(if v∈s then 1 else 0)+neighborsIn G s v)
   (by intro v hv; exact vertex_exact_charge G s hs v)
 rw [sumBy_add,sumBy_add,sumBy_add,sumBy_const,sumBy_indicator,
   selected_membership_sum s hn] at h
 have hi : sumBy (List.finRange n) (neighborsIn G s)=selectedDegree G s := incidence_sum G s
 rw [hi] at h
 simpa [overlapSet,freeVertices] using h

theorem rank_exact_count {n : Nat} (G : Graph n) (r : Nat) :
 n*coefficient G r+overlap G r=
 (r+1)*coefficient G (r+1)+r*coefficient G r+
 sumBy (independentSets G r) (selectedDegree G) := by
 have h := sumBy_congr (independentSets G r) (fun s => n+overlapSet G s)
   (fun s => (freeVertices G s).length+r+selectedDegree G s) ?_
 · rw [sumBy_add,sumBy_add,sumBy_add,sumBy_const,sumBy_const,
     independentSets_length,graph_extension_counting] at h
   simpa [overlap,Nat.mul_comm] using h
 · intro s hs
   have hm := (mem_independentSets G r s).mp hs
   have hn := List.Sublist.nodup ((mem_subsets _ _).mp hm.1) (finRange_nodup n)
   simpa [hm.2.1] using set_exact_count G s hn hm.2.2

/-- The master identity includes the actual nonnegative overlap count. -/
theorem graph_curvature_overlap_identity {n : Nat} (G : Graph n) (r : Nat) :
 ((r:Int)+1)*(coefficient G (r+1):Int)=
 ((n:Int)-3*(r:Int))*(coefficient G r:Int)+curvature G r+(overlap G r:Int) := by
 have h := congrArg Int.ofNat (rank_exact_count G r)
 unfold curvature
 grind only

end Erdos993.Overlap
