import ForestCurvature
namespace Erdos993.Counting

theorem free_volume_upper {n : Nat} (G : Graph n) (s : List (Fin n)) (hs : s.Nodup) :
 (freeVertices G s).length+s.length≤n := by
 have h := sumBy_le (List.finRange n)
   (fun v => (if decide (v∉s) && s.all (fun u => !(G.adj v u)) then 1 else 0)
     +(if v∈s then 1 else 0)) (fun _ => 1) ?_
 · rw [sumBy_add,sumBy_indicator,selected_membership_sum s hs,sumBy_const] at h
   simpa [freeVertices] using h
 · intro v hv
   by_cases hm : v∈s <;> simp [hm]
   split <;> omega

/-- Extension upper bound with no truncated subtraction or support hypothesis. -/
theorem graph_extension_upper_add {n : Nat} (G : Graph n) (r : Nat) :
 (r+1)*coefficient G (r+1)+r*coefficient G r≤n*coefficient G r := by
 have h := sumBy_le (independentSets G r)
   (fun s => (freeVertices G s).length+r) (fun _ => n) ?_
 · rw [sumBy_add,graph_extension_counting,sumBy_const,sumBy_const,independentSets_length] at h
   simpa [Nat.mul_comm] using h
 · intro s hs
   have hm := (mem_independentSets G r s).mp hs
   have hn := List.Sublist.nodup ((mem_subsets _ _).mp hm.1) (finRange_nodup n)
   simpa [hm.2.1] using free_volume_upper G s hn

theorem graph_extension_upper_int {n : Nat} (G : Graph n) (r : Nat) :
 ((r:Int)+1)*(coefficient G (r+1):Int)≤((n:Int)-(r:Int))*(coefficient G r:Int) := by
 have h := Int.ofNat_le.mpr (graph_extension_upper_add G r)
 simp only [Int.natCast_add,Int.natCast_mul,Int.natCast_one] at h
 grind

end Erdos993.Counting
