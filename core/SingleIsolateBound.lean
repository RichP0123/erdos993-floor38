import VertexIncidence
namespace Erdos993.SingleIsolate
open Counting Structure LeafBoundary CurvatureProof IsolateCurvature VertexIncidence RootingBridgeAudit

theorem single_isolated_inc {n : Nat} (G : Graph n) (v : Fin n) (r : Nat) :
 isolatedInc G (fun u => decide (u=v)) r=inc G v r := by
 unfold isolatedInc
 have he : sumBy (independentSets G r) (fun s => sumBy s (fun u => if decide (u=v) then 1 else 0))=
     sumBy (independentSets G r) (fun s => if v∈s then 1 else 0) := by
   apply sumBy_congr
   intro s hs
   have hm := (mem_independentSets G r s).mp hs
   have hn := List.Sublist.nodup ((mem_subsets _ _).mp hm.1) (finRange_nodup n)
   simpa using sumBy_equal_indicator s hn v
 rw [he]
 simpa [inc] using sumBy_indicator (independentSets G r) (fun s => s.contains v)

theorem complement_singleton {n : Nat} (v : Fin n) :
 (List.finRange n).filter (fun u => !(decide (u=v)))=deleteVertices v := by
 apply sublist_eq_of_members (List.finRange n) _ _ (finRange_nodup n)
   List.filter_sublist List.erase_sublist
 intro u
 simp [List.Nodup.mem_erase_iff (finRange_nodup n)]

theorem isolate_inclusion_lower {n : Nat} (G : Graph n) (v : Fin n)
 (hi : ∀u,G.adj v u=false) (r : Nat) :
 r*coefficient G r≤n*inc G v r := by
 cases r with
 | zero => simp
 | succ k =>
   have hp := incidence_deletion_partition G v (k+1)
   have he := incidence_isolate G v hi k
   have hu := graph_extension_upper_add (deleteVertex G v) k
   have hl := deleteVertices_length v
   have hn := v.isLt
   have hd : (deleteVertices v).length+1=n := by omega
   rw [←he] at hu
   have hj : (k+1)*coefficient G (k+1)≤((deleteVertices v).length+1)*inc G v (k+1) := by
     rw [←hp]
     simp only [Nat.mul_add,Nat.add_mul,Nat.one_mul] at hu ⊢
     omega
   simpa only [hd] using hj

theorem single_isolate_algebra (n r a I K : Int) (hn : 2≤n)
 (ha : r*a≤n*I)
 (hc : 2*r*a+2*((n-1)-1)*I≤(n-1)*K) : 4*r*a≤n*K := by
 have h1 := Int.mul_le_mul_of_nonneg_left hc (show 0≤n by omega)
 have h2 := Int.mul_le_mul_of_nonneg_left ha (show 0≤2*((n-1)-1) by omega)
 have e1 : n*(2*r*a+2*((n-1)-1)*I)=2*n*r*a+2*((n-1)-1)*(n*I) := by grind
 have e2 : 2*n*r*a+2*((n-1)-1)*(r*a)=(n-1)*(4*r*a) := by grind
 have e3 : n*((n-1)*K)=(n-1)*(n*K) := by grind
 rw [e1,e3] at h1
 have hz : 0≤(n-1)*(n*K-4*r*a) := by
   rw [Int.mul_sub,←e2]
   omega
 have hh := Int.nonneg_of_mul_nonneg_right hz (show 0<n-1 by omega)
 omega

/-- One actual isolate doubles the global curvature lower bound (order>=2).
 This is a graph theorem at every rank, not a padding hypothesis. -/
theorem forest_single_isolate_bound {n : Nat} (G : Graph n) (hf : IsForest G)
 (hn : 2≤n) (v : Fin n) (hi : ∀u,G.adj v u=false) (r : Nat) :
 4*(r:Int)*(coefficient G r:Int)≤(n:Int)*curvature G r := by
 have hc := forest_isolate_curvature G hf (fun u => decide (u=v))
   (by intro u hu; have he : u=v := of_decide_eq_true hu; subst u; exact hi) r
 rw [complement_singleton,single_isolated_inc,deleteVertices_length] at hc
 have hn' : ((n-1:Nat):Int)=(n:Int)-1 := by omega
 rw [hn'] at hc
 have hi' := Int.ofNat_le.mpr (isolate_inclusion_lower G v hi r)
 simp only [Int.natCast_mul] at hi'
 exact single_isolate_algebra n r (coefficient G r) (inc G v r) (curvature G r) (by omega) hi' hc

end Erdos993.SingleIsolate
