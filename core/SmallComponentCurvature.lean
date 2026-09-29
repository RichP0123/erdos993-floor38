import FirstInteriorLargeSupport
namespace Erdos993.SmallComponent
open Counting Structure LeafBoundary RootingBridgeAudit CurvatureProof

theorem leaf_occupation_lower {n : Nat} (G : Graph n) (l v : Fin n)
 (hlv : l≠v) (hl : ∀u,G.adj l u=true ↔ u=v) (r : Nat) :
 r*coefficient G r≤(n+r-1)*inc G l r := by
 have h := LeafIncidence.leaf_incidence_lower G l v hlv hl r
 have hi := VertexIncidence.incidence_deletion_partition G l r
 have hn := l.isLt
 have he : n+r-1=(n-1)+r := by omega
 rw [←hi,he,Nat.mul_add,Nat.add_mul]
 omega

theorem leaf_neighbor_incidence {n : Nat} (G : Graph n) (l v : Fin n)
 (hlv : l≠v) (hl : ∀u,G.adj l u=true ↔ u=v) (r : Nat) :
 inc G v r≤inc G l r := by
 cases r with
 | zero =>
   have h := VertexIncidence.incidence_deletion_partition G v 0
   rw [Extraction.coefficient_zero,Extraction.coefficient_zero] at h
   omega
 | succ r =>
   have hrec := (actual_leaf_recurrences G l v hlv hl r).1
   have hp := VertexIncidence.incidence_deletion_partition G l (r+1)
   have hli : inc G l (r+1)=coefficient (inducedOn G (leafPairVertices l v)) r := by omega
   rw [hli,VertexIncidence.incidence_closed_deletion]
   have ha : G.adj v l=true := by rw [G.symm]; exact (hl v).mpr rfl
   have hfilter : (deleteVertices v).filter (fun u => !(G.adj v u))=
       (leafPairVertices l v).filter (fun u => !(G.adj v u)) := by
     unfold leafPairVertices deleteVertices
     rw [List.erase_comm]
     conv => rhs; rw [←List.erase_filter]
     have hnot : l∉((List.finRange n).erase v).filter (fun u => !(G.adj v u)) := by simp [ha]
     rw [List.erase_of_not_mem hnot]
   rw [hfilter]
   exact induced_filter_coefficient_le G (leafPairVertices l v) (fun u => !(G.adj v u)) r

theorem small_component_algebra (k a i K : Int) (hk : 2≤k) (ha : 0≤a)
 (hi : k*a≤(5*k-2)*i)
 (hc : 2*k*a+2*(4*k-7)*i≤(4*k-4)*K) : 3*a≤4*K := by
 have h1 := Int.mul_le_mul_of_nonneg_left hc (show 0≤5*k-2 by omega)
 have h2 := Int.mul_le_mul_of_nonneg_left hi (show 0≤2*(4*k-7) by omega)
 have h3 := Int.mul_nonneg (show 0≤12*(k+2)*(k-1) by
   exact Int.mul_nonneg (by omega) (by omega)) ha
 have ht : ((4*k-4)*(5*k-2))*(3*a)≤((4*k-4)*(5*k-2))*(4*K) := by grind
 exact Int.le_of_mul_le_mul_left ht (Int.mul_pos (by omega) (by omega))

theorem three_vertex_component_bound {n : Nat} (G : Graph n) (hf : IsForest G)
 (p : Fin n → Bool) (hc : ∀u v,G.adj u v=true → p u=p v)
 (hc3 : ((List.finRange n).filter p).length=3)
 (l v : Fin n) (hlv : l≠v) (hl : ∀u,G.adj l u=true ↔ u=v) (hp : p l=true)
 (k : Nat) (hk : 2≤k) (hn : n+1=4*k)
 (hmax : ∀u,p u=true → inc G u k≤inc G l k) :
 3*(coefficient G k:Int)≤4*curvature G k := by
 let b := (List.finRange n).filter (fun u => !(p u))
 have hbsize : b.length+3=n := by
   have hh := filter_complement_lengths (List.finRange n) p
   rw [hc3,List.length_finRange] at hh
   dsimp [b]; omega
 have hsum := SeparatedRoot.sum_scaled_bound b (fun u => inc G u k) 2
     (2*(inc G l k:Int)) (curvature G k) ?_
 · have hi := IsolateCurvature.isolated_inc_partition G p k
   have hmaxsum := sumBy_le ((List.finRange n).filter p) (fun u => inc G u k)
     (fun _ => inc G l k) (by intro u hu; exact hmax u (List.mem_filter.mp hu).2)
   rw [sumBy_const,hc3,IsolateCurvature.sum_inc_filter] at hmaxsum
   have hbi : sumBy b (fun u => inc G u k)=IsolateCurvature.isolatedInc G (fun u => !(p u)) k :=
     IsolateCurvature.sum_inc_filter G (fun u => !(p u)) k
   rw [hbi] at hsum
   have hlo := Int.ofNat_le.mpr (leaf_occupation_lower G l v hlv hl k)
   have hn' : n+k-1=5*k-2 := by omega
   rw [hn'] at hlo
   simp only [Int.natCast_mul] at hlo
   have hnki : ((5*k-2:Nat):Int)=5*(k:Int)-2 := by omega
   rw [hnki] at hlo
   have hcount := congrArg Int.ofNat hi
   have hmi := Int.ofNat_le.mpr hmaxsum
   have hbis : (b.length:Int)=4*(k:Int)-4 := by omega
   rw [hbis] at hsum
   exact small_component_algebra (k:Int) _ _ _ (by omega) (Int.natCast_nonneg _) hlo (by grind)
 · intro u hu
   have hup : p u=false := by simpa using (List.mem_filter.mp hu).2
   have hh := SeparatedRoot.forest_separated_pointed G hf p hc l u hp hup k
   grind

/-- The three vertices are an actual P3 component: both endpoints are leaves
 and the middle vertex has exactly those two neighbors. -/
theorem forest_p3_component_bound {n : Nat} (G : Graph n) (hf : IsForest G)
 (l v z : Fin n) (hlv : l≠v) (hlz : l≠z) (hvz : v≠z)
 (hl : ∀u,G.adj l u=true ↔ u=v) (hz : ∀u,G.adj z u=true ↔ u=v)
 (hv : ∀u,G.adj v u=true ↔ u=l ∨ u=z)
 (k : Nat) (hk : 2≤k) (hn : n+1=4*k) :
 3*(coefficient G k:Int)≤4*curvature G k := by
 let p := fun u => decide (u=l ∨ u=v ∨ u=z)
 have hin : ∀u,p u=true → ∀w,G.adj u w=true → p w=true := by
   intro u hu w hw
   have he : u=l ∨ u=v ∨ u=z := of_decide_eq_true hu
   rcases he with he | he | he
   · subst u; have hh := (hl w).mp hw; simp [p,hh]
   · subst u; rcases (hv w).mp hw with hh | hh <;> simp [p,hh]
   · subst u; have hh := (hz w).mp hw; simp [p,hh]
 have hc : ∀u w,G.adj u w=true → p u=p w := by
   intro u w huw
   cases hu : p u <;> cases hw : p w
   · rfl
   · have hh := hin w hw u (by rw [G.symm]; exact huw); rw [hu] at hh; contradiction
   · have hh := hin u hu w huw; rw [hw] at hh; contradiction
   · rfl
 have hc3 : ((List.finRange n).filter p).length=3 := by
   rw [←sumBy_indicator]
   have he : (fun u => if p u then 1 else 0)=(fun u => if u∈[l,v,z] then 1 else 0) := by
     funext u; simp [p]
   rw [he]
   have hnd : ([l,v,z] : List (Fin n)).Nodup := by simp [hlv,hlz,hvz]
   simpa using selected_membership_sum [l,v,z] hnd
 have hcl := leaf_neighbor_incidence G l v hlv hl k
 have hcz := leaf_neighbor_incidence G z v (Ne.symm hvz) hz k
 by_cases hmax : inc G z k≤inc G l k
 · apply three_vertex_component_bound G hf p hc hc3 l v hlv hl (by simp [p]) k hk hn
   intro u hu
   have he : u=l ∨ u=v ∨ u=z := of_decide_eq_true hu
   rcases he with he | he | he <;> subst u <;> omega
 · apply three_vertex_component_bound G hf p hc hc3 z v (Ne.symm hvz) hz (by simp [p]) k hk hn
   intro u hu
   have he : u=l ∨ u=v ∨ u=z := of_decide_eq_true hu
   rcases he with he | he | he <;> subst u <;> omega

end Erdos993.SmallComponent
