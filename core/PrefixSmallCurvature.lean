import PrefixSmallIncidence
namespace Erdos993.PrefixSmallCurvature
open Counting Structure RootingBridgeAudit PrefixPairDensity PrefixDegreeSums
open PrefixSmallIncidence PrefixRootBudget MarkedInjectionAudit ParentConstruction CurvatureProof
set_option maxHeartbeats 8000000

def smallRoot {n : Nat} {G : Graph n} (R : ParentCertificate G) (v : Fin n) : Bool :=
 small G v && decide (R.parent v=none)
def smallChild {n : Nat} {G : Graph n} (R : ParentCertificate G) (v : Fin n) : Bool :=
 small G v && decide (R.parent v≠none)

theorem small_parent_root {n : Nat} {G : Graph n} (R : ParentCertificate G)
 (v u : Fin n) (hs : small G v=true) (hp : R.parent v=some u) :
 smallRoot R u=true ∧ G.adj v u=true := by
 have ha := (R.edges v u).mpr (Or.inl hp)
 have hu := small_neighbor G v u hs ha
 have hd : degree G u≤1 := (of_decide_eq_true hu).1
 have hr : R.parent u=none := by
   cases hw : R.parent u
   · rfl
   · rename_i w
     have haw := (R.edges u w).mpr (Or.inl hw)
     have he := degree_one_unique G u hd w v haw (by rw [G.symm]; exact ha)
     subst w
     exact False.elim (R.noTwoCycle v u ⟨hp,hw⟩)
 exact ⟨by simp [smallRoot,hu,hr],ha⟩

theorem small_root_mass {n : Nat} {G : Graph n} (R : ParentCertificate G) (r : Nat) :
 mass (small G) (fun v => inc G v r)≤2*mass (smallRoot R) (fun v => inc G v r) := by
 have h := mass_le (smallChild R) (fun v => inc G v r)
   (neighborWeight G (smallRoot R) (fun u => inc G u r)) ?_
 · rw [weighted_degree_swap] at h
   have hh := mass_le (smallRoot R)
     (fun u => degreeIn G (smallChild R) u*inc G u r) (fun u => inc G u r) ?_
   · have he : mass (small G) (fun v => inc G v r)=
       mass (smallRoot R) (fun v => inc G v r)+mass (smallChild R) (fun v => inc G v r) := by
       unfold mass
       rw [←sumBy_add]
       apply sumBy_congr
       intro v hv
       dsimp only [smallRoot,smallChild]
       by_cases hs : small G v=true <;> by_cases hr : R.parent v=none <;> simp [hs,hr]
     omega
   · intro u hu
     have hs : small G u=true := by
       have hh : small G u=true ∧ R.parent u=none := by simpa [smallRoot] using hu
       exact hh.1
     have hd : degree G u≤1 := (of_decide_eq_true hs).1
     have hi := degreeIn_le G (smallChild R) u
     have hm := Nat.mul_le_mul_right (inc G u r) (show degreeIn G (smallChild R) u≤1 by omega)
     simpa using hm
 · intro v hv
   have hh : small G v=true ∧ R.parent v≠none := by simpa [smallChild] using hv
   cases hp : R.parent v
   · exact False.elim (hh.2 hp)
   · rename_i u
     obtain ⟨hu,ha⟩ := small_parent_root R v u hh.1 hp
     have hs := small_neighbor G v u hh.1 ha
     have hvd : degree G v≤1 := (of_decide_eq_true hh.1).1
     have hud : degree G u≤1 := (of_decide_eq_true hs).1
     have he := edge_incidence_equal G v u hvd hud ha r
     dsimp only
     conv => lhs; rw [he]
     exact neighborWeight_member_le G (smallRoot R) (fun u => inc G u r) v u ha hu

theorem smallRoot_le_roots {n : Nat} {G : Graph n} (R : ParentCertificate G) (r : Nat) :
 mass (smallRoot R) (fun v => inc G v r)≤sumBy (roots R) (fun v => inc G v r) := by
 unfold roots
 rw [sumBy_filter]
 apply sumBy_le
 intro v hv
 dsimp only [smallRoot]
 by_cases hs : small G v=true <;> by_cases hr : R.parent v=none <;> simp [hs,hr]

theorem smallRoot_extra {n : Nat} {G : Graph n} (R : ParentCertificate G)
 (z : Fin n) (hz : small G z=false) (hr : R.parent z=none) (r : Nat) :
 mass (smallRoot R) (fun v => inc G v r)+inc G z r≤
 sumBy (roots R) (fun v => inc G v r) := by
 have hz' := PrefixForkPacking.sumBy_weighted_indicator (List.finRange n) (finRange_nodup n) z
   (fun v => inc G v r)
 have h := sumBy_le (List.finRange n)
   (fun v => (if smallRoot R v then inc G v r else 0)+(if v=z then inc G v r else 0))
   (fun v => if R.parent v=none then inc G v r else 0) ?_
 · rw [sumBy_add,hz'] at h
   unfold roots
   rw [sumBy_filter]
   simpa [mass] using h
 · intro v hv
   dsimp only [smallRoot]
   by_cases he : v=z
   · subst v; simp [hz,hr]
   · by_cases hs : small G v=true <;> by_cases hp : R.parent v=none <;> simp [he,hs,hp]

theorem forest_small_mass_curvature {n : Nat} (G : Graph n) (hf : IsForest G) (r : Nat) :
 (mass (small G) (fun v => inc G v r):Int)≤curvature G r := by
 cases n with
 | zero => simpa [mass] using forest_curvature_nonnegative G hf r
 | succ m =>
   obtain ⟨R,_⟩ := forest_parent_certificate G hf ⟨0,by omega⟩
   have h := small_root_mass R r
   have h' := smallRoot_le_roots R r
   have hc := all_roots_curvature R r
   omega

theorem forest_small_pointed {n : Nat} (G : Graph n) (hf : IsForest G)
 (z : Fin n) (hz : small G z=false) (r : Nat) :
 (mass (small G) (fun v => inc G v r):Int)+2*(inc G z r:Int)≤curvature G r := by
 obtain ⟨R,hr⟩ := forest_parent_certificate G hf z
 have h := small_root_mass R r
 have h' := smallRoot_extra R z hz hr r
 have hc := all_roots_curvature R r
 omega

/-- Small-component curvature, with no division or positivity premise on a_r. -/
theorem forest_small_global {n : Nat} (G : Graph n) (hf : IsForest G) (r : Nat) :
 2*(r:Int)*(coefficient G r:Int)+((n:Int)-2)*
   (mass (small G) (fun v => inc G v r):Int)≤(n:Int)*curvature G r := by
 let M := mass (small G) (fun v => inc G v r)
 let xs := (List.finRange n).filter (fun v => !(small G v))
 have h := sum_int_const_bound xs (fun v => M+2*inc G v r) (2*curvature G r) ?_
 · rw [sumBy_add,sumBy_const,sumBy_mul_left] at h
   have he : sumBy xs (fun v => inc G v r)=mass (fun v => !(small G v)) (fun v => inc G v r) :=
     sumBy_filter _ _ _
   rw [he] at h
   have hp := mass_complement (small G) (fun v => inc G v r)
   rw [sum_inc] at hp
   have hn := count_complement (small G)
   have hx : xs.length=count (fun v => !(small G v)) := (count_length _).symm
   rw [hx] at h
   have hc := forest_small_mass_curvature G hf r
   have hm := Int.mul_le_mul_of_nonneg_left hc (Int.natCast_nonneg (count (small G)))
   have hp' := congrArg (fun x : Nat => (x:Int)) hp
   have hn' := congrArg (fun x : Nat => (x:Int)) hn
   dsimp only [M] at h
   simp only [Int.natCast_add,Int.natCast_mul] at h hp' hn'
   rw [Int.mul_left_comm (count (fun v => !(small G v)):Int) 2] at h
   rw [←hn',Int.mul_assoc 2 (r:Int),←hp']
   simp only [Int.add_mul,Int.sub_mul,Int.mul_add] at h ⊢
   omega
 · intro v hv
   have hs : small G v=false := by simpa [xs] using (List.mem_filter.mp hv).2
   have hc := forest_small_pointed G hf v hs r
   dsimp only [M]
   simp only [Int.natCast_add,Int.natCast_mul]
   omega

end Erdos993.PrefixSmallCurvature
