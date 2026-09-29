import PrefixPairDensity
import LeafIncidenceBounds
namespace Erdos993.PrefixSmallIncidence
open Counting Structure LeafBoundary RootingBridgeAudit PrefixPairDensity PrefixDegreeSums
set_option maxHeartbeats 8000000

theorem degree_one_unique {n : Nat} (G : Graph n) (v : Fin n) (hd : degree G v≤1)
 (u w : Fin n) (hu : G.adj v u=true) (hw : G.adj v w=true) : u=w := by
 let xs := (List.finRange n).filter (G.adj v)
 have hum : u∈xs := by simp [xs,hu]
 have hwm : w∈xs := by simp [xs,hw]
 have hl : xs.length≤1 := hd
 cases hx : xs with
 | nil => simp [hx] at hum
 | cons a ys =>
   have hy : ys=[] := by cases ys <;> simp_all
   simp only [hx,hy,List.mem_cons,List.not_mem_nil,or_false] at hum hwm
   exact hum.trans hwm.symm

theorem small_neighbor {n : Nat} (G : Graph n) (v u : Fin n)
 (hs : small G v=true) (ha : G.adj v u=true) : small G u=true := by
 have hh : degree G v≤1 ∧ ∀w,G.adj v w=true → degree G w≤1 := of_decide_eq_true hs
 have hu := hh.2 u ha
 apply decide_eq_true
 refine ⟨hu,?_⟩
 intro w hw
 have he := degree_one_unique G u hu w v hw (by rw [G.symm]; exact ha)
 rw [he]
 exact hh.1

theorem edge_incidence_equal {n : Nat} (G : Graph n) (v u : Fin n)
 (hv : degree G v≤1) (hu : degree G u≤1) (ha : G.adj v u=true) (r : Nat) :
 inc G v r=inc G u r := by
 have hlv : ∀w,G.adj v w=true ↔ w=u := by
   intro w
   exact ⟨fun hw => degree_one_unique G v hv w u hw ha,fun he => he ▸ ha⟩
 have hau : G.adj u v=true := by rw [G.symm]; exact ha
 have hlu : ∀w,G.adj u w=true ↔ w=v := by
   intro w
   exact ⟨fun hw => degree_one_unique G u hu w v hw hau,fun he => he ▸ hau⟩
 cases r with
 | zero =>
   have hz (z : Fin n) : inc G z 0=0 := by
     unfold inc
     have he : (independentSets G 0).filter (fun s => s.contains z)=[] := by
       apply List.filter_eq_nil_iff.mpr
       intro s hs
       have hm := (mem_independentSets G 0 s).mp hs
       have he : s=[] := List.length_eq_zero_iff.mp hm.2.1
       simp [he]
     rw [he]; rfl
   rw [hz,hz]
 | succ k =>
   rw [VertexIncidence.incidence_closed_deletion,VertexIncidence.incidence_closed_deletion,
     leaf_residual_eq G v u hlv,leaf_residual_eq G u v hlu]
   have he : leafPairVertices v u=leafPairVertices u v := by
     unfold leafPairVertices deleteVertices
     exact List.erase_comm _ _
   rw [he]

theorem low_degree_occupancy {n : Nat} (G : Graph n) (v : Fin n) (r : Nat)
 (hr : 1≤r) (hn : n≤4*r) (hd : degree G v≤1) : coefficient G r≤5*inc G v r := by
 have hp := VertexIncidence.incidence_deletion_partition G v r
 by_cases he : ∃u,G.adj v u=true
 · obtain ⟨u,hu⟩ := he
   have hne : v≠u := by intro he; subst u; rw [G.loopless] at hu; contradiction
   have hl : ∀w,G.adj v w=true ↔ w=u := by
     intro w
     exact ⟨fun hw => degree_one_unique G v hd w u hw hu,fun he => he ▸ hu⟩
   have hi := LeafIncidence.leaf_incidence_lower G v u hne hl r
   have hb := Nat.mul_le_mul_right (inc G v r) (show n-1≤4*r by omega)
   have hh : r*coefficient (deleteVertex G v) r≤r*(4*inc G v r) := by grind only
   have hx := Nat.le_of_mul_le_mul_left hh (by omega)
   omega
 · have hz : ∀u,G.adj v u=false := by
     intro u
     cases ha : G.adj v u
     · rfl
     · exact False.elim (he ⟨u,ha⟩)
   obtain ⟨k,hk⟩ : ∃k,r=k+1 := ⟨r-1,by omega⟩
   subst r
   have hi := VertexIncidence.incidence_isolate G v hz k
   have hu := graph_extension_upper_add (deleteVertex G v) k
   have hs := deleteVertices_length v
   have hb : (deleteVertices v).length≤4*(k+1) := by omega
   have hm := Nat.mul_le_mul_right (coefficient (deleteVertex G v) k) hb
   have hh : (k+1)*coefficient (deleteVertex G v) (k+1)≤
     (k+1)*(4*coefficient (deleteVertex G v) k) := by grind only
   have hx := Nat.le_of_mul_le_mul_left hh (by omega)
   omega

theorem small_mass_lower {n : Nat} (G : Graph n) (r : Nat) (hr : 1≤r) (hn : n≤4*r) :
 count (small G)*coefficient G r≤5*mass (small G) (fun v => inc G v r) := by
 have h := mass_le (small G) (fun _ => coefficient G r) (fun v => 5*inc G v r)
   (by
     intro v hv
     have hd : degree G v≤1 := (of_decide_eq_true hv).1
     exact low_degree_occupancy G v r hr hn hd)
 rw [PrefixDegreeSums.mass_mul] at h
 have he : mass (small G) (fun _ => coefficient G r)=count (small G)*coefficient G r := by
   have hh := mass_mul (small G) (fun _ => 1) (coefficient G r)
   simpa [Nat.mul_comm,count] using hh
 rw [he] at h
 exact h

end Erdos993.PrefixSmallIncidence
