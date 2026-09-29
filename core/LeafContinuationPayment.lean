import SupportCoreRelationships
namespace Erdos993.LeafContinuation
open Counting Structure CurvatureProof RootingBridgeAudit PaddingCounts

theorem leaf_coefficient_ratio {n : Nat} (G : Graph n) (l v : Fin n)
 (hlv : l≠v) (hl : ∀u,G.adj l u=true ↔ u=v) (r : Nat) :
 ((n-1)+r)*coefficient (deleteVertex G l) r≤(n-1)*coefficient G r := by
 have h := LeafIncidence.leaf_incidence_lower G l v hlv hl r
 have hp := VertexIncidence.incidence_deletion_partition G l r
 rw [←hp,Nat.add_mul,Nat.mul_add]
 omega

theorem leaf_continuation_algebra (k q q1 u u1 x : Int) (hk : 2≤k) (hq : 0≤q)
 (hr : q≤3*q1) (hu : (5*k-1)*q≤(4*k-1)*u)
 (hu1 : (5*k-2)*q1≤(4*k-1)*u1)
 (hb : 2*k*(u+u1)+2*(4*k-1)*u1≤4*k*x) : 3*q≤2*x := by
 have h1 := Int.mul_le_mul_of_nonneg_left hb (show 0≤3*(4*k-1) by omega)
 have h2 := Int.mul_le_mul_of_nonneg_left hu (show 0≤6*k by omega)
 have h3 := Int.mul_le_mul_of_nonneg_left hu1 (show 0≤3*(10*k-2) by omega)
 have h4 := Int.mul_le_mul_of_nonneg_left hr
   (show 0≤(10*k-2)*(5*k-2) by exact Int.mul_nonneg (by omega) (by omega))
 have h5 := Int.mul_nonneg (show 0≤4*(4*k-1)*(k-2) by
   exact Int.mul_nonneg (by omega) (by omega)) hq
 have ht : (12*k*(4*k-1))*(3*q)≤(12*k*(4*k-1))*(2*x) := by grind
 exact Int.le_of_mul_le_mul_left ht (Int.mul_pos (by omega) (by omega))

theorem curvature_sum_slope {nh nq : Nat} (H : Graph nh) (Q : Graph nq)
 (k : Nat) (hn : nh=4*k+1) (hq : nq+1=4*k)
 (hb : 2*(coefficient Q k:Int)≤curvature H k+curvature Q k) :
 coefficient H k+coefficient Q k≤coefficient H (k+1)+coefficient Q (k+1) := by
 have hg := graph_curvature_growth H k
 have hqg := graph_curvature_growth Q k
 have hnhi : (nh:Int)=4*(k:Int)+1 := by omega
 have hnqi : (nq:Int)=4*(k:Int)-1 := by omega
 rw [hnhi] at hg
 rw [hnqi] at hqg
 have ht : ((k:Int)+1)*((coefficient H k:Int)+(coefficient Q k:Int))≤
     ((k:Int)+1)*((coefficient H (k+1):Int)+(coefficient Q (k+1):Int)) := by grind
 have hh := Int.le_of_mul_le_mul_left ht (by omega)
 omega

theorem leaf_core_slope {nh nu : Nat} (H : Graph nh) (U : Graph nu) (uf : IsForest U)
 (l v : Fin nu) (hlv : l≠v) (hl : ∀u,U.adj l u=true ↔ u=v)
 (k : Nat) (hk : 2≤k) (hn : nh=4*k+1) (hu : nu=4*k)
 (hp : coefficient H k=coefficient U k+coefficient U (k-1))
 (hb : 2*(k:Int)*(coefficient H k:Int)+2*(4*(k:Int)-1)*(coefficient U (k-1):Int)≤
     4*(k:Int)*curvature H k) :
 coefficient H k+coefficient (deleteVertex U l) k≤
 coefficient H (k+1)+coefficient (deleteVertex U l) (k+1) := by
 let Q := deleteVertex U l
 have qf := deleteVertex_isForest U uf l
 have hqo : (deleteVertices l).length+1=4*k := by rw [deleteVertices_length]; omega
 have hi : k-1+1=k := by omega
 have he := graph_extension_upper_add Q (k-1)
 rw [hi] at he
 have hei := Int.ofNat_le.mpr he
 have hqi : ((deleteVertices l).length:Int)=4*(k:Int)-1 := by omega
 have hki : ((k-1:Nat):Int)=(k:Int)-1 := by omega
 simp only [Int.natCast_add,Int.natCast_mul,hqi,hki] at hei
 have hback : (coefficient Q k:Int)≤3*(coefficient Q (k-1):Int) := by
   have ht : (k:Int)*(coefficient Q k:Int)≤(k:Int)*(3*(coefficient Q (k-1):Int)) := by grind
   exact Int.le_of_mul_le_mul_left ht (by omega)
 have h0 := Int.ofNat_le.mpr (leaf_coefficient_ratio U l v hlv hl k)
 have h1 := Int.ofNat_le.mpr (leaf_coefficient_ratio U l v hlv hl (k-1))
 have hui : ((nu-1:Nat):Int)=4*(k:Int)-1 := by omega
 simp only [Int.natCast_add,Int.natCast_mul,hui,hki] at h0 h1
 have hpi := congrArg Int.ofNat hp
 have hx := leaf_continuation_algebra (k:Int) (coefficient Q k:Int) (coefficient Q (k-1):Int)
   (coefficient U k:Int) (coefficient U (k-1):Int) (curvature H k) (by omega) (Int.natCast_nonneg _)
   hback (by grind) (by grind) (by grind)
 have hqc := forest_curvature_bound Q qf k
 have hqn := forest_curvature_nonnegative Q qf k
 have hs := Int.mul_le_mul_of_nonneg_right (show ((deleteVertices l).length:Int)≤4*(k:Int) by omega) hqn
 have hhalf : (coefficient Q k:Int)≤2*curvature Q k := by
   have ht : (2*(k:Int))*(coefficient Q k:Int)≤(2*(k:Int))*(2*curvature Q k) := by grind
   exact Int.le_of_mul_le_mul_left ht (by omega)
 exact curvature_sum_slope H Q k hn hqo (by omega)

theorem critical_two_leaf_leaf_core (w : Closure.CriticalWitness)
 (hn : w.n+1=4*w.M) (l v z : Fin w.n) (hlv : l≠v)
 (hl : ∀u,w.graph.adj l u=true ↔ u=v)
 (hz : z∈LeafBoundary.leafPairVertices l v) (ha : w.graph.adj v z=true)
 (he : ∀u,w.graph.adj v u=true → u≠z → ∀x y,w.graph.adj u x=true → w.graph.adj u y=true → x=y)
 (hs : (EndPadding.supportLeaves w.graph l v z).length=1)
 (i j : Fin (SupportCore.coreVertices w.graph l v z).length)
 (hi : (SupportCore.coreVertices w.graph l v z)[i.val]=z) (hij : i≠j)
 (hleaf : ∀u,(inducedOn w.graph (SupportCore.coreVertices w.graph l v z)).adj i u=true ↔ u=j) : False := by
 let H := inducedOn w.graph (LeafBoundary.leafPairVertices l v)
 let U := inducedOn w.graph (SupportCore.coreVertices w.graph l v z)
 let k := w.M-1
 have hmin := InteriorDegreeTwo.critical_order_above_half w
 have hk : 2≤k := by dsimp [k]; omega
 have hh := LeafBoundary.leafPair_length l v hlv
 have hcore := SupportCore.core_length w.graph l v z
 rw [hs] at hcore
 have hnH : (LeafBoundary.leafPairVertices l v).length=4*k+1 := by dsimp [k]; omega
 have hnU : (SupportCore.coreVertices w.graph l v z).length=4*k := by omega
 have hnd : (SupportCore.coreVertices w.graph l v z).Nodup :=
   List.Sublist.nodup List.filter_sublist (LeafBoundary.leafPair_nodup l v)
 have uf : IsForest U := inducedOn_isForest w.graph w.forest _ hnd
 have hf : IsForest H := inducedOn_isForest w.graph w.forest _ (LeafBoundary.leafPair_nodup l v)
 have hq (r : Nat) : coefficient (deleteVertex U i) r=
     coefficient (inducedOn w.graph ((LeafBoundary.leafPairVertices l v).filter (fun u => !(w.graph.adj v u)))) r := by
   rw [NestedDeletion.coefficient_delete_inducedOn w.graph _ hnd i r,hi,SupportCore.core_delete_continuation w.graph l v z ha]
 have hp := SupportCore.core_factor w.graph l v z he k
 rw [hs] at hp
 have hkr : k-1+1=k := by omega
 have hp' : coefficient H k=coefficient U k+coefficient U (k-1) := by
   have hpp : pad 1 (coefficient U) k=coefficient U k+coefficient U (k-1) := by
     conv => lhs; rw [←hkr]
     simp only [pad,hkr]
   exact hp.trans hpp
 have hb := SupportCore.core_curvature_budget w.graph w.forest l v z hz he hs (k-1)
 rw [hkr] at hb
 have hki : ((k-1:Nat):Int)+1=(k:Int) := by omega
 have hnu : ((SupportCore.coreVertices w.graph l v z).length:Int)=4*(k:Int) := by omega
 rw [hki,hnu] at hb
 have cert := leaf_core_slope H U uf i j hij hleaf k hk hnH hnU hp' hb
 rw [hq,hq] at cert
 have pre := LeafBoundary.forest_prefix_step H hf k (by omega)
 have hidx : k+1=w.M := by dsimp [k]; omega
 rw [hidx] at cert pre
 exact LeafBoundary.critical_leaf_certificate_impossible w l v hlv hl pre cert

end Erdos993.LeafContinuation

