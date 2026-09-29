import ForestDeletionSeparation
namespace Erdos993.LeafIncidence
open Counting Structure LeafBoundary RootingBridgeAudit

theorem leaf_incidence_lower {n : Nat} (G : Graph n) (l v : Fin n)
 (hlv : l≠v) (hl : ∀u,G.adj l u=true ↔ u=v) (r : Nat) :
 r*coefficient (deleteVertex G l) r≤(n-1)*inc G l r := by
 cases r with
 | zero => simp
 | succ k =>
   have hrec := actual_leaf_recurrences G l v hlv hl k
   have hinc := VertexIncidence.incidence_deletion_partition G l (k+1)
   have hie : inc G l (k+1)=coefficient (inducedOn G (leafPairVertices l v)) k := by omega
   rw [hie]
   have hsub := induced_filter_coefficient_le G (leafPairVertices l v) (fun u => !(G.adj v u)) k
   have hupper := graph_extension_upper_add (inducedOn G (leafPairVertices l v)) k
   have horder := leafPair_length l v hlv
   have hm := Nat.mul_le_mul_left (k+1) hsub
   have hn : n-1=(leafPairVertices l v).length+1 := by omega
   rw [hn,hrec.2,Nat.mul_add]
   simp only [Nat.add_mul,Nat.one_mul] at hm hupper ⊢
   omega

theorem low_degree_quarter_ratio {n : Nat} (G : Graph n) (v : Fin n) (k : Nat)
 (hk : 1≤k) (hn : n=4*k+1)
 (hl : ∀u w,G.adj v u=true → G.adj v w=true → u=w) :
 5*coefficient (deleteVertex G v) k≤4*coefficient G k := by
 classical
 have hp := VertexIncidence.incidence_deletion_partition G v k
 by_cases he : ∃u,G.adj v u=true
 · obtain ⟨u,hu⟩ := he
   have hvu : v≠u := by intro h; subst u; rw [G.loopless] at hu; contradiction
   have hleaf : ∀w,G.adj v w=true ↔ w=u := by
     intro w; exact ⟨fun h => hl w u h hu,fun h => h ▸ hu⟩
   have hi := leaf_incidence_lower G v u hvu hleaf k
   have hn' : n-1=4*k := by omega
   rw [hn'] at hi
   have hh : k*(coefficient (deleteVertex G v) k)≤k*(4*inc G v k) := by grind
   have hb := Nat.le_of_mul_le_mul_left hh (by omega)
   omega
 · have hz : ∀u,G.adj v u=false := by
     intro u; cases hh : G.adj v u
     · rfl
     · exact False.elim (he ⟨u,hh⟩)
   obtain ⟨t,ht⟩ : ∃t,k=t+1 := ⟨k-1,by omega⟩
   subst k
   have hi := VertexIncidence.incidence_isolate G v hz t
   have hu := graph_extension_upper_add (deleteVertex G v) t
   conv at hu => rhs; lhs; rw [deleteVertices_length,hn]; simp
   have hh : (t+1)*coefficient (deleteVertex G v) (t+1)≤
       (t+1)*(4*coefficient (deleteVertex G v) t) := by grind
   have hb := Nat.le_of_mul_le_mul_left hh (by omega)
   omega

end Erdos993.LeafIncidence

