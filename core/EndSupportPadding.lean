import ForestEndSupport
import IsolatePaddingCounts
namespace Erdos993.EndPadding
open Counting Structure LeafBoundary PaddingCounts

def supportLeaves {n : Nat} (G : Graph n) (l v w : Fin n) :=
 (leafPairVertices l v).filter (fun u => G.adj v u && decide (u≠w))

theorem support_padding_lower {n : Nat} (G : Graph n) (l v w : Fin n)
 (he : ∀ u, G.adj v u=true → u≠w →
   ∀ x y, G.adj u x=true → G.adj u y=true → x=y) (r : Nat) :
 pad (supportLeaves G l v w).length
   (coefficient (inducedOn G ((leafPairVertices l v).filter (fun u => !(G.adj v u))))) r≤
 coefficient (inducedOn G (leafPairVertices l v)) r := by
 let p := fun u => G.adj v u && decide (u≠w)
 have hi : ∀ u∈(leafPairVertices l v).filter p, ∀ x∈leafPairVertices l v, G.adj u x=false := by
   intro u hu x hx
   have hp := (List.mem_filter.mp hu).2
   have hp' : G.adj v u=true ∧ u≠w := by simpa [p] using hp
   have ha := hp'.1
   have hw := hp'.2
   have hv : x≠v := ((List.Nodup.mem_erase_iff (deleteVertices_nodup l)).mp hx).1
   cases hh : G.adj u x with
   | false => rfl
   | true =>
     have eq := he u ha hw x v hh (by rw [G.symm]; exact ha)
     exact False.elim (hv eq)
 have hc := isolated_partition_lower G (leafPairVertices l v) p (fun u => !(G.adj v u)) hi r
 have hid : ((leafPairVertices l v).filter (fun u => !(p u))).filter (fun u => !(G.adj v u))=
     (leafPairVertices l v).filter (fun u => !(G.adj v u)) := by
   rw [List.filter_filter]
   apply List.filter_congr
   intro u hu
   dsimp [p]
   cases hh : G.adj v u <;> simp
 simp only [coefficient_inducedOn] at hc ⊢
 rw [hid] at hc
 exact hc

theorem support_leaves_length {n : Nat} (G : Graph n) (l v w : Fin n)
 (hlv : l≠v) (hl : ∀ u, G.adj l u=true ↔ u=v)
 (hw : w∈leafPairVertices l v) (ha : G.adj v w=true) :
 (supportLeaves G l v w).length+2=degree G v := by
 let xs := (leafPairVertices l v).filter (fun u => G.adj v u)
 have hnod : xs.Nodup := List.Sublist.nodup List.filter_sublist (leafPair_nodup l v)
 have hmem : w∈xs := by simp [xs,hw,ha]
 have he : supportLeaves G l v w=xs.erase w := by
   rw [List.Nodup.erase_eq_filter hnod]
   unfold supportLeaves xs
   rw [List.filter_filter]
   apply List.filter_congr
   intro u hu
   by_cases hh : u=w <;> simp [hh]
 have hdeg : xs.length+1=degree G v := by
   have h1 := filter_complement_lengths (leafPairVertices l v) (fun u => G.adj v u)
   have h2 := leaf_closed_residual_length G l v hlv hl
   have h3 := leafPair_length l v hlv
   dsimp [xs]
   omega
 rw [he]
 have hh := List.length_erase_of_mem hmem
 have hp := List.length_pos_of_mem hmem
 omega

end Erdos993.EndPadding
