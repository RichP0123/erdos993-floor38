import CentralWindowClosure

namespace Erdos993.CardinalityMoments
open Counting Structure LeafBoundary ForestReturnPhases

/-- Zeroth cardinality moment, including rank zero. -/
def massThrough (a : Nat → Nat) : Nat → Nat
 | 0 => a 0
 | b+1 => massThrough a b + a (b+1)

/-- Unnormalized first cardinality moment. -/
def momentThrough (a : Nat → Nat) : Nat → Nat
 | 0 => 0
 | b+1 => momentThrough a b + (b+1)*a (b+1)

def partition {n : Nat} (G : Graph n) : Nat := massThrough (coefficient G) n
def firstMoment {n : Nat} (G : Graph n) : Nat := momentThrough (coefficient G) n

theorem mass_stable (a : Nat → Nat) (n b : Nat) (h : n≤b)
 (hz : ∀ j, n<j → a j=0) : massThrough a b=massThrough a n := by
 induction b with
 | zero =>
   have hn : n=0 := by omega
   subst n
   rfl
 | succ b ih =>
   by_cases hn : n=b+1
   · rw [hn]
   · have hb : n≤b := by omega
     rw [massThrough,ih hb,hz (b+1) (by omega),Nat.add_zero]

theorem moment_stable (a : Nat → Nat) (n b : Nat) (h : n≤b)
 (hz : ∀ j, n<j → a j=0) : momentThrough a b=momentThrough a n := by
 induction b with
 | zero =>
   have hn : n=0 := by omega
   subst n
   rfl
 | succ b ih =>
   by_cases hn : n=b+1
   · rw [hn]
   · have hb : n≤b := by omega
     rw [momentThrough,ih hb,hz (b+1) (by omega),Nat.mul_zero,Nat.add_zero]

theorem split_mass (f d e : Nat → Nat) (h0 : f 0=d 0)
 (rec : ∀ j, f (j+1)=d (j+1)+e j) (b : Nat) :
 massThrough f (b+1)=massThrough d (b+1)+massThrough e b := by
 induction b with
 | zero => simp only [massThrough,rec,h0]; omega
 | succ b ih => simp only [massThrough,rec] at *; omega

theorem split_moment (f d e : Nat → Nat)
 (rec : ∀ j, f (j+1)=d (j+1)+e j) (b : Nat) :
 momentThrough f (b+1)=momentThrough d (b+1)+momentThrough e b+massThrough e b := by
 induction b with
 | zero => simp only [momentThrough,massThrough,rec]; omega
 | succ b ih =>
   simp only [momentThrough,rec,massThrough,Nat.mul_add,Nat.add_mul,Nat.one_mul] at *
   omega

theorem partition_positive {n : Nat} (G : Graph n) : 0<partition G := by
 have h : ∀ b, 1≤massThrough (coefficient G) b := by
   intro b
   induction b with
   | zero => simp [massThrough,Extraction.coefficient_zero]
   | succ b ih => simp only [massThrough]; omega
 exact h n

/-- Exact actual-graph partition function identity, without truncation hypotheses. -/
theorem partition_vertex {n : Nat} (G : Graph n) (v : Fin n) :
 partition G=partition (deleteVertex G v)+
   partition (inducedOn G (closedVertices G v)) := by
 have hv := v.isLt
 have hn : n-1+1=n := by omega
 have hlen := deleteVertices_length v
 have he : (closedVertices G v).length≤n-1 := by
   unfold closedVertices
   exact hlen ▸ List.length_filter_le _ _
 have h0 : coefficient G 0=coefficient (deleteVertex G v) 0 := by
   simp [Extraction.coefficient_zero]
 have h := split_mass (coefficient G) (coefficient (deleteVertex G v))
   (coefficient (inducedOn G (closedVertices G v))) h0 (coefficient_vertex_recurrence G v) (n-1)
 rw [hn] at h
 rw [mass_stable (coefficient (deleteVertex G v)) (deleteVertices v).length n
       (by omega) (fun j hj => coefficient_above_order _ hj),
     mass_stable (coefficient (inducedOn G (closedVertices G v))) _ (n-1)
       he (fun j hj => coefficient_above_order _ hj)] at h
 exact h

/-- Selecting v adds one to the size in the closed-neighborhood minor.
This is the counting identity underlying the actual conditional-mean mixture. -/
theorem firstMoment_vertex {n : Nat} (G : Graph n) (v : Fin n) :
 firstMoment G=firstMoment (deleteVertex G v)+
   firstMoment (inducedOn G (closedVertices G v))+
   partition (inducedOn G (closedVertices G v)) := by
 have hv := v.isLt
 have hn : n-1+1=n := by omega
 have hlen := deleteVertices_length v
 have he : (closedVertices G v).length≤n-1 := by
   unfold closedVertices
   exact hlen ▸ List.length_filter_le _ _
 have h := split_moment (coefficient G) (coefficient (deleteVertex G v))
   (coefficient (inducedOn G (closedVertices G v))) (coefficient_vertex_recurrence G v) (n-1)
 rw [hn] at h
 rw [moment_stable (coefficient (deleteVertex G v)) (deleteVertices v).length n
       (by omega) (fun j hj => coefficient_above_order _ hj),
     moment_stable (coefficient (inducedOn G (closedVertices G v))) _ (n-1)
       he (fun j hj => coefficient_above_order _ hj),
     mass_stable (coefficient (inducedOn G (closedVertices G v))) _ (n-1)
       he (fun j hj => coefficient_above_order _ hj)] at h
 exact h

end Erdos993.CardinalityMoments
