import WeightedInducedCounting
namespace Erdos993.JointGrowth
open Counting Structure SecondGradient RootingBridgeAudit

theorem rooted_first_growth {n : Nat} (G : Graph n) (hf : IsForest G)
 (v : Fin n) (r : Nat) :
 ((n:Int)-3*(r:Int)+2)*(coefficient G r:Int)≤
 ((r:Int)+1)*(coefficient G (r+1):Int)+2*(coefficient (deleteVertex G v) r:Int) := by
 obtain ⟨R,hr⟩ := ParentConstruction.forest_parent_certificate G hf v
 have hp := CurvatureProof.pointed_curvature R v hr r
 have hg := graph_curvature_growth G r
 have hd := congrArg Int.ofNat (VertexIncidence.incidence_deletion_partition G v r)
 grind

/-- Joint rooted growth with the actual root-deletion order and coefficients.
 The root-avoiding curvature is bounded by the deletion curvature via the
 literal degree partition, not a substituted nominal graph order. -/
theorem rooted_joint_growth {n : Nat} (G : Graph n) (hf : IsForest G)
 (v : Fin n) (r : Nat) (hr : 1≤r) :
 ((n:Int)-3*(r:Int)+1)*(coefficient G r:Int)+
 ((n:Int)+3-3*(r:Int))*(coefficient (deleteVertex G v) (r-1):Int)≤
 ((r:Int)+1)*(coefficient G (r+1):Int)+
 ((r:Int)+1)*(coefficient (deleteVertex G v) r:Int) := by
 cases r with
 | zero => omega
 | succ k =>
   have hs := AttachmentCounting.forest_second_gradient G hf v k
   have hc := WeightedInduced.avoiding_curvature_le_deleted G v k
   have ha := graph_curvature_growth G (k+1)
   have hb := graph_curvature_growth (deleteVertex G v) k
   have hi := congrArg Int.ofNat (VertexIncidence.incidence_deletion_partition G v (k+1))
   rw [WeightedInduced.avoiding_coefficient] at hs
   have hn : 0<n := Nat.lt_of_le_of_lt (Nat.zero_le v.val) v.isLt
   have hl : ((deleteVertices v).length:Int)=(n:Int)-1 := by
     rw [deleteVertices_length]
     omega
   rw [hl] at hb
   simp only [Nat.add_sub_cancel,Int.natCast_add,Int.natCast_one] at ha ⊢
   grind

end Erdos993.JointGrowth
