import LinearFactorUnimodality
namespace Erdos993.SecondGradient
open Counting RootingBridgeAudit

def avoidingSets {n : Nat} (G : Graph n) (v : Fin n) (r : Nat) :=
 (independentSets G r).filter (fun s => !(s.contains v))

/-- Uses ambient degrees in G, NOT degrees after deleting v. -/
def avoidingCurvature {n : Nat} (G : Graph n) (v : Fin n) (r : Nat) : Int :=
 2*(r:Int)*((avoidingSets G v r).length:Int)-
 (sumBy (avoidingSets G v r) (selectedDegree G):Int)

/-- Open formalization obligation. This definition asserts no theorem. -/
def RootedSecondGradient : Prop :=
 ∀ n (G : Graph n), IsForest G → ∀ (v : Fin n) (r : Nat),
 (inc G v (r+1):Int)+((avoidingSets G v r).length:Int)≤
 curvature G (r+1)+avoidingCurvature G v r

/-- Exact equivalence for testing proposed injections; it does not prove the
 inequality on either side. Both finite cardinalities are natural numbers. -/
theorem second_gradient_iff_count_bound {n : Nat} (G : Graph n) (v : Fin n) (r : Nat) :
 ((inc G v (r+1):Int)+((avoidingSets G v r).length:Int)≤
   curvature G (r+1)+avoidingCurvature G v r) ↔
 (sumBy (independentSets G (r+1)) (selectedDegree G)+
  sumBy (avoidingSets G v r) (selectedDegree G)+inc G v (r+1)+(avoidingSets G v r).length≤
  2*(r+1)*coefficient G (r+1)+2*r*(avoidingSets G v r).length) := by
 unfold curvature avoidingCurvature
 have cast2 : ((2:Nat):Int)=2 := by decide
 constructor
 · intro h
   apply Int.ofNat_le.mp
   simp only [Int.natCast_add,Int.natCast_mul,Int.natCast_one,cast2]
   simp only [Int.natCast_add,Int.natCast_one] at h
   omega
 · intro h
   have hi := Int.ofNat_le.mpr h
   simp only [Int.natCast_add,Int.natCast_mul,Int.natCast_one,cast2] at hi
   simp only [Int.natCast_add,Int.natCast_one]
   omega

end Erdos993.SecondGradient
