import FirstInteriorDegreeTwo
namespace Erdos993.MultipleIsolate
open Counting IsolateCurvature RootingBridgeAudit

theorem isolate_mass_lower {n : Nat} (G : Graph n) (p : Fin n → Bool)
 (hi : ∀v,p v=true → ∀u,G.adj v u=false) (r : Nat) :
 (((List.finRange n).filter p).length:Int)*(r:Int)*(coefficient G r:Int)≤
 (n:Int)*(isolatedInc G p r:Int) := by
 have hh := SeparatedRoot.sum_scaled_bound ((List.finRange n).filter p)
   (fun v => inc G v r) (-(n:Int)) ((r:Int)*(coefficient G r:Int)) 0 ?_
 · rw [sum_inc_filter] at hh
   grind
 · intro v hv
   have ht := Int.ofNat_le.mpr (SingleIsolate.isolate_inclusion_lower G v (hi v (List.mem_filter.mp hv).2) r)
   simp only [Int.natCast_mul] at ht
   dsimp
   grind

theorem multiple_isolate_algebra (n s r a I K : Int) (hs : 0≤s) (hm : s<n)
 (hi : s*r*a≤n*I)
 (hc : 2*r*a+2*(n-s-1)*I≤(n-s)*K) : 2*r*(s+1)*a≤n*K := by
 have hn : 0≤n := by omega
 have h1 := Int.mul_le_mul_of_nonneg_left hc hn
 have h2 := Int.mul_le_mul_of_nonneg_left hi (show 0≤2*(n-s-1) by omega)
 have ht : (n-s)*(2*r*(s+1)*a)≤(n-s)*(n*K) := by grind
 exact Int.le_of_mul_le_mul_left ht (by omega)

/-- s designated isolates multiply the global curvature lower bound by s+1,
 provided at least one vertex remains outside the designated set. -/
theorem forest_multiple_isolate_bound {n : Nat} (G : Graph n) (hf : IsForest G)
 (p : Fin n → Bool) (hi : ∀v,p v=true → ∀u,G.adj v u=false)
 (hs : ((List.finRange n).filter p).length<n) (r : Nat) :
 2*(r:Int)*((((List.finRange n).filter p).length:Int)+1)*(coefficient G r:Int)≤
 (n:Int)*curvature G r := by
 have hc := forest_isolate_curvature G hf p hi r
 have hm := LeafBoundary.filter_complement_lengths (List.finRange n) p
 have he : (((List.finRange n).filter (fun u => !(p u))).length:Int)=
     (n:Int)-(((List.finRange n).filter p).length:Int) := by
   simp only [List.length_finRange] at hm
   omega
 rw [he] at hc
 exact multiple_isolate_algebra n _ r _ _ _ (Int.natCast_nonneg _) (by omega)
   (isolate_mass_lower G p hi r) hc

end Erdos993.MultipleIsolate
