import IsolateMassIdentity
namespace Erdos993.InducedIsolate
open Counting Structure IsolateCurvature PaddingCounts

theorem coefficient_induced_twice {n : Nat} (G : Graph n) (xs : List (Fin n))
 (ys : List (Fin xs.length)) (r : Nat) :
 coefficient (inducedOn (inducedOn G xs) ys) r=
 coefficient (inducedOn G (ys.map (fun i => xs[i.val]))) r := by
 rw [coefficient_inducedOn,coefficient_inducedOn,rankCount_map]
 apply rankCount_congr
 intro s
 exact Extraction.independent_inducedGraph G (fun i : Fin xs.length => xs[i.val]) s

theorem induced_filter_map {n : Nat} (xs : List (Fin n)) (p : Fin n → Bool) :
 ((List.finRange xs.length).filter (fun i => p xs[i.val])).map (fun i => xs[i.val])=xs.filter p := by
 have h := congrArg (List.filter p) (finRange_map_get xs)
 simpa only [List.filter_map] using h

theorem induced_filter_length {n : Nat} (xs : List (Fin n)) (p : Fin n → Bool) :
 ((List.finRange xs.length).filter (fun i => p xs[i.val])).length=(xs.filter p).length := by
 have h := congrArg List.length (induced_filter_map xs p)
 simpa only [List.length_map] using h

/-- Exact isolate mass combined with the already verified curvature theorem.
 The spectators and their induced subforest remain actual graph counts. -/
theorem induced_isolate_budget {n : Nat} (G : Graph n) (hf : IsForest G)
 (xs : List (Fin n)) (hx : xs.Nodup) (p t : Fin n → Bool)
 (hi : ∀v∈xs.filter p,∀u∈xs,G.adj v u=false)
 (s : Nat) (hs : (xs.filter p).length=s+1)
 (hm : 1≤(xs.filter (fun u => !(p u))).length) (r : Nat) :
 2*((r:Int)+1)*(coefficient (inducedOn G xs) (r+1):Int)+
 2*(((xs.filter (fun u => !(p u))).length:Int)-1)*((s:Int)+1)*
   (pad s (coefficient (inducedOn G ((xs.filter (fun u => !(p u))).filter t))) r:Int)≤
 ((xs.filter (fun u => !(p u))).length:Int)*curvature (inducedOn G xs) (r+1) := by
 let H := inducedOn G xs
 let pp := fun i : Fin xs.length => p xs[i.val]
 have hhi : ∀v,pp v=true → ∀u,H.adj v u=false := by
   intro v hv u
   exact hi xs[v.val] (List.mem_filter.mpr ⟨List.getElem_mem _,hv⟩) xs[u.val] (List.getElem_mem _)
 have hps : ((List.finRange xs.length).filter pp).length=s+1 := by
   exact (induced_filter_length xs p).trans hs
 have hcore (j : Nat) : coefficient (inducedOn H ((List.finRange xs.length).filter (fun u => !(pp u)))) j=
     coefficient (inducedOn G (xs.filter (fun u => !(p u)))) j := by
   rw [coefficient_induced_twice]
   exact congrArg (fun ys => coefficient (inducedOn G ys) j) (induced_filter_map xs (fun u => !(p u)))
 have hmass := IsolateMass.isolate_mass_identity H pp hhi s hps r
 have hfun : coefficient (inducedOn H ((List.finRange xs.length).filter (fun u => !(pp u))))=
     coefficient (inducedOn G (xs.filter (fun u => !(p u)))) := funext hcore
 rw [hfun] at hmass
 have hpad := pad_mono s _ _
   (fun j => LeafBoundary.induced_filter_coefficient_le G (xs.filter (fun u => !(p u))) t j) r
 have hmasslower := Nat.mul_le_mul_left (s+1) hpad
 rw [←hmass] at hmasslower
 have hc := forest_isolate_curvature H (inducedOn_isForest G hf xs hx) pp hhi (r+1)
 have hlen : ((List.finRange xs.length).filter (fun u => !(pp u))).length=
     (xs.filter (fun u => !(p u))).length := induced_filter_length xs (fun u => !(p u))
 rw [hlen] at hc
 have hmi := Int.ofNat_le.mpr hmasslower
 simp only [Int.natCast_mul,Int.natCast_add,Int.natCast_one] at hmi hc
 have hscaled := Int.mul_le_mul_of_nonneg_left hmi
   (show 0≤2*(((xs.filter (fun u => !(p u))).length:Int)-1) by omega)
 grind

end Erdos993.InducedIsolate
