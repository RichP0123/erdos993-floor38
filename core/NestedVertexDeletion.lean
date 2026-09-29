import FirstInteriorRootSlope
namespace Erdos993.NestedDeletion
open Counting Structure SecondGradient WeightedInduced

theorem contains_induced_map {n : Nat} (xs : List (Fin n)) (hx : xs.Nodup)
 (i : Fin xs.length) (s : List (Fin xs.length)) :
 (s.map (fun j => xs[j.val])).contains xs[i.val]=s.contains i := by
 simp only [List.contains_eq_mem,decide_eq_decide]
 constructor
 · intro h
   obtain ⟨j,hj,he⟩ := List.mem_map.mp h
   have hij := list_vertex_injective xs hx j i he
   simpa [hij] using hj
 · intro h
   exact List.mem_map.mpr ⟨i,h,rfl⟩

theorem coefficient_delete_inducedOn {n : Nat} (G : Graph n)
 (xs : List (Fin n)) (hx : xs.Nodup) (i : Fin xs.length) (r : Nat) :
 coefficient (deleteVertex (inducedOn G xs) i) r=
 coefficient (inducedOn G (xs.erase xs[i.val])) r := by
 have hw := weighted_inducedOn G xs r (fun s => if !(s.contains xs[i.val]) then 1 else 0)
 simp only [contains_induced_map xs hx i] at hw
 rw [sumBy_indicator] at hw
 change (avoidingSets (inducedOn G xs) i r).length=_ at hw
 rw [avoiding_coefficient] at hw
 rw [hw,coefficient_inducedOn,List.Nodup.erase_eq_filter hx,←rankCount_restrict]
 unfold rankCount
 rw [sumBy_filter]
 apply sumBy_congr
 intro s hs
 dsimp
 simp only [VertexIncidence.all_avoid]
 by_cases hr : s.length=r <;> cases (independent G s) <;> cases (s.contains xs[i.val]) <;> simp [hr]

end Erdos993.NestedDeletion


