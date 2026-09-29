import LeafAttachmentCounting
namespace Erdos993.WeightedInduced
open Counting Structure SecondGradient

theorem weighted_inducedOn {n : Nat} (G : Graph n) (xs : List (Fin n))
 (r : Nat) (f : List (Fin n) → Nat) :
 sumBy (independentSets (inducedOn G xs) r)
   (fun s => f (s.map (fun i : Fin xs.length => xs[i.val])))=
 sumBy ((subsets xs).filter (fun s => decide (s.length=r) && independent G s)) f := by
 unfold independentSets
 rw [sumBy_filter,sumBy_filter]
 conv => rhs; rw [←finRange_map_get xs,subsets_map,sumBy_map]
 apply sumBy_congr
 intro s hs
 simp only [List.length_map]
 rw [←Extraction.independent_inducedGraph]
 rfl

theorem subsets_filter {α : Type} (xs : List α) (p : α → Bool) :
 subsets (xs.filter p)=(subsets xs).filter (fun s => s.all p) := by
 induction xs with
 | nil => simp [subsets]
 | cons a xs ih =>
   cases hp : p a <;> simp [hp,subsets,ih,List.filter_append,List.filter_map,Function.comp_def]

theorem avoiding_as_deleted_lists {n : Nat} (G : Graph n) (v : Fin n) (r : Nat) :
 ((subsets (deleteVertices v)).filter (fun s => decide (s.length=r) && independent G s))=
 avoidingSets G v r := by
 unfold deleteVertices avoidingSets independentSets
 rw [List.Nodup.erase_eq_filter (finRange_nodup n),subsets_filter,List.filter_filter,List.filter_filter]
 apply List.filter_congr
 intro s hs
 rw [VertexIncidence.all_avoid]
 cases (s.contains v) <;> cases (decide (s.length=r)) <;> cases (independent G s) <;> rfl

theorem avoiding_coefficient {n : Nat} (G : Graph n) (v : Fin n) (r : Nat) :
 (avoidingSets G v r).length=coefficient (deleteVertex G v) r := by
 change _=coefficient (inducedOn G (deleteVertices v)) r
 rw [coefficient_inducedOn,VertexIncidence.rankCount_as_filter,avoiding_as_deleted_lists]

theorem degree_inducedOn {n : Nat} (G : Graph n) (xs : List (Fin n))
 (u : Fin xs.length) :
 degree (inducedOn G xs) u=(xs.filter (fun w => G.adj xs[u.val] w)).length := by
 change ((List.finRange xs.length).filter (fun w => G.adj xs[u.val] xs[w.val])).length=_
 have h := congrArg (fun ys : List (Fin n) => (ys.filter (fun w => G.adj xs[u.val] w)).length) (finRange_map_get xs)
 dsimp at h
 rw [List.filter_map,List.length_map] at h
 exact h

theorem degree_deleted {n : Nat} (G : Graph n) (v : Fin n)
 (u : Fin (deleteVertices v).length) :
 degree G (deleteVertices v)[u.val]=degree (deleteVertex G v) u+
   (if G.adj (deleteVertices v)[u.val] v then 1 else 0) := by
 unfold deleteVertex
 rw [degree_inducedOn]
 unfold degree
 have hp := List.perm_cons_erase (show v∈List.finRange n by simp)
 have h := hp.filter (fun w => G.adj (deleteVertices v)[u.val] w)
 have hl := h.length_eq
 change _=(List.filter _ (deleteVertices v)).length+_
 change (List.filter (fun w => G.adj (deleteVertices v)[u.val] w) (List.finRange n)).length=
   (List.filter (fun w => G.adj (deleteVertices v)[u.val] w) (v::deleteVertices v)).length at hl
 cases ha : G.adj (deleteVertices v)[u.val] v <;> simp [ha] at hl ⊢ <;> omega

theorem selected_degree_deleted {n : Nat} (G : Graph n) (v : Fin n)
 (s : List (Fin (deleteVertices v).length)) :
 selectedDegree G (s.map (fun i => (deleteVertices v)[i.val]))=
 selectedDegree (deleteVertex G v) s+
 sumBy s (fun i => if G.adj (deleteVertices v)[i.val] v then 1 else 0) := by
 unfold selectedDegree
 rw [sumBy_map,←sumBy_add]
 apply sumBy_congr
 intro u hu
 exact degree_deleted G v u

theorem avoiding_curvature_le_deleted {n : Nat} (G : Graph n) (v : Fin n) (r : Nat) :
 avoidingCurvature G v r≤curvature (deleteVertex G v) r := by
 have hw := weighted_inducedOn G (deleteVertices v) r (selectedDegree G)
 rw [avoiding_as_deleted_lists] at hw
 have hd : sumBy (independentSets (deleteVertex G v) r) (selectedDegree (deleteVertex G v))≤
     sumBy (avoidingSets G v r) (selectedDegree G) := by
   rw [←hw]
   apply sumBy_le
   intro s hs
   have he := selected_degree_deleted G v s
   omega
 unfold avoidingCurvature curvature
 rw [avoiding_coefficient]
 have hi := Int.ofNat_le.mpr hd
 omega

end Erdos993.WeightedInduced


