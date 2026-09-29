import PrefixCenterPairs
namespace Erdos993.PrefixDegreeSums
open Counting Structure PrefixRootBudget PrefixForkPacking ParentConstruction
set_option maxHeartbeats 8000000

def degreeIn {n : Nat} (G : Graph n) (p : Fin n → Bool) (v : Fin n) : Nat :=
 sumBy (List.finRange n) (fun u => if G.adj v u && p u then 1 else 0)

def mass {n : Nat} (p : Fin n → Bool) (f : Fin n → Nat) : Nat :=
 sumBy (List.finRange n) (fun v => if p v then f v else 0)

def count {n : Nat} (p : Fin n → Bool) : Nat := mass p (fun _ => 1)

theorem mass_add {n : Nat} (p : Fin n → Bool) (f g : Fin n → Nat) :
 mass p (fun v => f v+g v)=mass p f+mass p g := by
 unfold mass
 rw [←sumBy_add]
 apply sumBy_congr
 intro v hv
 cases p v <;> simp

theorem mass_mul {n : Nat} (p : Fin n → Bool) (f : Fin n → Nat) (c : Nat) :
 mass p (fun v => c*f v)=c*mass p f := by
 unfold mass
 rw [←sumBy_mul_left]
 apply sumBy_congr
 intro v hv
 cases p v <;> simp

theorem mass_le {n : Nat} (p : Fin n → Bool) (f g : Fin n → Nat)
 (h : ∀v,p v=true → f v≤g v) : mass p f≤mass p g := by
 apply sumBy_le
 intro v hv
 dsimp only
 cases hp : p v
 · simp
 · simp only [if_true]
   exact h v hp

theorem mass_complement {n : Nat} (p : Fin n → Bool) (f : Fin n → Nat) :
 mass p f+mass (fun v => !(p v)) f=sumBy (List.finRange n) f := by
 unfold mass
 rw [←sumBy_add]
 apply sumBy_congr
 intro v hv
 dsimp only
 by_cases hp : p v=true <;> simp [hp]

theorem count_complement {n : Nat} (p : Fin n → Bool) :
 count p+count (fun v => !(p v))=n := by
 simpa [count,sumBy_const] using mass_complement p (fun _ => 1)

theorem count_length {n : Nat} (p : Fin n → Bool) :
 count p=((List.finRange n).filter p).length := sumBy_indicator _ _

theorem degreeIn_length {n : Nat} (G : Graph n) (p : Fin n → Bool) (v : Fin n) :
 degreeIn G p v=(((List.finRange n).filter p).filter (G.adj v)).length := by
 rw [List.filter_filter]
 exact sumBy_indicator _ _

theorem degree_split {n : Nat} (G : Graph n) (p : Fin n → Bool) (v : Fin n) :
 degreeIn G p v+degreeIn G (fun u => !(p u)) v=degree G v := by
 unfold degreeIn degree
 rw [←sumBy_add,←sumBy_indicator]
 apply sumBy_congr
 intro u hu
 dsimp only
 by_cases ha : G.adj v u=true <;> by_cases hp : p u=true <;> simp [ha,hp]

theorem degreeIn_le {n : Nat} (G : Graph n) (p : Fin n → Bool) (v : Fin n) :
 degreeIn G p v≤degree G v := by have h := degree_split G p v; omega

theorem degreeIn_adj_positive {n : Nat} (G : Graph n) (p : Fin n → Bool)
 (v u : Fin n) (ha : G.adj v u=true) (hp : p u=true) : 1≤degreeIn G p v := by
 rw [degreeIn_length]
 have hm : u∈((List.finRange n).filter p).filter (G.adj v) := by simp [ha,hp]
 exact List.length_pos_of_mem hm

theorem mass_degree_swap {n : Nat} (G : Graph n) (p q : Fin n → Bool) :
 mass p (degreeIn G q)=mass q (degreeIn G p) := by
 have he (p q : Fin n → Bool) : mass p (degreeIn G q)=
   sumBy (List.finRange n) (fun v => sumBy (List.finRange n)
     (fun u => if p v && G.adj v u && q u then 1 else 0)) := by
   apply sumBy_congr
   intro v hv
   cases p v
   · simp
   · simp [degreeIn]
 rw [he,he,sumBy_swap]
 apply sumBy_congr
 intro u hu
 apply sumBy_congr
 intro v hv
 rw [G.symm v u]
 cases p v <;> cases q u <;> cases G.adj u v <;> rfl

theorem forest_degree_total_le {n : Nat} (G : Graph n) (hf : IsForest G) :
 sumBy (List.finRange n) (degree G)≤2*n := by
 cases n with
 | zero => simp
 | succ m =>
   obtain ⟨R,_⟩ := forest_parent_certificate G hf ⟨0,by omega⟩
   have h := degree_total_with_roots R
   omega

theorem forest_internal_degree {n : Nat} (G : Graph n) (hf : IsForest G)
 (p : Fin n → Bool) : mass p (degreeIn G p)≤2*count p := by
 let xs := (List.finRange n).filter p
 have hf' := inducedOn_isForest G hf xs ((finRange_nodup n).filter p)
 have h := forest_degree_total_le (inducedOn G xs) hf'
 have he : sumBy (List.finRange xs.length) (degree (inducedOn G xs))=
   sumBy xs (degreeIn G p) := by
   conv => rhs; rw [←finRange_map_get xs,sumBy_map]
   apply sumBy_congr
   intro v hv
   rw [WeightedInduced.degree_inducedOn,degreeIn_length]
 have hm : sumBy xs (degreeIn G p)=mass p (degreeIn G p) := sumBy_filter _ _ _
 rw [he,hm] at h
 simpa [xs,count_length] using h

def neighborWeight {n : Nat} (G : Graph n) (p : Fin n → Bool)
 (f : Fin n → Nat) (v : Fin n) : Nat :=
 sumBy (List.finRange n) (fun u => if G.adj v u && p u then f u else 0)

theorem neighborWeight_member_le {n : Nat} (G : Graph n) (p : Fin n → Bool)
 (f : Fin n → Nat) (v u : Fin n) (ha : G.adj v u=true) (hp : p u=true) :
 f u≤neighborWeight G p f v := by
 have he := sumBy_weighted_indicator (List.finRange n) (finRange_nodup n) u f
 have hh := sumBy_le (List.finRange n) (fun z => if z=u then f z else 0)
   (fun z => if G.adj v z && p z then f z else 0) ?_
 · simpa [neighborWeight,he] using hh
 · intro z hz
   dsimp only
   by_cases he : z=u
   · subst z; simp [ha,hp]
   · simp [he]

theorem weighted_degree_swap {n : Nat} (G : Graph n) (p q : Fin n → Bool)
 (f : Fin n → Nat) :
 mass p (neighborWeight G q f)=mass q (fun u => degreeIn G p u*f u) := by
 have he : mass p (neighborWeight G q f)=
   sumBy (List.finRange n) (fun v => sumBy (List.finRange n)
     (fun u => if p v && G.adj v u && q u then f u else 0)) := by
   apply sumBy_congr
   intro v hv
   by_cases hp : p v=true <;> simp [neighborWeight,hp]
 rw [he,sumBy_swap]
 apply sumBy_congr
 intro u hu
 dsimp only
 by_cases hq : q u=true
 · simp only [hq,Bool.and_true,if_true]
   unfold degreeIn
   rw [Nat.mul_comm,←sumBy_mul_left]
   apply sumBy_congr
   intro v hv
   rw [G.symm v u]
   by_cases hp : p v=true <;> by_cases ha : G.adj u v=true <;> simp [hp,ha]
 · simp [hq]

end Erdos993.PrefixDegreeSums
