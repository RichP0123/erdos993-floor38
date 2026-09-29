import LeafBoundaryTransfer
namespace Erdos993.PaddingCounts
open Counting Structure LeafBoundary

def pad : Nat → (Nat → Nat) → Nat → Nat
 | 0,a,r => a r
 | s+1,a,0 => pad s a 0
 | s+1,a,r+1 => pad s a (r+1)+pad s a r

theorem pad_zero_rank (s : Nat) (a : Nat → Nat) : pad s a 0=a 0 := by
 induction s <;> simp_all [pad]

theorem pad_ge (s : Nat) (a : Nat → Nat) (r : Nat) : a r≤pad s a r := by
 induction s generalizing r with
 | zero => simp [pad]
 | succ s ih =>
   cases r with
   | zero => exact ih 0
   | succ r =>
     have h := ih (r+1)
     change _≤pad s a (r+1)+pad s a r
     omega

theorem pad_first_order (s : Nat) (a : Nat → Nat) (r : Nat) :
 a (r+1)+s*a r≤pad s a (r+1) := by
 induction s with
 | zero => simp [pad]
 | succ s ih =>
   have h := pad_ge s a r
   simp only [pad]
   grind

/-- Integer-free truncated binomial expansion, including zero coefficients. -/
theorem pad_second_order (s : Nat) (a : Nat → Nat) (r : Nat) :
 2*a (r+2)+2*s*a (r+1)+s*(s-1)*a r≤2*pad s a (r+2) := by
 induction s with
 | zero => simp [pad]
 | succ s ih =>
   have h := pad_first_order s a r
   change _≤2*(pad s a (r+2)+pad s a (r+1))
   have hs : s*(s-1)+2*s=(s+1)*s := by
     cases s <;> simp <;> grind
   have hm := Nat.mul_le_mul_left 2 h
   have he : 2*a (r+2)+2*(s+1)*a (r+1)+(s+1)*((s+1)-1)*a r=
       (2*a (r+2)+2*s*a (r+1)+s*(s-1)*a r)+2*(a (r+1)+s*a r) := by
     simp only [Nat.add_sub_cancel]
     rw [←hs]
     simp only [Nat.add_mul,Nat.mul_add,Nat.mul_one,Nat.mul_assoc]
     omega
   rw [he]
   simpa only [Nat.mul_add] using Nat.add_le_add ih hm

/-- Actual independent-set counts after adjoining a list of vertices with
 no neighbours in the induced vertex set. No polynomial model is assumed. -/
theorem rankCount_isolated_prefix {n : Nat} (G : Graph n)
 (ls us : List (Fin n))
 (hi : ∀ v∈ls, ∀ u∈ls++us, G.adj v u=false) (r : Nat) :
 rankCount (independent G) (ls++us) r=pad ls.length (rankCount (independent G) us) r := by
 induction ls generalizing r with
 | nil => simp [pad]
 | cons v ls ih =>
   have ht : ∀ v∈ls, ∀ u∈ls++us, G.adj v u=false := by
     intro v hv u hu
     exact hi v (by simp [hv]) u (by simp only [List.cons_append,List.mem_cons]; exact Or.inr hu)
   cases r with
   | zero => simp [rankCount_zero,pad_zero_rank,independent]
   | succ r =>
     change rankCount (independent G) (v::(ls++us)) (r+1)=_
     rw [graph_root_recurrence]
     have he : (ls++us).filter (fun u => !(G.adj v u))=ls++us := by
       apply List.filter_eq_self.mpr
       intro u hu
       have ha := hi v (by simp) u (by simp only [List.cons_append,List.mem_cons]; exact Or.inr hu)
       simp [ha]
     rw [he,ih ht (r+1),ih ht r]
     rfl

theorem pad_mono (s : Nat) (a b : Nat → Nat) (hab : ∀ r,a r≤b r) (r : Nat) :
 pad s a r≤pad s b r := by
 induction s generalizing r with
 | zero => exact hab r
 | succ s ih =>
   cases r with
   | zero => exact ih 0
   | succ r => exact Nat.add_le_add (ih (r+1)) (ih r)

/-- A partition into actual isolated vertices and spectators gives lower
 bounds against any induced subforest of the spectators. -/
theorem isolated_partition_lower {n : Nat} (G : Graph n) (xs : List (Fin n))
 (p t : Fin n → Bool)
 (hi : ∀ v∈xs.filter p, ∀ u∈xs, G.adj v u=false) (r : Nat) :
 pad (xs.filter p).length
   (coefficient (inducedOn G ((xs.filter (fun u => !(p u))).filter t))) r≤
 coefficient (inducedOn G xs) r := by
 have hc : ∀ r, coefficient (inducedOn G ((xs.filter (fun u => !(p u))).filter t)) r≤
     rankCount (independent G) (xs.filter (fun u => !(p u))) r := by
   intro r
   rw [coefficient_inducedOn]
   exact rankCount_filter_le _ _ _ _
 have hpad := pad_mono (xs.filter p).length _ _ hc r
 have he := rankCount_isolated_prefix G (xs.filter p) (xs.filter (fun u => !(p u))) ?_ r
 · have hp := rankCount_perm (List.filter_append_perm p xs) (independent G)
     (independent_permInvariant G) r
   rw [←he,hp] at hpad
   rw [coefficient_inducedOn]
   exact hpad
 · intro v hv u hu
   apply hi v hv u
   rcases List.mem_append.mp hu with hu | hu
   · exact (List.mem_filter.mp hu).1
   · exact (List.mem_filter.mp hu).1

end Erdos993.PaddingCounts
