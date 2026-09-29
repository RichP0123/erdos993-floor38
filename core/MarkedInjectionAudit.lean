import ForestLeafStructure

/-! Auditor verification of the new injection's swap/decoder mechanism.
Parent certificate existence, finite-family cardinalities and their connection
to graph coefficient lists remain separate obligations. -/
namespace Erdos993.MarkedInjectionAudit

structure ParentCertificate {n : Nat} (G : Graph n) where
 parent : Fin n → Option (Fin n)
 edges : ∀ u v, G.adj u v=true ↔
   parent u=some v ∨ parent v=some u
 noTwoCycle : ∀ u v, ¬(parent u=some v ∧ parent v=some u)

def MaskIndependent {n : Nat} (G : Graph n) (S : Fin n → Bool) : Prop :=
 ∀ u v, S u=true → S v=true → G.adj u v=false

def swapMask {n : Nat} (S : Fin n → Bool) (a b : Fin n) : Fin n → Bool :=
 fun x => if x=b then true else if x=a then false else S x

theorem swap_reverse {n : Nat} (S : Fin n → Bool) (a b : Fin n)
 (ha : S a=true) (hb : S b=false) (hab : a≠b) :
 swapMask (swapMask S a b) b a=S := by
 funext x
 by_cases hxa : x=a
 · subst x; simp [swapMask,ha]
 · by_cases hxb : x=b
   · subst x; simp [swapMask,hb,Ne.symm hab]
   · simp [swapMask,hxa,hxb]

theorem source_separation {n : Nat} {G : Graph n} (R : ParentCertificate G)
 (S : Fin n → Bool) (hs : MaskIndependent G S) (a b : Fin n)
 (ha : S a=true) (hp : R.parent b=some a) : S b=false ∧ a≠b := by
 have he := (R.edges b a).mpr (Or.inl hp)
 have hb : S b=false := by
   cases hh : S b with
   | false => rfl
   | true => exact he.symm.trans (hs b a hh ha)
 refine ⟨hb,?_⟩
 intro hh; subst a; rw [ha] at hb; contradiction

/-- A swap-case output cannot have a selected grandparent. -/
theorem swapped_grandparent_absent {n : Nat} {G : Graph n} (R : ParentCertificate G)
 (S : Fin n → Bool) (hs : MaskIndependent G S) (a b h : Fin n)
 (ha : S a=true) (hp : R.parent b=some a) (hg : R.parent a=some h) :
 swapMask S a b h=false := by
 have hh : S h=false := by
   have he := (R.edges a h).mpr (Or.inl hg)
   cases ht : S h with
   | false => rfl
   | true => exact he.symm.trans (hs a h ha ht)
 have hhb : h≠b := by
   intro he; subst h
   exact R.noTwoCycle a b ⟨hg,hp⟩
 simp [swapMask,hhb,hh]

def decode {n : Nat} {G : Graph n} (R : ParentCertificate G)
 (T : Fin n → Bool) (t : Fin n) : (Fin n → Bool) × Fin n × Fin n :=
 match R.parent t with
 | none => (T,t,t)
 | some a => match R.parent a with
   | none => (swapMask T t a,a,t)
   | some h => if T h then (T,h,a) else (swapMask T t a,a,t)

theorem decode_selected_child {n : Nat} {G : Graph n} (R : ParentCertificate G)
 (S : Fin n → Bool) (a b t : Fin n)
 (ha : S a=true) (hp : R.parent b=some a) (ht : R.parent t=some b) :
 decode R S t=(S,a,b) := by simp [decode,ht,hp,ha]

theorem decode_swapped {n : Nat} {G : Graph n} (R : ParentCertificate G)
 (S : Fin n → Bool) (hs : MaskIndependent G S) (a b : Fin n)
 (ha : S a=true) (hp : R.parent b=some a) :
 decode R (swapMask S a b) b=(S,a,b) := by
 have hh := source_separation R S hs a b ha hp
 have hi := swap_reverse S a b ha hh.1 hh.2
 cases hg : R.parent a with
 | none => simp [decode,hp,hg,hi]
 | some h =>
   have hz := swapped_grandparent_absent R S hs a b h ha hp hg
   simp [decode,hp,hg,hz,hi]

/-- Images from either branch have a left inverse; no counting assumption. -/
theorem images_have_unique_source {n : Nat} {G : Graph n} (R : ParentCertificate G)
 (S U T : Fin n → Bool) (a b c d t : Fin n)
 (hs : decode R T t=(S,a,b)) (hu : decode R T t=(U,c,d)) :
 (S,a,b)=(U,c,d) := hs.symm.trans hu

theorem selected_after_swap {n : Nat} (S : Fin n → Bool) (a b x : Fin n)
 (hxb : x≠b) (hx : swapMask S a b x=true) : S x=true ∧ x≠a := by
 by_cases hxa : x=a
 · subst x; simp [swapMask,hxb] at hx
 · exact ⟨by simpa [swapMask,hxb,hxa] using hx,hxa⟩

theorem free_to_swap {n : Nat} {G : Graph n} (R : ParentCertificate G)
 (S : Fin n → Bool) (a b : Fin n) (hp : R.parent b=some a)
 (hc : ¬∃ t, S t=true ∧ R.parent t=some b) :
 ∀ u, S u=true → u≠a → G.adj b u=false := by
 intro u hu hne
 cases he : G.adj b u with
 | false => rfl
 | true =>
   have hh := (R.edges b u).mp he
   rcases hh with hh | hh
   · have hau : a=u := Option.some.inj (hp.symm.trans hh)
     exact False.elim (hne hau.symm)
   · exact False.elim (hc ⟨u,hu,hh⟩)

theorem swap_independent {n : Nat} {G : Graph n} (R : ParentCertificate G)
 (S : Fin n → Bool) (hs : MaskIndependent G S) (a b : Fin n)
 (hp : R.parent b=some a) (hc : ¬∃ t, S t=true ∧ R.parent t=some b) :
 MaskIndependent G (swapMask S a b) := by
 intro x y hx hy
 by_cases hxb : x=b
 · subst x
   by_cases hyb : y=b
   · subst y; exact G.loopless b
   · have hh := selected_after_swap S a b y hyb hy
     exact free_to_swap R S a b hp hc y hh.1 hh.2
 · have hxo := selected_after_swap S a b x hxb hx
   by_cases hyb : y=b
   · subst y; rw [G.symm]
     exact free_to_swap R S a b hp hc x hxo.1 hxo.2
   · have hyo := selected_after_swap S a b y hyb hy
     exact hs x y hxo.1 hyo.1

theorem swap_rank {n : Nat} (S : Fin n → Bool) (a b : Fin n)
 (ha : S a=true) (hb : S b=false) (hab : a≠b) :
 ((List.finRange n).filter (swapMask S a b)).length=
 ((List.finRange n).filter S).length := by
 open Counting in
 have he : sumBy (List.finRange n) (fun x =>
     (if S x then 1 else 0)+(if x=b then 1 else 0))=
   sumBy (List.finRange n) (fun x =>
     (if swapMask S a b x then 1 else 0)+(if x=a then 1 else 0)) := by
   apply sumBy_congr
   intro x hx
   by_cases hxa : x=a
   · subst x; simp [swapMask,ha,hab]
   · by_cases hxb : x=b
     · subst x; simp [swapMask,hb,Ne.symm hab]
     · simp [swapMask,hxa,hxb]
 open Counting in
 rw [sumBy_add,sumBy_add,sumBy_indicator,sumBy_indicator,
   sumBy_equal_indicator (List.finRange n) (finRange_nodup n) b,
   sumBy_equal_indicator (List.finRange n) (finRange_nodup n) a] at he
 simp at he
 omega

/-- Natural-number accounting after the finite injection has supplied its
image-complement partition. These three counting premises remain explicit. -/
theorem unmatched_count_balance (degreeTotal selectedSlots markedEdges markedNonroots
 markedRoots unmatched : Nat)
 (hd : degreeTotal=markedEdges+markedNonroots)
 (hs : selectedSlots=markedNonroots+markedRoots)
 (hi : markedNonroots=markedEdges+unmatched) :
 degreeTotal+2*markedRoots+unmatched=2*selectedSlots := by omega

theorem curvature_from_count_balance (degreeTotal selectedSlots markedRoots unmatched : Nat)
 (h : degreeTotal+2*markedRoots+unmatched=2*selectedSlots) :
 2*(selectedSlots:Int)-(degreeTotal:Int)=2*(markedRoots:Int)+(unmatched:Int) := by
 have hh := congrArg (fun k : Nat => (k:Int)) h
 simp only [Int.natCast_add,Int.natCast_mul] at hh
 omega

#print axioms swap_reverse
#print axioms source_separation
#print axioms swapped_grandparent_absent
#print axioms decode_selected_child
#print axioms decode_swapped
#print axioms images_have_unique_source
#print axioms selected_after_swap
#print axioms free_to_swap
#print axioms swap_independent
#print axioms swap_rank
#print axioms unmatched_count_balance
#print axioms curvature_from_count_balance
end Erdos993.MarkedInjectionAudit
