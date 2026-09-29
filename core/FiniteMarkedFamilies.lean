import ForestParentCertificate
namespace Erdos993.FiniteMarked
open Counting Structure MarkedInjectionAudit ParentConstruction
set_option maxHeartbeats 8000000

theorem canonical_sublist {α : Type} [DecidableEq α] (xs s : List α)
 (hx : xs.Nodup) (hs : s.Sublist xs) : xs.filter (fun x => decide (x∈s))=s := by
 induction xs generalizing s with
 | nil => have := List.sublist_nil.mp hs; subst s; rfl
 | cons a xs ih =>
   have hn := List.nodup_cons.mp hx
   rcases List.sublist_cons_iff.mp hs with hh | ⟨t,he,ht⟩
   · have ha : a∉s := fun h => hn.1 (hh.subset h)
     simp only [List.filter_cons,ha,decide_false,Bool.false_eq_true,if_false]
     exact ih s hn.2 hh
   · subst s
     simp only [List.filter_cons,List.mem_cons,true_or,decide_true,if_true]
     congr 1
     have he : xs.filter (fun x => decide (x∈a::t))=xs.filter (fun x => decide (x∈t)) := by
       apply List.filter_congr
       intro x hx
       have hxa : x≠a := by intro h; subst x; exact hn.1 hx
       simp [hxa]
     simp only [List.mem_cons] at he
     rw [he]
     exact ih t hn.2 ht

def mask {n : Nat} (s : List (Fin n)) : Fin n → Bool := fun v => decide (v∈s)
def canon {n : Nat} (S : Fin n → Bool) : List (Fin n) := (List.finRange n).filter S

theorem canon_mask {n : Nat} (s : List (Fin n)) (hs : s∈subsets (List.finRange n)) :
 canon (mask s)=s := canonical_sublist _ s (finRange_nodup n) ((mem_subsets _ _).mp hs)

theorem mask_canon {n : Nat} (S : Fin n → Bool) : mask (canon S)=S := by
 funext v
 simp [mask,canon]

theorem mask_independent_iff {n : Nat} (G : Graph n) (s : List (Fin n)) :
 MaskIndependent G (mask s) ↔ independent G s=true := by
 simp only [MaskIndependent,mask,decide_eq_true_eq,independent_iff]
 constructor
 · intro h u hu v hv; exact h u v hu hv
 · intro h u v hu hv; exact h u hu v hv

theorem canonical_independent_member {n : Nat} (G : Graph n) (r : Nat)
 (S : Fin n → Bool) (hs : MaskIndependent G S) (hr : (canon S).length=r) :
 canon S∈independentSets G r := by
 apply (mem_independentSets G r (canon S)).mpr
 refine ⟨(mem_subsets _ _).mpr List.filter_sublist,hr,?_⟩
 apply (mask_independent_iff G (canon S)).mp
 rw [mask_canon]
 exact hs

theorem injection_length_le {α β : Type} [DecidableEq β]
 (xs : List α) (ys : List β) (f : α → β) (hx : xs.Nodup)
 (hf : ∀ x∈xs, f x∈ys)
 (hi : ∀ x∈xs, ∀ y∈xs, f x=f y → x=y) : xs.length≤ys.length := by
 induction xs generalizing ys with
 | nil => simp
 | cons x xs ih =>
   have hn := List.nodup_cons.mp hx
   have hfx := hf x (by simp)
   have hh : xs.length≤(ys.erase (f x)).length := by
     apply ih (ys.erase (f x)) hn.2
     · intro y hy
       apply (List.mem_erase_of_ne ?_).mpr (hf y (by simp [hy]))
       intro he
       have hxy := hi y (by simp [hy]) x (by simp) he
       exact hn.1 (hxy ▸ hy)
     · intro y hy z hz he
       exact hi y (by simp [hy]) z (by simp [hz]) he
   rw [List.length_erase_of_mem hfx] at hh
   have hpos := List.length_pos_of_mem hfx
   simp only [List.length_cons]
   omega

def pairs {α β : Type} (xs : List α) (f : α → List β) : List (α × β) :=
 xs.flatMap (fun x => (f x).map (fun y => (x,y)))

theorem mem_pairs {α β : Type} (xs : List α) (f : α → List β) (x : α) (y : β) :
 (x,y)∈pairs xs f ↔ x∈xs ∧ y∈f x := by simp [pairs]

theorem pairs_length {α β : Type} (xs : List α) (f : α → List β) :
 (pairs xs f).length=sumBy xs (fun x => (f x).length) := by
 simp [pairs,List.length_flatMap,sumBy]

theorem pairs_nodup {α β : Type} (xs : List α) (f : α → List β)
 (hx : xs.Nodup) (hf : ∀ x∈xs, (f x).Nodup) : (pairs xs f).Nodup := by
 apply List.pairwise_flatMap.mpr
 constructor
 · intro x hxm
   exact nodup_map_injective (fun y => (x,y)) _ (by intros; simp_all) (hf x hxm)
 · apply hx.imp
   intro a b hab x hx y hy he
   obtain ⟨u,hu,hux⟩ := List.mem_map.mp hx
   obtain ⟨v,hv,hvy⟩ := List.mem_map.mp hy
   have hh := congrArg Prod.fst (hux.trans (he.trans hvy.symm))
   exact hab hh

def children {n : Nat} {G : Graph n} (R : ParentCertificate G) (a : Fin n) : List (Fin n) :=
 (List.finRange n).filter (fun b => decide (R.parent b=some a))

def sources {n : Nat} {G : Graph n} (R : ParentCertificate G) (r : Nat) :
 List (List (Fin n) × Fin n × Fin n) :=
 pairs (independentSets G r) (fun s => pairs s (children R))

def targets {n : Nat} {G : Graph n} (R : ParentCertificate G) (r : Nat) :
 List (List (Fin n) × Fin n) :=
 pairs (independentSets G r) (fun s => s.filter (fun v => decide (R.parent v≠none)))

theorem mem_sources {n : Nat} {G : Graph n} (R : ParentCertificate G) (r : Nat)
 (s : List (Fin n)) (a b : Fin n) :
 (s,a,b)∈sources R r ↔ s∈independentSets G r ∧ a∈s ∧ R.parent b=some a := by
 simp [sources,mem_pairs,children]

theorem mem_targets {n : Nat} {G : Graph n} (R : ParentCertificate G) (r : Nat)
 (s : List (Fin n)) (a : Fin n) :
 (s,a)∈targets R r ↔ s∈independentSets G r ∧ a∈s ∧ R.parent a≠none := by
 simp [targets,mem_pairs]

theorem independentSets_nodup {n : Nat} (G : Graph n) (r : Nat) :
 (independentSets G r).Nodup :=
 List.Sublist.nodup List.filter_sublist (vertex_subsets_nodup n)

theorem sources_nodup {n : Nat} {G : Graph n} (R : ParentCertificate G) (r : Nat) :
 (sources R r).Nodup := by
 apply pairs_nodup _ _ (independentSets_nodup G r)
 intro s hs
 have hm := (mem_independentSets G r s).mp hs
 apply pairs_nodup _ _ (List.Sublist.nodup ((mem_subsets _ _).mp hm.1) (finRange_nodup n))
 intro a ha
 exact List.Sublist.nodup List.filter_sublist (finRange_nodup n)

noncomputable def encode {n : Nat} {G : Graph n} (R : ParentCertificate G)
 (x : List (Fin n) × Fin n × Fin n) : List (Fin n) × Fin n :=
 if hc : ∃ t, t∈x.1 ∧ R.parent t=some x.2.2 then
   (x.1,Classical.choose hc)
 else (canon (swapMask (mask x.1) x.2.1 x.2.2),x.2.2)

theorem encode_in_targets {n : Nat} {G : Graph n} (R : ParentCertificate G) (r : Nat)
 (s : List (Fin n)) (a b : Fin n) (hx : (s,a,b)∈sources R r) :
 encode R (s,a,b)∈targets R r := by
 classical
 have hm := (mem_sources R r s a b).mp hx
 have hset := (mem_independentSets G r s).mp hm.1
 have hs := (mask_independent_iff G s).mpr hset.2.2
 have ha : mask s a=true := by simpa [mask] using hm.2.1
 unfold encode
 dsimp
 split
 · rename_i hc
   have ht := Classical.choose_spec hc
   apply (mem_targets R r s (Classical.choose hc)).mpr
   exact ⟨hm.1,ht.1,by rw [ht.2]; simp⟩
 · rename_i hc
   apply (mem_targets R r _ b).mpr
   have hnone : ¬∃ t, mask s t=true ∧ R.parent t=some b := by simpa [mask] using hc
   have hsep := source_separation R (mask s) hs a b ha hm.2.2
   have hlen := swap_rank (mask s) a b ha hsep.1 hsep.2
   change (canon (swapMask (mask s) a b)).length=(canon (mask s)).length at hlen
   rw [canon_mask s hset.1,hset.2.1] at hlen
   refine ⟨canonical_independent_member G r _ (swap_independent R _ hs a b hm.2.2 hnone) hlen,?_,?_⟩
   · simp [canon,swapMask]
   · rw [hm.2.2]; simp

theorem encode_decodes {n : Nat} {G : Graph n} (R : ParentCertificate G) (r : Nat)
 (s : List (Fin n)) (a b : Fin n) (hx : (s,a,b)∈sources R r) :
 decode R (mask (encode R (s,a,b)).1) (encode R (s,a,b)).2=(mask s,a,b) := by
 classical
 have hm := (mem_sources R r s a b).mp hx
 have hset := (mem_independentSets G r s).mp hm.1
 have hs := (mask_independent_iff G s).mpr hset.2.2
 have ha : mask s a=true := by simpa [mask] using hm.2.1
 unfold encode
 dsimp
 split
 · rename_i hc
   have ht := Classical.choose_spec hc
   exact decode_selected_child R (mask s) a b (Classical.choose hc) ha hm.2.2 ht.2
 · simp only [mask_canon]
   exact decode_swapped R (mask s) hs a b ha hm.2.2

theorem encode_injective_on_sources {n : Nat} {G : Graph n} (R : ParentCertificate G) (r : Nat) :
 ∀ x∈sources R r, ∀ y∈sources R r, encode R x=encode R y → x=y := by
 rintro ⟨s,a,b⟩ hx ⟨t,c,d⟩ hy he
 have hd1 := encode_decodes R r s a b hx
 have hd2 := encode_decodes R r t c d hy
 rw [he] at hd1
 have hp : (mask s,a,b)=(mask t,c,d) := hd1.symm.trans hd2
 have hm := congrArg Prod.fst hp
 have hs := (mem_independentSets G r s).mp ((mem_sources R r s a b).mp hx).1
 have ht := (mem_independentSets G r t).mp ((mem_sources R r t c d).mp hy).1
 have hst : s=t := (canon_mask s hs.1).symm.trans ((congrArg canon hm).trans (canon_mask t ht.1))
 have hab : (a,b)=(c,d) := congrArg (fun z : (Fin n → Bool) × Fin n × Fin n => z.2) hp
 exact Prod.ext hst hab

/-- Cardinality inequality for the actual canonical-list marked families. -/
theorem sources_le_targets {n : Nat} {G : Graph n} (R : ParentCertificate G) (r : Nat) :
 (sources R r).length≤(targets R r).length := by
 classical
 apply injection_length_le _ _ (encode R) (sources_nodup R r)
 · rintro ⟨s,a,b⟩ hx; exact encode_in_targets R r s a b hx
 · exact encode_injective_on_sources R r

end Erdos993.FiniteMarked
