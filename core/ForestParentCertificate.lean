import MarkedInjectionAudit

/-! Construct the injection's parent certificate on actual forests, preserving
an arbitrary designated root. No rooted grammar or height invariant is needed. -/
namespace Erdos993.ParentConstruction
open Counting Structure MarkedInjectionAudit
set_option maxHeartbeats 4000000

def embed {n : Nat} (v : Fin n) (i : Fin (deleteVertices v).length) : Fin n :=
 (deleteVertices v)[i.val]

theorem embed_injective {n : Nat} (v : Fin n) (i j : Fin (deleteVertices v).length)
 (h : embed v i=embed v j) : i=j :=
 list_vertex_injective _ (deleteVertices_nodup v) i j h

theorem embed_ne_deleted {n : Nat} (v : Fin n) (i : Fin (deleteVertices v).length) :
 embed v i≠v := by
 intro h
 have hm : v∈deleteVertices v := List.mem_of_getElem h
 exact (List.Nodup.not_mem_erase (finRange_nodup n)) hm

noncomputable def oldIndex {n : Nat} (v x : Fin n) (hx : x≠v) :
 Fin (deleteVertices v).length :=
 Classical.choose (root_survives_deletion v x (Ne.symm hx))

theorem embed_oldIndex {n : Nat} (v x : Fin n) (hx : x≠v) :
 embed v (oldIndex v x hx)=x :=
 Classical.choose_spec (root_survives_deletion v x (Ne.symm hx))

theorem oldIndex_embed {n : Nat} (v : Fin n) (i : Fin (deleteVertices v).length)
 (hx : embed v i≠v) : oldIndex v (embed v i) hx=i := by
 apply embed_injective v
 exact embed_oldIndex v (embed v i) hx

noncomputable def liftParent {n : Nat} {G : Graph n} (v : Fin n)
 (R : ParentCertificate (deleteVertex G v)) (newParent : Option (Fin n)) :
 Fin n → Option (Fin n) := fun x =>
 if hx : x=v then newParent else
   (R.parent (oldIndex v x hx)).map (embed v)

theorem liftParent_deleted {n : Nat} {G : Graph n} (v : Fin n)
 (R : ParentCertificate (deleteVertex G v)) (np : Option (Fin n)) :
 liftParent v R np v=np := by simp [liftParent]

theorem liftParent_embed {n : Nat} {G : Graph n} (v : Fin n)
 (R : ParentCertificate (deleteVertex G v)) (np : Option (Fin n))
 (i : Fin (deleteVertices v).length) :
 liftParent v R np (embed v i)=(R.parent i).map (embed v) := by
 simp [liftParent,embed_ne_deleted,oldIndex_embed]

theorem mapped_parent_ne_deleted {n : Nat} (v : Fin n)
 (p : Option (Fin (deleteVertices v).length)) : p.map (embed v)≠some v := by
 cases p with
 | none => simp
 | some i => simpa using embed_ne_deleted v i

theorem map_parent_eq {n : Nat} (v : Fin n)
 (p : Option (Fin (deleteVertices v).length)) (i : Fin (deleteVertices v).length) :
 p.map (embed v)=some (embed v i) ↔ p=some i := by
 cases p with
 | none => simp
 | some j =>
   simp only [Option.map_some,Option.some.injEq]
   constructor
   · exact embed_injective v j i
   · intro h; rw [h]

theorem lifted_edges {n : Nat} {G : Graph n} (v : Fin n)
 (R : ParentCertificate (deleteVertex G v)) (np : Option (Fin n))
 (hnp : ∀ u, np=some u ↔ G.adj v u=true) :
 ∀ u w, G.adj u w=true ↔
   liftParent v R np u=some w ∨ liftParent v R np w=some u := by
 intro u w
 by_cases hu : u=v
 · subst u
   rw [liftParent_deleted]
   by_cases hw : w=v
   · subst w
     rw [liftParent_deleted]
     simp only [or_self]
     exact (hnp v).symm
   · let i := oldIndex v w hw
     have hi : embed v i=w := embed_oldIndex v w hw
     rw [←hi,liftParent_embed]
     simp only [mapped_parent_ne_deleted,or_false]
     exact (hnp (embed v i)).symm
 · by_cases hw : w=v
   · subst w
     let i := oldIndex v u hu
     have hi : embed v i=u := embed_oldIndex v u hu
     rw [←hi,liftParent_embed,liftParent_deleted]
     simp only [mapped_parent_ne_deleted,false_or]
     rw [G.symm]
     exact (hnp (embed v i)).symm
   · let i := oldIndex v u hu
     let j := oldIndex v w hw
     have hi : embed v i=u := embed_oldIndex v u hu
     have hj : embed v j=w := embed_oldIndex v w hw
     rw [←hi,←hj,liftParent_embed,liftParent_embed,map_parent_eq,map_parent_eq]
     exact R.edges i j

theorem lifted_no_two_cycle {n : Nat} {G : Graph n} (v : Fin n)
 (R : ParentCertificate (deleteVertex G v)) (np : Option (Fin n))
 (hnp : ∀ u, np=some u ↔ G.adj v u=true) :
 ∀ u w, ¬(liftParent v R np u=some w ∧ liftParent v R np w=some u) := by
 intro u w ⟨huw,hwu⟩
 have hnv : np≠some v := by
   intro hh
   have he := (hnp v).mp hh
   rw [G.loopless] at he
   contradiction
 by_cases hu : u=v
 · subst u
   by_cases hw : w=v
   · subst w; exact hnv (by simpa [liftParent_deleted] using huw)
   · let i := oldIndex v w hw
     have hi : embed v i=w := embed_oldIndex v w hw
     rw [←hi,liftParent_embed] at hwu
     exact mapped_parent_ne_deleted v _ hwu
 · by_cases hw : w=v
   · subst w
     let i := oldIndex v u hu
     have hi : embed v i=u := embed_oldIndex v u hu
     rw [←hi,liftParent_embed] at huw
     exact mapped_parent_ne_deleted v _ huw
   · let i := oldIndex v u hu
     let j := oldIndex v w hw
     have hi : embed v i=u := embed_oldIndex v u hu
     have hj : embed v j=w := embed_oldIndex v w hw
     rw [←hi,←hj,liftParent_embed,map_parent_eq] at huw
     rw [←hi,←hj,liftParent_embed,map_parent_eq] at hwu
     exact R.noTwoCycle i j ⟨huw,hwu⟩

noncomputable def restoreCertificate {n : Nat} {G : Graph n} (v : Fin n)
 (R : ParentCertificate (deleteVertex G v)) (np : Option (Fin n))
 (hnp : ∀ u, np=some u ↔ G.adj v u=true) : ParentCertificate G where
 parent := liftParent v R np
 edges := lifted_edges v R np hnp
 noTwoCycle := lifted_no_two_cycle v R np hnp

theorem leaf_parent_option {n : Nat} (G : Graph n) (v : Fin n)
 (hv : ∀ u w, G.adj v u=true → G.adj v w=true → u=w) :
 ∃ np : Option (Fin n), ∀ u, np=some u ↔ G.adj v u=true := by
 classical
 by_cases he : ∃ t, G.adj v t=true
 · obtain ⟨t,ht⟩ := he
   refine ⟨some t,?_⟩
   intro u
   simp only [Option.some.injEq]
   constructor
   · intro h; subst u; exact ht
   · intro hu; exact hv t u ht hu
 · refine ⟨none,?_⟩
   intro u
   constructor
   · intro h; contradiction
   · intro hu; exact False.elim (he ⟨u,hu⟩)

def singletonCertificate (G : Graph 1) : ParentCertificate G where
 parent := fun _ => none
 edges := by
   intro u v
   have he : u=v := by apply Fin.ext; omega
   subst v
   simp [G.loopless]
 noTwoCycle := by intros; simp

/-- Actual graph theorem: a forest admits the injection's parent certificate,
with any designated vertex parentless and all spectator components retained. -/
theorem forest_parent_certificate {n : Nat} (G : Graph n) (hf : IsForest G) (root : Fin n) :
 ∃ R : ParentCertificate G, R.parent root=none := by
 refine forest_rooted_leaf_induction
   (fun {m} (H : Graph m) v => ∃ R : ParentCertificate H, R.parent v=none) ?_ ?_ G hf root
 · intro H v
   exact ⟨singletonCertificate H,rfl⟩
 · intro m H hH root v hv hleaf i hi hR
   obtain ⟨R,hr⟩ := hR
   obtain ⟨np,hnp⟩ := leaf_parent_option H v hleaf
   refine ⟨restoreCertificate v R np hnp,?_⟩
   change liftParent v R np root=none
   change embed v i=root at hi
   rw [←hi,liftParent_embed,hr]
   rfl

end Erdos993.ParentConstruction
