import LinearFactorUnimodality
namespace Erdos993.LeafAttachment
open Counting MarkedInjectionAudit ParentConstruction CurvatureProof

def attachLeaf {n : Nat} (G : Graph n) (v : Fin n) : Graph (n+1) where
 adj := Fin.cases (Fin.cases false (fun u => decide (u=v)))
   (fun u => Fin.cases (decide (u=v)) (fun w => G.adj u w))
 symm := by
   intro a b
   refine Fin.cases ?_ (fun u => ?_) a
   · refine Fin.cases ?_ (fun w => ?_) b <;> rfl
   · refine Fin.cases ?_ (fun w => ?_) b
     · rfl
     · exact G.symm u w
 loopless := by
   intro a
   refine Fin.cases ?_ (fun u => ?_) a
   · rfl
   · exact G.loopless u

def attachedParent {n : Nat} {G : Graph n} (R : ParentCertificate G) (v : Fin n) :
 Fin (n+1) → Option (Fin (n+1)) :=
 Fin.cases none (fun u => if u=v then some 0 else (R.parent u).map Fin.succ)

theorem succ_ne_new {n : Nat} (u : Fin n) : u.succ≠(0:Fin (n+1)) := by
 intro h
 have hh := congrArg Fin.val h
 simp only [Fin.val_succ,Fin.val_zero] at hh
 omega

theorem new_ne_succ {n : Nat} (u : Fin n) : (0:Fin (n+1))≠u.succ := Ne.symm (succ_ne_new u)

attribute [simp] succ_ne_new new_ne_succ

theorem map_succ_not_zero {n : Nat} (p : Option (Fin n)) : p.map Fin.succ≠some 0 := by
 cases p <;> simp

theorem map_succ_eq {n : Nat} (p : Option (Fin n)) (u : Fin n) :
 p.map Fin.succ=some u.succ ↔ p=some u := by
 cases p <;> simp

def attachedCertificate {n : Nat} {G : Graph n} (R : ParentCertificate G) (v : Fin n)
 (hr : R.parent v=none) : ParentCertificate (attachLeaf G v) where
 parent := attachedParent R v
 edges := by
   intro a b
   refine Fin.cases ?_ (fun u => ?_) a
   · refine Fin.cases ?_ (fun w => ?_) b
     · simp [attachLeaf,attachedParent]
     · by_cases hw : w=v
       · simp [attachLeaf,attachedParent,hw]
       · simp [attachLeaf,attachedParent,hw]
   · refine Fin.cases ?_ (fun w => ?_) b
     · by_cases hu : u=v
       · simp [attachLeaf,attachedParent,hu]
       · simp [attachLeaf,attachedParent,hu]
     · have he := R.edges u w
       by_cases hu : u=v <;> by_cases hw : w=v
       · subst u; subst w; simp [attachLeaf,attachedParent,G.loopless]
       · subst u
         simpa [attachLeaf,attachedParent,hw,hr,map_succ_eq] using he
       · subst w
         simpa [attachLeaf,attachedParent,hu,hr,map_succ_eq] using he
       · simpa [attachLeaf,attachedParent,hu,hw,map_succ_eq] using he
 noTwoCycle := by
   intro a b
   refine Fin.cases ?_ (fun u => ?_) a
   · simp [attachedParent]
   · refine Fin.cases ?_ (fun w => ?_) b
     · simp [attachedParent]
     · by_cases hu : u=v <;> by_cases hw : w=v
       · simp [attachedParent,hu,hw]
       · simp [attachedParent,hu,hw]
       · simp [attachedParent,hu,hw]
       · simpa [attachedParent,hu,hw,map_succ_eq] using R.noTwoCycle u w

/-- We need only the constructed parent certificate to apply the checked
 injection. No unproved forest-preservation premise is hidden here. -/
theorem attached_pointed_curvature {n : Nat} (G : Graph n) (hf : IsForest G)
 (v : Fin n) (r : Nat) :
 2*(RootingBridgeAudit.inc (attachLeaf G v) 0 r:Int)≤curvature (attachLeaf G v) r := by
 obtain ⟨R,hr⟩ := forest_parent_certificate G hf v
 exact pointed_curvature (attachedCertificate R v hr) 0 rfl r

theorem degree_old {n : Nat} (G : Graph n) (v u : Fin n) :
 degree (attachLeaf G v) u.succ=degree G u+(if u=v then 1 else 0) := by
 unfold degree
 rw [←sumBy_indicator,List.finRange_succ,sumBy_cons,sumBy_map]
 change (if decide (u=v) then 1 else 0)+sumBy (List.finRange n) (fun w => if G.adj u w then 1 else 0)=_
 rw [sumBy_indicator]
 simp [Nat.add_comm]

theorem degree_new {n : Nat} (G : Graph n) (v : Fin n) :
 degree (attachLeaf G v) 0=1 := by
 unfold degree
 rw [←sumBy_indicator,List.finRange_succ,sumBy_cons,sumBy_map]
 change 0+sumBy (List.finRange n) (fun u => if decide (u=v) then 1 else 0)=1
 simp only [Nat.zero_add,decide_eq_true_eq]
 rw [sumBy_equal_indicator _ (finRange_nodup n) v]
 simp

end Erdos993.LeafAttachment
