import ForestReturnPhases

namespace Erdos993.LeafReturnDepth
open Counting Structure LeafBoundary LeafPhases

theorem prefix_interval (a : Nat → Nat) (ua : Unimodal a)
 (r : Nat) (rise : a r < a (r+1)) (i j : Nat)
 (hij : i ≤ j) (hjr : j ≤ r+1) : a i ≤ a j := by
 induction j with
 | zero =>
   have hi : i=0 := by omega
   subst i
   exact Nat.le_refl _
 | succ j ih =>
   by_cases hi : i=j+1
   · subst i; exact Nat.le_refl _
   · have h1 := ih (by omega) (by omega)
     have h2 := unimodal_prefix_of_rise a ua r rise j (by omega)
     omega

theorem tail_interval (a : Nat → Nat) (ua : Unimodal a)
 (r : Nat) (fall : a (r+1) < a r) (i j : Nat)
 (hri : r ≤ i) (hij : i ≤ j) : a j ≤ a i := by
 induction j with
 | zero =>
   have hi : i=0 := by omega
   subst i
   exact Nat.le_refl _
 | succ j ih =>
   by_cases hi : i=j+1
   · subst i; exact Nat.le_refl _
   · have h1 := ih (by omega)
     have h2 := unimodal_tail_of_fall a ua r fall j (by omega)
     omega

/-- Sequence lemma for the actual leaf-pair recurrences. No first-return
 assumption is needed, and no division or positive-support assumption is hidden. -/
theorem low_depth (f g h q : Nat → Nat) (M b : Nat)
 (hM : 1 ≤ M) (hb : M < b)
 (fg : ∀ r, f (r+1)=g (r+1)+h r)
 (gh : ∀ r, g (r+1)=h (r+1)+q r)
 (qh : ∀ r, q r ≤ h r) (uh : Unimodal h)
 (phase : Low g h q M b) : 2*f M < 3*f b := by
 have hm : M-1+1=M := by omega
 have hbi : b-1+1=b := by omega
 have rise : h (b-1)<h ((b-1)+1) := by rw [hbi]; exact phase.2.1
 have h1 := prefix_interval h uh (b-1) rise (M-1) M (by omega) (by omega)
 have h2 := prefix_interval h uh (b-1) rise M (b-1) (by omega) (by omega)
 have h3 := phase.2.1
 have h4 := qh (M-1)
 have fm := fg (M-1)
 have gm := gh (M-1)
 have fb := fg (b-1)
 have gb := gh (b-1)
 rw [hm] at fm gm
 rw [hbi] at fb gb
 omega

/-- The opposite leaf phase forces an even shallower drop. -/
theorem high_depth (f g h q : Nat → Nat) (M b : Nat)
 (hM : 1 ≤ M) (hb : M < b)
 (fg : ∀ r, f (r+1)=g (r+1)+h r)
 (gh : ∀ r, g (r+1)=h (r+1)+q r)
 (hg : ∀ r, h r ≤ g r) (qh : ∀ r, q r ≤ h r)
 (ug : Unimodal g) (uh : Unimodal h)
 (phase : High g h q M b) : 3*f M < 4*f b := by
 have hm : M-1+1=M := by omega
 have hbi : b-1+1=b := by omega
 have fall : h ((M-1)+1)<h (M-1) := by rw [hm]; exact phase.1
 have g1 := prefix_interval g ug b phase.2.1 M b (by omega) (by omega)
 have g2 := prefix_interval g ug b phase.2.1 (M-1) b (by omega) (by omega)
 have h1 := hg (M-1)
 have h2 := tail_interval h uh (M-1) fall (b-1) b (by omega) (by omega)
 have h3 := tail_interval h uh (M-1) fall b (b+1) (by omega) (by omega)
 have h4 := qh b
 have g3 := gh b
 have g4 := phase.2.1
 have fm := fg (M-1)
 have fb := fg (b-1)
 rw [hm] at fm
 rw [hbi] at fb
 omega

/-- Actual graph endpoint: any leaf of a minimum counterexample certifies
 that a later rising coefficient remains strictly above two-thirds of the
 coefficient at the falling departure. Spectators remain in every deletion. -/
theorem critical_leaf_depth (w : Closure.CriticalWitness) (l v : Fin w.n)
 (hlv : l ≠ v) (hl : ∀ u, w.graph.adj l u=true ↔ u=v) :
 2*coefficient w.graph w.M < 3*coefficient w.graph w.b := by
 let g := coefficient (deleteVertex w.graph l)
 let h := coefficient (inducedOn w.graph (leafPairVertices l v))
 let q := coefficient (inducedOn w.graph
   ((leafPairVertices l v).filter (fun u => !(w.graph.adj v u))))
 have recs := actual_leaf_recurrences w.graph l v hlv hl
 have ug : Unimodal g := critical_inducedOn_unimodal w (deleteVertices l)
   (deleteVertices_nodup l)
   (by have hh := deleteVertices_length l; have hi := l.isLt; omega)
 have uh : Unimodal h := critical_inducedOn_unimodal w (leafPairVertices l v)
   (leafPair_nodup l v) (by have hh := leafPair_length l v hlv; omega)
 have qh : ∀ r, q r ≤ h r := fun r => induced_filter_coefficient_le w.graph _ _ r
 have hg : ∀ r, h r ≤ g r := by
   intro r
   cases r with
   | zero => simp [g,h,Extraction.coefficient_zero]
   | succ r =>
     have hh := (recs r).2
     dsimp only [h,g]
     omega
 rcases critical_leaf_phases w l v hlv hl with hp | hp
 · exact low_depth _ g h q _ _ w.positiveFallIndex w.returnAfterFall
     (fun r => (recs r).1) (fun r => (recs r).2) qh uh hp
 · have hd := high_depth _ g h q _ _ w.positiveFallIndex w.returnAfterFall
     (fun r => (recs r).1) (fun r => (recs r).2) hg qh ug uh hp
   omega

/-- Leaf existence is discharged from the actual forest and its minimality. -/
theorem critical_has_leaf (w : Closure.CriticalWitness) :
 ∃ l v : Fin w.n, l ≠ v ∧ (∀ u, w.graph.adj l u=true ↔ u=v) := by
 have hn : 0 < w.n := by
   have hh := InteriorDegreeTwo.critical_order_above_half w
   omega
 obtain ⟨l,hl⟩ := forest_has_leaf_or_isolate w.graph w.forest hn
 have he : ∃ v, w.graph.adj l v=true := by
   apply Classical.byContradiction
   intro he
   apply LinearFactor.critical_has_no_isolate w l
   intro u
   cases hx : w.graph.adj l u with
   | false => rfl
   | true => exact False.elim (he ⟨u,hx⟩)
 obtain ⟨v,hv⟩ := he
 have hlv : l ≠ v := by
   intro h
   subst v
   rw [w.graph.loopless] at hv
   contradiction
 exact ⟨l,v,hlv,fun u => ⟨fun hu => hl u v hu hv,fun hu => hu ▸ hv⟩⟩

/-- Arbitrary-order, actual-forest depth restriction, with no supplied leaf,
 scalar compensation, census premise, or bounded-order hypothesis. -/
theorem critical_depth (w : Closure.CriticalWitness) :
 2*coefficient w.graph w.M < 3*coefficient w.graph w.b := by
 obtain ⟨l,v,hlv,hl⟩ := critical_has_leaf w
 exact critical_leaf_depth w l v hlv hl

end Erdos993.LeafReturnDepth
