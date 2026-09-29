import ForestCore.CountingBridge

/-!
These local semantic equivalences connect the project's adjacent-difference
unimodality and Mathlib's independent-set count to the peak-monotonicity and
filtered-powerset interfaces used in:
https://github.com/junwei-lu/Erdos_993_Tree_Independent_Set_Unimodality/blob/main/ErdosProblem993/Basic.lean

The equivalences are proved here with Lean 4.30. No theorem or compiled object
from that external Lean 4.29 project is imported or certified by this module.
No finite catalogue or certificate data is imported.
-/

namespace Erdos993.ForestCore

/-- Adjacent weak unimodality is equivalent to monotonicity on either side of
a peak, including plateaus and all natural-number indices. -/
theorem unimodal_iff_monotone_sides (a : Nat → Nat) :
    Erdos993.Unimodal a ↔
      ∃ m : Nat,
        (∀ ⦃j k : Nat⦄, j ≤ k → k ≤ m → a j ≤ a k) ∧
        (∀ ⦃j k : Nat⦄, m ≤ j → j ≤ k → a k ≤ a j) := by
  constructor
  · rintro ⟨m, hup, hdown⟩
    refine ⟨m, ?_, ?_⟩
    · intro j k hjk
      induction hjk with
      | refl => intro _; exact le_rfl
      | @step k hjk ih =>
        intro hkm
        exact (ih (by omega)).trans (hup k (by omega))
    · intro j k hmj hjk
      induction hjk with
      | refl => exact le_rfl
      | @step k hjk ih =>
        exact (hdown k (hmj.trans hjk)).trans ih
  · rintro ⟨m, hup, hdown⟩
    refine ⟨m, ?_, ?_⟩
    · intro i hi
      exact hup (Nat.le_succ i) (Nat.succ_le_of_lt hi)
    · intro i hi
      exact hdown hi (Nat.le_succ i)

/-- Mathlib's independent-set count equals the two-filter powerset formula
on every finite vertex type, for every graph and every cardinality. -/
theorem card_indepSetFinset_eq_filtered_powerset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : Nat) :
    (G.indepSetFinset k).card =
      (((Finset.univ.powerset.filter fun J : Finset V =>
          G.IsIndepSet (J : Set V)).filter fun J => J.card = k).card) := by
  congr 1
  ext J
  simp [SimpleGraph.mem_indepSetFinset_iff, SimpleGraph.isNIndepSet_iff]

#print axioms unimodal_iff_monotone_sides
#print axioms card_indepSetFinset_eq_filtered_powerset

end Erdos993.ForestCore
