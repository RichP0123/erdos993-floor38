import ForestStatements

/-!
Checked conditional composition interfaces for the exact ordinary Erdos 993
target. The classification and the two exclusion propositions below remain
open mathematical children. They are definitions and explicit theorem
parameters, never axioms or silently admitted proofs.
-/

namespace Erdos993.Closure

def CounterexampleExists : Prop :=
  ∃ n : Nat, ∃ G : Graph n, IsForest G ∧ ¬ Unimodal (coefficient G)

theorem counterexample_iff_not_target : CounterexampleExists ↔ ¬ Target := by
  classical
  constructor
  · rintro ⟨n, G, hf, hb⟩ ht
    exact hb (ht n G hf)
  · intro hn
    by_cases hex : CounterexampleExists
    · exact hex
    · apply False.elim
      apply hn
      intro n G hf
      by_cases hu : Unimodal (coefficient G)
      · exact hu
      · exact False.elim (hex ⟨n, G, hf, hu⟩)

/-- An exact minimum-order bad-forest witness carrying the first strict
    departure fall and the first subsequent strict returning departure.
    No connectedness hypothesis is imposed. All smaller forests are covered,
    including disconnected forests, not merely induced subgraphs of G. -/
structure CriticalWitness where
  n : Nat
  M : Nat
  b : Nat
  graph : Graph n
  forest : IsForest graph
  positiveFallIndex : 1 ≤ M
  smallerForestUnimodal : ∀ m : Nat, m < n → ∀ H : Graph m,
    IsForest H → Unimodal (coefficient H)
  firstFall : coefficient graph (M + 1) < coefficient graph M
  noEarlierFall : ∀ i : Nat, i < M →
    coefficient graph i ≤ coefficient graph (i + 1)
  returnAfterFall : M < b
  returningRise : coefficient graph b < coefficient graph (b + 1)
  noIntermediateReturn : ∀ i : Nat, M < i → i < b →
    coefficient graph (i + 1) ≤ coefficient graph i

/-- A fall followed by a later rise contradicts ordinary weak unimodality.
    This is proved directly against the finite-graph foundation's definition. -/
theorem fall_return_not_unimodal {a : Nat → Nat} {M b : Nat}
    (hfall : a (M + 1) < a M) (hafter : M < b)
    (hrise : a b < a (b + 1)) : ¬ Unimodal a := by
  rintro ⟨mode, hp, ht⟩
  by_cases hbefore : M < mode
  · have h := hp M hbefore
    omega
  · have hm : mode ≤ b := by omega
    have h := ht b hm
    omega

theorem critical_witness_bad (w : CriticalWitness) :
    ¬ Unimodal (coefficient w.graph) :=
  fall_return_not_unimodal w.firstFall w.returnAfterFall w.returningRise

theorem critical_witness_not_target (w : CriticalWitness) : ¬ Target := by
  intro ht
  exact critical_witness_bad w (ht w.n w.graph w.forest)

/-- The critical delta=2 layer, with n=4M-2 written without Nat subtraction. -/
def Delta2CounterexampleExists : Prop :=
  ∃ w : CriticalWitness, w.n + 2 = 4 * w.M

/-- Every remaining deeper layer delta>=3, simultaneously. -/
def DeeperCounterexampleExists : Prop :=
  ∃ w : CriticalWitness, w.n + 3 ≤ 4 * w.M

/-- OPEN child: failure of ordinary 993 yields a critical witness in one
    of the two remaining layers. This includes minimum-counterexample
    extraction and the reductions excluding n>=4M-1. -/
def CriticalClassification : Prop :=
  ¬ Target → Delta2CounterexampleExists ∨ DeeperCounterexampleExists

/-- OPEN child: exclusion of the entire delta=2 layer, not just selected forks. -/
def Delta2Excluded : Prop := ¬ Delta2CounterexampleExists

/-- OPEN child: exclusion of all delta>=3 layers. -/
def DeeperExcluded : Prop := ¬ DeeperCounterexampleExists

theorem delta2_witness_not_target (h : Delta2CounterexampleExists) : ¬ Target := by
  obtain ⟨w, _⟩ := h
  exact critical_witness_not_target w

theorem deeper_witness_not_target (h : DeeperCounterexampleExists) : ¬ Target := by
  obtain ⟨w, _⟩ := h
  exact critical_witness_not_target w

/-- A genuinely kernel-checked parent implication with three explicit open
    children. It does not prove or assume an axiom asserting any child. -/
theorem target_of_critical_children
    (classification : CriticalClassification)
    (noDelta2 : Delta2Excluded)
    (noDeeper : DeeperExcluded) : Target := by
  classical
  by_cases ht : Target
  · exact ht
  · rcases classification ht with h2 | hd
    · exact False.elim (noDelta2 h2)
    · exact False.elim (noDeeper hd)

/-- The reduction classification makes the remaining two exclusions
    equivalent to the exact target; its reverse direction is also checked. -/
theorem target_iff_exclusions (classification : CriticalClassification) :
    Target ↔ Delta2Excluded ∧ DeeperExcluded := by
  constructor
  · intro ht
    exact ⟨fun h => delta2_witness_not_target h ht,
      fun h => deeper_witness_not_target h ht⟩
  · rintro ⟨h2, hd⟩
    exact target_of_critical_children classification h2 hd

#print axioms counterexample_iff_not_target
#print axioms fall_return_not_unimodal
#print axioms critical_witness_bad
#print axioms critical_witness_not_target
#print axioms delta2_witness_not_target
#print axioms deeper_witness_not_target
#print axioms target_of_critical_children
#print axioms target_iff_exclusions

end Erdos993.Closure
