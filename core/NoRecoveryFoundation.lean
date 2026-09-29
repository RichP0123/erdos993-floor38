import ForestStatements

namespace Erdos993.Foundation

/-- Exact no-recovery condition. Plateaus after a fall are allowed. -/
def NoRecovery (a : Nat → Nat) : Prop :=
  ∀ p q, p < q → a (p+1) < a p → a (q+1) ≤ a q

theorem least_witness (P : Nat → Prop) (hex : ∃ k, P k) :
    ∃ m, P m ∧ ∀ i, i<m → ¬P i := by
  classical
  have bounded : ∀ k, (∃ i, i≤k ∧ P i) → ∃ m, P m ∧ ∀ i, i<m → ¬P i := by
    intro k
    induction k with
    | zero =>
      rintro ⟨i, hi, hp⟩
      have he : i=0 := by omega
      subst i
      exact ⟨0,hp,by intro j hj; omega⟩
    | succ k ih =>
      intro h
      by_cases hb : ∃ i, i≤k ∧ P i
      · exact ih hb
      · obtain ⟨i, hi, hp⟩ := h
        have he : i=k+1 := by
          by_cases hik : i≤k
          · exact False.elim (hb ⟨i,hik,hp⟩)
          · omega
        subst i
        refine ⟨k+1,hp,?_⟩
        intro j hj hpj
        exact hb ⟨j,by omega,hpj⟩
  obtain ⟨k,hk⟩ := hex
  exact bounded k ⟨k,by omega,hk⟩

theorem noRecovery_of_unimodal (a : Nat → Nat) (h : Erdos993.Unimodal a) :
    NoRecovery a := by
  obtain ⟨m, up, down⟩ := h
  intro p q hpq hp
  by_cases hpm : p < m
  · have hh := up p hpm
    omega
  · exact down q (by omega)

theorem monotone_steps (a : Nat → Nat) (h : ∀ i, a i ≤ a (i+1)) :
    ∀ i d, a i ≤ a (i+d) := by
  intro i d
  induction d with
  | zero => simp
  | succ d ih =>
    have hh := h (i+d)
    have he : i+(d+1)=i+d+1 := by omega
    rw [he]
    exact Nat.le_trans ih hh

theorem unimodal_of_noRecovery (a : Nat → Nat) (N : Nat)
    (finite : ∀ i, N ≤ i → a i=0) (h : NoRecovery a) :
    Erdos993.Unimodal a := by
  classical
  by_cases hex : ∃ m, a (m+1) < a m
  · obtain ⟨m,hm,hmin⟩ := least_witness (fun i => a (i+1)<a i) hex
    refine ⟨m, ?_, ?_⟩
    · intro i hi
      have hn : ¬ a (i+1) < a i := hmin i hi
      omega
    · intro i hi
      by_cases he : i=m
      · subst i
        omega
      · exact h m i (by omega) hm
  · have up : ∀ i, a i ≤ a (i+1) := by
      intro i
      by_cases hn : a i ≤ a (i+1)
      · exact hn
      · exact False.elim (hex ⟨i, by omega⟩)
    have hz : ∀ i, a i=0 := by
      intro i
      have hh := monotone_steps a up i N
      have ht := finite (i+N) (by omega)
      omega
    exact ⟨0, by intro i hi; omega, by intro i hi; simp [hz]⟩

theorem graph_unimodal_iff_noRecovery {n : Nat} (G : Erdos993.Graph n) :
    Erdos993.Unimodal (Erdos993.coefficient G) ↔
      NoRecovery (Erdos993.coefficient G) := by
  constructor
  · exact noRecovery_of_unimodal _
  · intro h
    apply unimodal_of_noRecovery _ (n+1) ?_ h
    intro i hi
    exact Erdos993.coefficient_above_order G (by omega)

/-- This is a kernel-checked equivalence to the actual graph target, not a
theorem that forests satisfy NoRecovery. That universal sign fact remains open. -/
theorem target_iff_noRecovery : Erdos993.Target ↔
    ∀ n (G : Erdos993.Graph n), Erdos993.IsForest G →
      NoRecovery (Erdos993.coefficient G) := by
  constructor
  · intro ht n G hf
    exact (graph_unimodal_iff_noRecovery G).mp (ht n G hf)
  · intro hn n G hf
    exact (graph_unimodal_iff_noRecovery G).mpr (hn n G hf)

def NoRecoveryBefore (a : Nat → Nat) (cut : Nat) : Prop :=
  ∀ p q, p<q → q<cut → a (p+1)<a p → a (q+1)≤a q

theorem noRecovery_of_tail_and_prefix (a : Nat → Nat) (cut : Nat)
    (tail : ∀ q, cut≤q → a (q+1)≤a q)
    (hprefix : NoRecoveryBefore a cut) : NoRecovery a := by
  intro p q hpq hp
  by_cases hq : q<cut
  · exact hprefix p q hpq hq hp
  · exact tail q (by omega)

theorem graph_unimodal_of_tail_and_prefix {n : Nat} (G : Erdos993.Graph n)
    (cut : Nat)
    (tail : ∀ q, cut≤q → Erdos993.coefficient G (q+1)≤Erdos993.coefficient G q)
    (hprefix : NoRecoveryBefore (Erdos993.coefficient G) cut) :
    Erdos993.Unimodal (Erdos993.coefficient G) :=
  (graph_unimodal_iff_noRecovery G).mpr
    (noRecovery_of_tail_and_prefix _ cut tail hprefix)

#print axioms graph_unimodal_iff_noRecovery
#print axioms target_iff_noRecovery
#print axioms graph_unimodal_of_tail_and_prefix
end Erdos993.Foundation
