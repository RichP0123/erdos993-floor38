import Floor216Acceptance

namespace Erdos993.Floor216

abbrev Rectangle (m : ℕ) := Fin m → ℕ × ℕ
def Inside {m : ℕ} (b : Rectangle m) (v : Fin m → ℕ) : Prop :=
  ∀ i, (b i).1 ≤ v i ∧ v i < (b i).2
def leftPart {m : ℕ} (b : Rectangle m) (i : Fin m) (cut : ℕ) : Rectangle m :=
  Function.update b i ((b i).1, cut)
def rightPart {m : ℕ} (b : Rectangle m) (i : Fin m) (cut : ℕ) : Rectangle m :=
  Function.update b i (cut, (b i).2)

/-- A split changes only one factor, even when two positions use the same bank. -/
theorem split_coverage {m : ℕ} (b : Rectangle m) (i : Fin m) (cut : ℕ)
    (hlo : (b i).1 ≤ cut) (hhi : cut ≤ (b i).2) (v : Fin m → ℕ) :
    Inside b v ↔ Inside (leftPart b i cut) v ∨ Inside (rightPart b i cut) v := by
  constructor
  · intro h
    by_cases hc : v i < cut
    · left
      intro j
      by_cases hj : j = i
      · subst j
        simpa [leftPart] using And.intro (h i).1 hc
      · simpa [leftPart, hj] using h j
    · right
      intro j
      by_cases hj : j = i
      · subst j
        have hm : cut ≤ v i := by omega
        simpa [rightPart] using And.intro hm (h i).2
      · simpa [rightPart, hj] using h j
  · rintro (h | h) j
    · by_cases hj : j = i
      · subst j
        have hh := h i
        simp [leftPart] at hh
        exact ⟨hh.1, by omega⟩
      · simpa [leftPart, hj] using h j
    · by_cases hj : j = i
      · subst j
        have hh := h i
        simp [rightPart] at hh
        exact ⟨by omega, hh.2⟩
      · simpa [rightPart, hj] using h j

theorem split_disjoint {m : ℕ} (b : Rectangle m) (i : Fin m) (cut : ℕ)
    (v : Fin m → ℕ) : ¬(Inside (leftPart b i cut) v ∧ Inside (rightPart b i cut) v) := by
  intro h
  have hl := h.1 i
  have hr := h.2 i
  simp [leftPart] at hl
  simp [rightPart] at hr
  omega

inductive BoxTrace (m : ℕ) where
  | accept : BoxTrace m
  | split (axis : Fin m) (cut : ℕ) (left right : BoxTrace m) : BoxTrace m

def traceCheck {m : ℕ} (accept : Rectangle m → Bool) (b : Rectangle m) : BoxTrace m → Bool
  | .accept => accept b
  | .split i cut l r =>
    decide ((b i).1 < cut ∧ cut < (b i).2) &&
      (traceCheck accept (leftPart b i cut) l && traceCheck accept (rightPart b i cut) r)

/-- Both children must pass. There is no constructor for a cap, missing branch,
unresolved leaf, or sampled terminal. -/
theorem traceCheck_sound {m : ℕ} (accept : Rectangle m → Bool)
    (property : (Fin m → ℕ) → Prop)
    (leaf_sound : ∀ b, accept b = true → ∀ v, Inside b v → property v)
    (trace : BoxTrace m) (b : Rectangle m) (passed : traceCheck accept b trace = true) :
    ∀ v, Inside b v → property v := by
  induction trace generalizing b with
  | accept => exact leaf_sound b passed
  | split i cut l r ihl ihr =>
    simp only [traceCheck, Bool.and_eq_true, decide_eq_true_eq] at passed
    intro v hv
    rcases (split_coverage b i cut (le_of_lt passed.1.1) (le_of_lt passed.1.2) v).mp hv with hl | hr
    · exact ihl (leftPart b i cut) passed.2.1 v hl
    · exact ihr (rightPart b i cut) passed.2.2 v hr

/-- Instantiation with the actual-graph safe-window theorem. Correctly supplied
enclosures for every state in a box certify every graph in the root product. -/
theorem graph_trace_sound {m n : ℕ} (graphs : (Fin m → ℕ) → Graph n)
    (scales : (Fin m → ℕ) → ℚ) (positive : ∀ v, 0 < scales v)
    (d e : Rectangle m → Bounds) (f l : Rectangle m → ℕ)
    (lengths : ∀ b, l b ≤ n)
    (first : ∀ b v, Inside b v → Encloses (d b) (difference 1 (normalizedGraph (graphs v) (scales v))))
    (second : ∀ b v, Inside b v → Encloses (e b) (difference 2 (normalizedGraph (graphs v) (scales v))))
    (trace : BoxTrace m) (b : Rectangle m)
    (passed : traceCheck (fun b => windowCheck n (f b) (l b) (d b) (e b)) b trace = true) :
    ∀ v, Inside b v → Unimodal (coefficient (graphs v)) := by
  refine traceCheck_sound _ (fun v => Unimodal (coefficient (graphs v))) ?_ trace b passed
  intro box ok v hv
  exact graph_certificate_sound (graphs v) (scales v) (positive v)
    (d box) (e box) (f box) (l box) (lengths box) (first box v hv) (second box v hv) ok

#print axioms split_coverage
#print axioms traceCheck_sound
#print axioms graph_trace_sound
end Erdos993.Floor216
