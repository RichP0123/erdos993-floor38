import Std

/-! Self-contained finite graph semantics for ordinary Erdos 993.
Lean 4.30.0; only the bundled Std library is imported.
No theorem asserting Erdos993 is introduced. -/
namespace Erdos993

/-- A labelled finite simple undirected graph. No connectedness is required. -/
structure Graph (n : Nat) where
  adj : Fin n → Fin n → Bool
  symm : ∀ u v, adj u v = adj v u
  loopless : ∀ u, adj u u = false

/-- All subsets, represented in the inherited order of the input list. -/
def subsets {α : Type} : List α → List (List α)
  | [] => [[]]
  | a :: xs => subsets xs ++ (subsets xs).map (a :: ·)

theorem mem_subsets {α : Type} (s xs : List α) :
    s ∈ subsets xs ↔ List.Sublist s xs := by
  induction xs generalizing s with
  | nil => simp [subsets]
  | cons a xs ih =>
    simp only [subsets, List.mem_append, List.mem_map, List.sublist_cons_iff]
    simp only [ih]
    constructor
    · rintro (h | ⟨r, hr, he⟩)
      · exact Or.inl h
      · exact Or.inr ⟨r, he.symm, hr⟩
    · rintro (h | ⟨r, he, hr⟩)
      · exact Or.inl h
      · exact Or.inr ⟨r, hr, he.symm⟩

theorem nodup_map_injective {α β : Type} (f : α → β) (xs : List α)
    (hf : ∀ a b, f a = f b → a = b) (hx : xs.Nodup) :
    (xs.map f).Nodup := by
  apply List.pairwise_map.mpr
  exact hx.imp (fun {a b} hab he => hab (hf a b he))

theorem subsets_nodup {α : Type} (xs : List α) (hx : xs.Nodup) :
    (subsets xs).Nodup := by
  induction xs with
  | nil => simp [subsets]
  | cons a xs ih =>
    obtain ⟨ha, hx⟩ := List.nodup_cons.mp hx
    rw [subsets, List.nodup_append]
    refine ⟨ih hx, nodup_map_injective (a :: ·) _ (by intros; simp_all) (ih hx), ?_⟩
    intro s hs t ht he
    obtain ⟨r, _, hr⟩ := List.mem_map.mp ht
    have has : a ∈ s := by rw [he, ← hr]; simp
    exact ha (((mem_subsets s xs).mp hs).subset has)

theorem finRange_nodup (n : Nat) : (List.finRange n).Nodup := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.finRange_succ, List.nodup_cons]
    constructor
    · intro h
      obtain ⟨x, _, he⟩ := List.mem_map.mp h
      have hv := congrArg Fin.val he
      simp at hv
    · exact nodup_map_injective Fin.succ _ (by intros; simp_all) ih

theorem vertex_subsets_nodup (n : Nat) :
    (subsets (List.finRange n)).Nodup := subsets_nodup _ (finRange_nodup n)

/-- True precisely when every pair of listed vertices is nonadjacent. -/
def independent {n : Nat} (G : Graph n) (s : List (Fin n)) : Bool :=
  s.all fun u => s.all fun v => !(G.adj u v)

theorem independent_iff {n : Nat} (G : Graph n) (s : List (Fin n)) :
    independent G s = true ↔ ∀ u ∈ s, ∀ v ∈ s, G.adj u v = false := by
  simp [independent]

theorem independent_empty {n : Nat} (G : Graph n) :
    independent G [] = true := by simp [independent]

theorem independent_singleton {n : Nat} (G : Graph n) (v : Fin n) :
    independent G [v] = true := by simp [independent, G.loopless]

/-- Number of independent vertex subsets of cardinality r. -/
def coefficient {n : Nat} (G : Graph n) (r : Nat) : Nat :=
  ((subsets (List.finRange n)).filter
    (fun s => decide (s.length = r) && independent G s)).length

theorem coefficient_above_order {n r : Nat} (G : Graph n) (hr : n < r) :
    coefficient G r = 0 := by
  unfold coefficient
  rw [List.filter_eq_nil_iff.mpr]
  · rfl
  · intro s hs
    have hlen := (mem_subsets s (List.finRange n)).mp hs |>.length_le
    have hn : s.length ≤ n := by simpa using hlen
    have hne : s.length ≠ r := by omega
    simp [hne]

/-- Successor around a cycle with at least three vertices. -/
def cycleNext {k : Nat} (i : Fin (k + 3)) : Fin (k + 3) :=
  ⟨(i.val + 1) % (k + 3), Nat.mod_lt _ (by omega)⟩

/-- No injectively embedded simple cycle of any length at least three.
This permits arbitrary disconnected components, isolated vertices, and n=0. -/
def IsForest {n : Nat} (G : Graph n) : Prop :=
  ∀ k : Nat, ∀ v : Fin (k + 3) → Fin n,
    (∀ i j, v i = v j → i = j) →
    ¬ (∀ i, G.adj (v i) (v (cycleNext i)) = true)

/-- Ordinary weak unimodality, including plateaus and trailing zero coefficients. -/
def Unimodal (a : Nat → Nat) : Prop :=
  ∃ m : Nat, (∀ i, i < m → a i ≤ a (i + 1)) ∧
    (∀ i, m ≤ i → a (i + 1) ≤ a i)

/-- The exact open target, for ALL finite forests; this is a Prop, not an axiom. -/
def Target : Prop := ∀ n : Nat, ∀ G : Graph n,
  IsForest G → Unimodal (coefficient G)

theorem isForest_of_atMostOneNeighbor {n : Nat} (G : Graph n)
    (hdeg : ∀ u v w, G.adj u v = true → G.adj u w = true → v = w) :
    IsForest G := by
  intro k v hinj hcycle
  let i0 : Fin (k + 3) := ⟨0, by omega⟩
  let i1 : Fin (k + 3) := ⟨1, by omega⟩
  let i2 : Fin (k + 3) := ⟨2, by omega⟩
  have hn0 : cycleNext i0 = i1 := by
    apply Fin.ext
    simp [cycleNext, i0, i1, Nat.mod_eq_of_lt (show 1 < k + 3 by omega)]
  have hn1 : cycleNext i1 = i2 := by
    apply Fin.ext
    simp [cycleNext, i1, i2, Nat.mod_eq_of_lt (show 2 < k + 3 by omega)]
  have e01 := hcycle i0
  have e12 := hcycle i1
  rw [hn0, G.symm] at e01
  rw [hn1] at e12
  have he := hinj i0 i2 (hdeg (v i1) (v i0) (v i2) e01 e12)
  have := congrArg Fin.val he
  simp [i0, i2] at this

/-- An edgeless graph, allowing the empty graph. -/
def emptyGraph (n : Nat) : Graph n where
  adj := fun _ _ => false
  symm := by intros; rfl
  loopless := by intros; rfl

theorem emptyGraph_isForest (n : Nat) : IsForest (emptyGraph n) := by
  intro k v _ h
  have h0 := h ⟨0, by omega⟩
  simp [emptyGraph] at h0

theorem emptyGraph_coefficient (r : Nat) :
    coefficient (emptyGraph 0) r = if r = 0 then 1 else 0 := by
  by_cases hr : r = 0
  · subst r; rfl
  · simp [coefficient, subsets, independent, List.filter, hr, Ne.symm hr]

theorem emptyGraph_zero_unimodal : Unimodal (coefficient (emptyGraph 0)) := by
  refine ⟨0, ?_, ?_⟩
  · intro i hi; omega
  · intro i _
    simp [emptyGraph_coefficient]

/-- Small semantic checks compute through the kernel, with no native_decide. -/
example : (List.range 4).map (coefficient (emptyGraph 3)) = [1, 3, 3, 1] := by
  decide

/-- Two disjoint edges, a disconnected forest with polynomial 1+4x+4x^2. -/
def twoEdges : Graph 4 where
  adj := fun u v => decide (u.val / 2 = v.val / 2 ∧ u ≠ v)
  symm := by intro u v; simp [eq_comm]
  loopless := by intro u; simp

theorem twoEdges_isForest : IsForest twoEdges := by
  apply isForest_of_atMostOneNeighbor
  decide

example : (List.range 5).map (coefficient twoEdges) = [1, 4, 4, 0, 0] := by
  decide

#print axioms mem_subsets
#print axioms subsets_nodup
#print axioms vertex_subsets_nodup
#print axioms independent_iff
#print axioms coefficient_above_order
#print axioms emptyGraph_zero_unimodal
#print axioms twoEdges_isForest

end Erdos993
