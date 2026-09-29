import CriticalExtraction
set_option maxHeartbeats 4000000
namespace Erdos993.Counting

def sumBy {α : Type} (xs : List α) (f : α → Nat) : Nat := (xs.map f).sum
@[simp] theorem sumBy_nil {α : Type} (f : α → Nat) : sumBy [] f=0 := rfl
@[simp] theorem sumBy_cons {α : Type} (a : α) (xs : List α) (f : α → Nat) :
 sumBy (a::xs) f=f a+sumBy xs f := rfl
theorem sumBy_append {α : Type} (xs ys : List α) (f : α → Nat) :
 sumBy (xs++ys) f=sumBy xs f+sumBy ys f := by simp [sumBy,List.sum_append]
theorem sumBy_map {α β : Type} (xs : List α) (g : α → β) (f : β → Nat) :
 sumBy (xs.map g) f=sumBy xs (fun x => f (g x)) := by simp [sumBy,List.map_map,Function.comp_def]
theorem sumBy_congr {α : Type} (xs : List α) (f g : α → Nat)
 (h : ∀ x ∈ xs, f x=g x) : sumBy xs f=sumBy xs g := by
 induction xs with
 | nil => rfl
 | cons x xs ih =>
   rw [sumBy_cons,sumBy_cons,h x (by simp),ih (by intro y hy; exact h y (by simp [hy]))]
theorem sumBy_add {α : Type} (xs : List α) (f g : α → Nat) :
 sumBy xs (fun x => f x+g x)=sumBy xs f+sumBy xs g := by
 induction xs with
 | nil => rfl
 | cons x xs ih => simp only [sumBy_cons,ih]; omega
@[simp] theorem sumBy_zero {α : Type} (xs : List α) : sumBy xs (fun _ => 0)=0 := by
 induction xs <;> simp_all
theorem sumBy_indicator {α : Type} (xs : List α) (p : α → Bool) :
 sumBy xs (fun x => if p x then 1 else 0)=(xs.filter p).length := by
 induction xs with
 | nil => rfl
 | cons x xs ih => cases hp : p x <;> simp [hp,ih,Nat.add_comm]

def rankCount {α : Type} (P : List α → Bool) (xs : List α) (r : Nat) : Nat :=
 sumBy (subsets xs) (fun s => if s.length=r then (if P s then 1 else 0) else 0)

def extensions {α : Type} [DecidableEq α] (P : List α → Bool) (xs : List α) (r : Nat) : Nat :=
 sumBy (subsets xs) (fun s => if s.length=r then
   sumBy xs (fun v => if v∈s then 0 else if P (v::s) then 1 else 0) else 0)

def PermInvariant {α : Type} (P : List α → Bool) : Prop :=
 ∀ s t, List.Perm s t → P s=P t

theorem permInvariant_cons {α : Type} (P : List α → Bool) (hp : PermInvariant P) (a : α) :
 PermInvariant (fun s => P (a::s)) := by
 intro s t h; exact hp _ _ (List.Perm.cons a h)

theorem rankCount_cons_zero {α : Type} (P : List α → Bool) (a : α) (xs : List α) :
 rankCount P (a::xs) 0=rankCount P xs 0 := by
 unfold rankCount
 rw [subsets,sumBy_append,sumBy_map]
 simp

theorem rankCount_cons_succ {α : Type} (P : List α → Bool) (a : α) (xs : List α) (r : Nat) :
 rankCount P (a::xs) (r+1)=rankCount P xs (r+1)+rankCount (fun s => P (a::s)) xs r := by
 unfold rankCount
 rw [subsets,sumBy_append,sumBy_map]
 simp

theorem extension_without_head {α : Type} [DecidableEq α]
 (P : List α → Bool) (a : α) (xs : List α) (ha : a∉xs) (r : Nat) :
 sumBy (subsets xs) (fun s => if s.length=r then
   sumBy (a::xs) (fun v => if v∈s then 0 else if P (v::s) then 1 else 0) else 0)
 =rankCount (fun s => P (a::s)) xs r+extensions P xs r := by
 unfold rankCount extensions
 rw [←sumBy_add]
 apply sumBy_congr
 intro s hs
 have hn : a∉s := fun hm => ha (((mem_subsets _ _).mp hs).subset hm)
 by_cases hr : s.length=r <;> simp [hr,hn]

theorem extension_with_head {α : Type} [DecidableEq α]
 (P : List α → Bool) (hp : PermInvariant P) (a : α) (xs : List α) (ha : a∉xs)
 (s : List α) :
 sumBy (a::xs) (fun v => if v∈a::s then 0 else if P (v::a::s) then 1 else 0)
 =sumBy xs (fun v => if v∈s then 0 else if P (a::v::s) then 1 else 0) := by
 simp only [sumBy_cons,List.mem_cons,true_or,if_true,Nat.zero_add]
 apply sumBy_congr
 intro v hv
 have hn : v≠a := by intro he; subst v; exact ha hv
 have hh := hp (v::a::s) (a::v::s) (List.Perm.swap a v s)
 simp [hn,hh]

theorem extensions_cons_zero {α : Type} [DecidableEq α]
 (P : List α → Bool) (a : α) (xs : List α) (ha : a∉xs) :
 extensions P (a::xs) 0=rankCount (fun s => P (a::s)) xs 0+extensions P xs 0 := by
 unfold extensions
 rw [subsets,sumBy_append,sumBy_map]
 have h := extension_without_head P a xs ha 0
 simpa [extensions] using h

theorem extensions_cons_succ {α : Type} [DecidableEq α]
 (P : List α → Bool) (hp : PermInvariant P) (a : α) (xs : List α) (ha : a∉xs) (r : Nat) :
 extensions P (a::xs) (r+1)=rankCount (fun s => P (a::s)) xs (r+1)+
 extensions P xs (r+1)+extensions (fun s => P (a::s)) xs r := by
 unfold extensions
 rw [subsets,sumBy_append,sumBy_map]
 rw [extension_without_head P a xs ha (r+1)]
 congr 1
 apply sumBy_congr
 intro s hs
 simp only [List.length_cons,Nat.add_right_cancel_iff]
 by_cases hh : s.length=r
 · simp only [hh,if_true]
   exact extension_with_head P hp a xs ha s
 · simp [hh]

/-- Counts the same marked subset by its deleted marked vertex or by its size. -/
theorem extensions_eq_rankCount {α : Type} [DecidableEq α]
 (xs : List α) (hx : xs.Nodup) (P : List α → Bool) (hp : PermInvariant P) (r : Nat) :
 extensions P xs r=(r+1)*rankCount P xs (r+1) := by
 induction xs generalizing P r with
 | nil => simp [extensions,rankCount,subsets]
 | cons a xs ih =>
   obtain ⟨ha,hxs⟩ := List.nodup_cons.mp hx
   cases r with
   | zero =>
     rw [extensions_cons_zero P a xs ha,rankCount_cons_succ]
     rw [ih hxs P hp 0]
     simp [Nat.add_comm]
   | succ r =>
     rw [extensions_cons_succ P hp a xs ha r,rankCount_cons_succ]
     rw [ih hxs P hp (r+1),ih hxs (fun s => P (a::s)) (permInvariant_cons P hp a) r]
     grind

theorem sumBy_filter {α : Type} (xs : List α) (p : α → Bool) (f : α → Nat) :
 sumBy (xs.filter p) f=sumBy xs (fun x => if p x then f x else 0) := by
 induction xs with
 | nil => rfl
 | cons x xs ih => cases hp : p x <;> simp [hp,ih]

theorem independent_permInvariant {n : Nat} (G : Graph n) : PermInvariant (independent G) := by
 intro s t hp
 apply Bool.eq_iff_iff.mpr
 rw [independent_iff,independent_iff]
 constructor
 · intro h u hu v hv
   exact h u (hp.mem_iff.mpr hu) v (hp.mem_iff.mpr hv)
 · intro h u hu v hv
   exact h u (hp.mem_iff.mp hu) v (hp.mem_iff.mp hv)

theorem independent_cons_iff {n : Nat} (G : Graph n) (v : Fin n) (s : List (Fin n)) :
 independent G (v::s)=true ↔ independent G s=true ∧ ∀ u∈s, G.adj v u=false := by
 rw [independent_iff,independent_iff]
 constructor
 · intro h
   exact ⟨fun u hu w hw => h u (by simp [hu]) w (by simp [hw]),
     fun u hu => h v (by simp) u (by simp [hu])⟩
 · rintro ⟨h,hv⟩ u hu w hw
   rcases List.mem_cons.mp hu with he | hu
   · subst u
     rcases List.mem_cons.mp hw with he | hw
     · subst w; exact G.loopless v
     · exact hv w hw
   · rcases List.mem_cons.mp hw with he | hw
     · subst w; rw [G.symm]; exact hv u hu
     · exact h u hu w hw

theorem independent_cons_bool {n : Nat} (G : Graph n) (v : Fin n) (s : List (Fin n)) :
 independent G (v::s)=(independent G s && s.all (fun u => !(G.adj v u))) := by
 apply Bool.eq_iff_iff.mpr
 simp [independent_cons_iff]

def independentSets {n : Nat} (G : Graph n) (r : Nat) : List (List (Fin n)) :=
 (subsets (List.finRange n)).filter (fun s => decide (s.length=r) && independent G s)

/-- Actual vertices outside the closed neighbourhood of s. -/
def freeVertices {n : Nat} (G : Graph n) (s : List (Fin n)) : List (Fin n) :=
 (List.finRange n).filter (fun v => decide (v∉s) && s.all (fun u => !(G.adj v u)))

theorem mem_freeVertices {n : Nat} (G : Graph n) (s : List (Fin n)) (v : Fin n) :
 v∈freeVertices G s ↔ v∉s ∧ ∀u∈s,G.adj v u=false := by
 simp [freeVertices,List.mem_finRange]

theorem rankCount_graph {n : Nat} (G : Graph n) (r : Nat) :
 rankCount (independent G) (List.finRange n) r=coefficient G r := by
 unfold rankCount coefficient
 rw [←sumBy_indicator]
 apply sumBy_congr
 intro s hs
 by_cases hh : s.length=r <;> simp [hh]

theorem extensions_graph {n : Nat} (G : Graph n) (r : Nat) :
 extensions (independent G) (List.finRange n) r =
 sumBy (independentSets G r) (fun s => (freeVertices G s).length) := by
 unfold extensions independentSets
 rw [sumBy_filter]
 apply sumBy_congr
 intro s hs
 by_cases hlen : s.length=r
 · simp only [hlen,if_true,decide_true,Bool.true_and]
   by_cases hind : independent G s=true
   · simp only [hind,if_true]
     unfold freeVertices
     rw [←sumBy_indicator]
     apply sumBy_congr
     intro v hv
     rw [independent_cons_bool]
     by_cases hm : v∈s <;> simp [hm,hind]
   · have hfalse : independent G s=false := Bool.eq_false_iff.mpr hind
     simp [independent_cons_bool,hfalse]
 · simp [hlen]

/-- Exact graph extension counting, all ranks, empty and disconnected graphs.
 The left side is a sum of actual free-vertex cardinalities over independent r-sets. -/
theorem graph_extension_counting {n : Nat} (G : Graph n) (r : Nat) :
 sumBy (independentSets G r) (fun s => (freeVertices G s).length) =
 (r+1)*coefficient G (r+1) := by
 rw [←extensions_graph,extensions_eq_rankCount (List.finRange n) (finRange_nodup n)
   (independent G) (independent_permInvariant G),rankCount_graph]

theorem sumBy_le {α : Type} (xs : List α) (f g : α → Nat)
 (h : ∀x∈xs, f x≤g x) : sumBy xs f≤sumBy xs g := by
 induction xs with
 | nil => exact Nat.le_refl 0
 | cons x xs ih =>
   exact Nat.add_le_add (h x (by simp)) (ih (by intro y hy; exact h y (by simp [hy])))

theorem sumBy_member_le {α : Type} (xs : List α) (f : α → Nat) (x : α) (hx : x∈xs) :
 f x≤sumBy xs f := by
 induction xs with
 | nil => simp at hx
 | cons y ys ih =>
   rcases List.mem_cons.mp hx with he | hm
   · subst x; simp
   · have hh := ih hm; simp only [sumBy_cons]; omega

theorem sumBy_const {α : Type} (xs : List α) (c : Nat) : sumBy xs (fun _ => c)=xs.length*c := by
 induction xs with
 | nil => simp
 | cons x xs ih => simp [ih,Nat.add_mul,Nat.add_comm]

theorem sumBy_swap {α β : Type} (xs : List α) (ys : List β) (f : α → β → Nat) :
 sumBy xs (fun x => sumBy ys (f x))=sumBy ys (fun y => sumBy xs (fun x => f x y)) := by
 induction xs with
 | nil => simp
 | cons x xs ih => simp only [sumBy_cons]; rw [sumBy_add,ih]

theorem sumBy_equal_indicator {α : Type} [DecidableEq α] (xs : List α) (hx : xs.Nodup) (v : α) :
 sumBy xs (fun u => if u=v then 1 else 0)=if v∈xs then 1 else 0 := by
 induction xs with
 | nil => simp
 | cons a xs ih =>
   obtain ⟨ha,hxs⟩ := List.nodup_cons.mp hx
   rw [sumBy_cons,ih hxs]
   by_cases he : a=v
   · subst v; simp [ha]
   · by_cases hm : v∈xs <;> simp [he,Ne.symm he,hm]

def degree {n : Nat} (G : Graph n) (v : Fin n) : Nat :=
 ((List.finRange n).filter (fun u => G.adj v u)).length

def selectedDegree {n : Nat} (G : Graph n) (s : List (Fin n)) : Nat := sumBy s (degree G)

theorem incidence_sum {n : Nat} (G : Graph n) (s : List (Fin n)) :
 sumBy (List.finRange n) (fun v => sumBy s (fun u => if G.adj v u then 1 else 0))=
 selectedDegree G s := by
 rw [sumBy_swap]
 unfold selectedDegree degree
 apply sumBy_congr
 intro u hu
 rw [←sumBy_indicator]
 apply sumBy_congr
 intro v hv
 rw [G.symm]

theorem selected_membership_sum {n : Nat} (s : List (Fin n)) (hs : s.Nodup) :
 sumBy (List.finRange n) (fun v => if v∈s then 1 else 0)=s.length := by
 have he : sumBy (List.finRange n) (fun v => if v∈s then 1 else 0)=
   sumBy (List.finRange n) (fun v => sumBy s (fun u => if u=v then 1 else 0)) := by
   apply sumBy_congr
   intro v hv
   exact (sumBy_equal_indicator s hs v).symm
 rw [he,sumBy_swap]
 have hh : sumBy s (fun u => sumBy (List.finRange n) (fun v => if u=v then 1 else 0))=
   sumBy s (fun _ => 1) := by
   apply sumBy_congr
   intro u hu
   have hi := sumBy_equal_indicator (List.finRange n) (finRange_nodup n) u
   simpa [eq_comm,List.mem_finRange] using hi
 rw [hh,sumBy_const]
 simp

theorem vertex_cover_charge {n : Nat} (G : Graph n) (s : List (Fin n)) (v : Fin n) :
 1 ≤ (if decide (v∉s) && s.all (fun u => !(G.adj v u)) then 1 else 0)
   +(if v∈s then 1 else 0)+sumBy s (fun u => if G.adj v u then 1 else 0) := by
 classical
 by_cases hm : v∈s
 · simp [hm]
 · by_cases he : ∃u∈s,G.adj v u=true
   · obtain ⟨u,hu,ha⟩ := he
     have hh := sumBy_member_le s (fun u => if G.adj v u then 1 else 0) u hu
     simp only [ha,if_true] at hh
     omega
   · have hall : s.all (fun u => !(G.adj v u))=true := by
       apply List.all_eq_true.mpr
       intro u hu
       have hh : G.adj v u=false := by
         apply Bool.eq_false_iff.mpr
         intro ha; exact he ⟨u,hu,ha⟩
       simp [hh]
     simp [hm,hall]

/-- A pointwise union bound on the actual closed neighbourhood. -/
theorem free_volume_degree_bound {n : Nat} (G : Graph n) (s : List (Fin n)) (hs : s.Nodup) :
 n ≤ (freeVertices G s).length+s.length+selectedDegree G s := by
 have h := sumBy_le (List.finRange n) (fun _ => 1)
   (fun v => (if decide (v∉s) && s.all (fun u => !(G.adj v u)) then 1 else 0)
     +(if v∈s then 1 else 0)+sumBy s (fun u => if G.adj v u then 1 else 0))
   (by intro v hv; exact vertex_cover_charge G s v)
 rw [sumBy_add,sumBy_add,sumBy_indicator,selected_membership_sum s hs,incidence_sum,sumBy_const] at h
 simpa [freeVertices] using h

theorem independentSets_length {n : Nat} (G : Graph n) (r : Nat) :
 (independentSets G r).length=coefficient G r := rfl

theorem mem_independentSets {n : Nat} (G : Graph n) (r : Nat) (s : List (Fin n)) :
 s∈independentSets G r ↔ s∈subsets (List.finRange n) ∧ s.length=r ∧ independent G s=true := by
 simp [independentSets]

/-- Degree-sum version of graph growth, before any forest curvature input. -/
theorem graph_degree_growth {n : Nat} (G : Graph n) (r : Nat) :
 n*coefficient G r ≤ (r+1)*coefficient G (r+1)+r*coefficient G r+
   sumBy (independentSets G r) (selectedDegree G) := by
 have h := sumBy_le (independentSets G r) (fun _ => n)
   (fun s => (freeVertices G s).length+s.length+selectedDegree G s) ?_
 · rw [sumBy_const,sumBy_add,sumBy_add,graph_extension_counting] at h
   have hh : sumBy (independentSets G r) List.length = r*coefficient G r := by
     have he : sumBy (independentSets G r) List.length=sumBy (independentSets G r) (fun _ => r) := by
       apply sumBy_congr
       intro s hs
       exact ((mem_independentSets G r s).mp hs).2.1
     rw [he,sumBy_const,independentSets_length,Nat.mul_comm]
   rw [hh,independentSets_length,Nat.mul_comm (coefficient G r) n] at h
   exact h
 · intro s hs
   have hsub := (mem_subsets _ _).mp (((mem_independentSets G r s).mp hs).1)
   exact free_volume_degree_bound G s (List.Sublist.nodup hsub (finRange_nodup n))

/-- Signed total curvature, expressed without truncated natural subtraction. -/
def curvature {n : Nat} (G : Graph n) (r : Nat) : Int :=
 2*(r:Int)*(coefficient G r:Int)-(sumBy (independentSets G r) (selectedDegree G):Int)

theorem graph_curvature_growth {n : Nat} (G : Graph n) (r : Nat) :
 ((n:Int)-3*(r:Int))*(coefficient G r:Int)+curvature G r ≤
 ((r:Int)+1)*(coefficient G (r+1):Int) := by
 have hn := graph_degree_growth G r
 have hi := Int.ofNat_le.mpr hn
 simp only [Int.natCast_add,Int.natCast_mul,Int.natCast_one] at hi
 unfold curvature
 grind

/-- The forest-specific curvature bound is an explicit input here. -/
theorem growth_of_component_curvature {n : Nat} (G : Graph n) (r : Nat) (L : Int)
 (hL : 0≤L) (hc : 2*(r:Int)*(coefficient G r:Int)≤L*curvature G r) :
 (L*((n:Int)-3*(r:Int))+2*(r:Int))*(coefficient G r:Int) ≤
 L*((r:Int)+1)*(coefficient G (r+1):Int) := by
 have hg := Int.mul_le_mul_of_nonneg_left (graph_curvature_growth G r) hL
 grind

theorem first_fall_quarter_bound {n : Nat} (G : Graph n) (r : Nat)
 (hfall : coefficient G (r+1)<coefficient G r) (hc : 0≤curvature G r) : n≤4*r := by
 have hg := graph_curvature_growth G r
 have hpn : 0<coefficient G r := by omega
 have hp : 0<(coefficient G r:Int) := by exact Int.ofNat_lt.mpr hpn
 have hf := Int.ofNat_lt.mpr hfall
 have hs := Int.mul_lt_mul_of_pos_left hf (show 0<(r:Int)+1 by omega)
 by_cases hb : n≤4*r
 · exact hb
 · have hn : (r:Int)+1≤(n:Int)-3*(r:Int) := by omega
   have hm := Int.mul_le_mul_of_nonneg_right hn (show 0≤(coefficient G r:Int) by omega)
   omega

theorem subsets_map {α β : Type} (f : α → β) (xs : List α) :
 subsets (xs.map f)=(subsets xs).map (List.map f) := by
 induction xs with
 | nil => rfl
 | cons a xs ih =>
   simp [subsets,ih,List.map_map,Function.comp_def]

theorem rankCount_map {α β : Type} (P : List β → Bool) (f : α → β) (xs : List α) (r : Nat) :
 rankCount P (xs.map f) r=rankCount (fun s => P (s.map f)) xs r := by
 unfold rankCount
 rw [subsets_map,sumBy_map]
 simp

/-- Coefficients on an actual induced graph are the counts over its selected
 vertices in the original graph. Injectivity is needed only for forest preservation. -/
theorem coefficient_inducedGraph {n m : Nat} (G : Graph n) (f : Fin m → Fin n) (r : Nat) :
 coefficient (Erdos993.Extraction.inducedGraph G f) r=
 rankCount (independent G) ((List.finRange m).map f) r := by
 rw [rankCount_map,←rankCount_graph]
 unfold rankCount
 apply sumBy_congr
 intro s hs
 rw [Erdos993.Extraction.independent_inducedGraph]

theorem rankCount_zero {α : Type} (P : List α → Bool) (xs : List α) :
 rankCount P xs 0=if P [] then 1 else 0 := by
 induction xs with
 | nil => simp [rankCount,subsets]
 | cons a xs ih => rw [rankCount_cons_zero,ih]

@[simp] theorem rankCount_false {α : Type} (xs : List α) (r : Nat) :
 rankCount (fun _ => false) xs r=0 := by simp [rankCount]

theorem rankCount_restrict {α : Type} (P : List α → Bool) (xs : List α)
 (allowed : α → Bool) (r : Nat) :
 rankCount (fun s => P s && s.all allowed) xs r=rankCount P (xs.filter allowed) r := by
 induction xs generalizing P r with
 | nil => simp [rankCount,subsets]
 | cons a xs ih =>
   cases r with
   | zero => simp [rankCount_zero]
   | succ r =>
     rw [rankCount_cons_succ]
     cases ha : allowed a
     · simp only [List.all_cons,ha,Bool.false_and,Bool.and_false,rankCount_false,Nat.add_zero]
       rw [ih P (r+1)]
       simp [ha]
     · simp only [List.all_cons,ha,Bool.true_and]
       rw [ih P (r+1),ih (fun s => P (a::s)) r]
       simp [ha,rankCount_cons_succ]

/-- Deletion and closed-neighbourhood deletion, retaining all spectator vertices. -/
theorem graph_root_recurrence {n : Nat} (G : Graph n) (v : Fin n)
 (xs : List (Fin n)) (r : Nat) :
 rankCount (independent G) (v::xs) (r+1)=
 rankCount (independent G) xs (r+1)+
 rankCount (independent G) (xs.filter (fun u => !(G.adj v u))) r := by
 rw [rankCount_cons_succ]
 have hpred : (fun s => independent G (v::s))=
     (fun s => independent G s && s.all (fun u => !(G.adj v u))) := by
   funext s; exact independent_cons_bool G v s
 rw [hpred,rankCount_restrict]

/-- The deletion recurrence at vertex0 of an actual labelled graph.
 The second term counts the actual vertices surviving its closed neighbourhood. -/
theorem coefficient_root_recurrence {n : Nat} (G : Graph (n+1)) (r : Nat) :
 coefficient G (r+1)=
 coefficient (Erdos993.Extraction.inducedGraph G Fin.succ) (r+1)+
 rankCount (independent G) (((List.finRange n).map Fin.succ).filter
   (fun u => !(G.adj ⟨0,by omega⟩ u))) r := by
 rw [coefficient_inducedGraph,←rankCount_graph,List.finRange_succ]
 exact graph_root_recurrence G ⟨0,by omega⟩ _ r

/-- The induced graph on a vertex list, with its actual cardinality as order. -/
def inducedOn {n : Nat} (G : Graph n) (xs : List (Fin n)) : Graph xs.length :=
 Erdos993.Extraction.inducedGraph G (fun i => xs[i.val])

theorem finRange_map_get {α : Type} (xs : List α) :
 (List.finRange xs.length).map (fun i => xs[i.val])=xs := by
 simp [List.finRange,List.map_ofFn,Function.comp_def]

theorem coefficient_inducedOn {n : Nat} (G : Graph n) (xs : List (Fin n)) (r : Nat) :
 coefficient (inducedOn G xs) r=rankCount (independent G) xs r := by
 unfold inducedOn
 rw [coefficient_inducedGraph,finRange_map_get]

theorem list_vertex_injective {α : Type} (xs : List α) (hx : xs.Nodup)
 (i j : Fin xs.length) (h : xs[i.val]=xs[j.val]) : i=j := by
 apply Fin.ext
 exact (List.getElem_inj hx).mp h

theorem inducedOn_isForest {n : Nat} (G : Graph n) (hf : IsForest G)
 (xs : List (Fin n)) (hx : xs.Nodup) : IsForest (inducedOn G xs) :=
 Erdos993.Extraction.inducedGraph_isForest G hf _ (list_vertex_injective xs hx)

theorem critical_inducedOn_unimodal (w : Closure.CriticalWitness) (xs : List (Fin w.n))
 (hx : xs.Nodup) (hm : xs.length<w.n) : Unimodal (coefficient (inducedOn w.graph xs)) :=
 Erdos993.Extraction.critical_proper_induced_unimodal w xs.length hm _
   (list_vertex_injective xs hx)

/-- Both summands now refer to actual graphs, including an empty residual. -/
theorem coefficient_root_recurrence_graphs {n : Nat} (G : Graph (n+1)) (r : Nat) :
 coefficient G (r+1)=
 coefficient (Erdos993.Extraction.inducedGraph G Fin.succ) (r+1)+
 coefficient (inducedOn G (((List.finRange n).map Fin.succ).filter
   (fun u => !(G.adj ⟨0,by omega⟩ u)))) r := by
 rw [coefficient_inducedOn]
 exact coefficient_root_recurrence G r

def rootResidualVertices {n : Nat} (G : Graph (n+1)) : List (Fin (n+1)) :=
 ((List.finRange n).map Fin.succ).filter (fun u => !(G.adj ⟨0,by omega⟩ u))

theorem rootResidualVertices_nodup {n : Nat} (G : Graph (n+1)) :
 (rootResidualVertices G).Nodup := by
 apply List.Sublist.nodup (List.filter_sublist)
 exact nodup_map_injective Fin.succ _ (by intros; simp_all) (finRange_nodup n)

theorem rootResidualVertices_length {n : Nat} (G : Graph (n+1)) :
 (rootResidualVertices G).length≤n := by
 have h := List.length_filter_le (fun u => !(G.adj ⟨0,by omega⟩ u))
   ((List.finRange n).map Fin.succ)
 simpa [rootResidualVertices] using h

/-- Acyclicity survives both actual deletions in the coefficient recurrence. -/
theorem root_children_forest {n : Nat} (G : Graph (n+1)) (hf : IsForest G) :
 IsForest (Erdos993.Extraction.inducedGraph G Fin.succ) ∧
 IsForest (inducedOn G (rootResidualVertices G)) := by
 constructor
 · exact Erdos993.Extraction.inducedGraph_isForest G hf Fin.succ (by intros; simp_all)
 · exact inducedOn_isForest G hf _ (rootResidualVertices_nodup G)

/-- This is only ordinary U of children, not their MU or log-concavity. -/
theorem root_children_unimodal_of_minimality {n : Nat} (G : Graph (n+1))
 (hf : IsForest G)
 (hmin : ∀ m, m<n+1 → ∀ H : Graph m, IsForest H → Unimodal (coefficient H)) :
 Unimodal (coefficient (Erdos993.Extraction.inducedGraph G Fin.succ)) ∧
 Unimodal (coefficient (inducedOn G (rootResidualVertices G))) := by
 have hc := root_children_forest G hf
 constructor
 · exact hmin n (by omega) _ hc.1
 · exact hmin _ (by have := rootResidualVertices_length G; omega) _ hc.2

end Erdos993.Counting
