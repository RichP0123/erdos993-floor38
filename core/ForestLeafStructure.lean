import GraphExtensionCounting

/-! Structural facts in the existing cycle-free finite graph model.
No rooted-tree representation is assumed. -/
set_option maxHeartbeats 4000000
namespace Erdos993.Structure
open Erdos993.Counting

/-- A simple path with l edges and l+1 distinct vertices. -/
structure SimplePath {n : Nat} (G : Graph n) (l : Nat) where
 vertex : Fin (l+1) → Fin n
 injective : ∀ i j, vertex i=vertex j → i=j
 consecutive : ∀ i : Fin l, G.adj (vertex i.castSucc) (vertex i.succ)=true

theorem path_order_bound {n l : Nat} {G : Graph n} (p : SimplePath G l) : l+1≤n := by
 have hn := nodup_map_injective p.vertex (List.finRange (l+1)) p.injective
   (finRange_nodup (l+1))
 have hh := sumBy_le (List.finRange n)
   (fun v => if v∈((List.finRange (l+1)).map p.vertex) then 1 else 0)
   (fun _ => 1) (by intro v hv; dsimp; split <;> omega)
 rw [selected_membership_sum _ hn,sumBy_const] at hh
 simpa using hh

theorem path_no_endpoint_chord {n l : Nat} {G : Graph n} (hf : IsForest G)
 (p : SimplePath G l) (t : Fin (l+1)) (ht : 2≤t.val) :
 G.adj (p.vertex ⟨0,by omega⟩) (p.vertex t)=false := by
 cases he : G.adj (p.vertex ⟨0,by omega⟩) (p.vertex t) with
 | false => rfl
 | true =>
   let k := t.val-2
   have hk : k+2=t.val := by dsimp [k]; omega
   let f : Fin (k+3) → Fin n := fun i => p.vertex ⟨i.val,by omega⟩
   have hinj : ∀ i j, f i=f j → i=j := by
     intro i j hij
     have hh := p.injective _ _ hij
     apply Fin.ext
     exact congrArg (fun z : Fin (l+1) => z.val) hh
   apply False.elim
   apply hf k f hinj
   intro i
   by_cases hlast : i.val=k+2
   · have hi : (⟨i.val,by omega⟩ : Fin (l+1))=t := by apply Fin.ext; dsimp; omega
     have hc : (cycleNext i).val=0 := by simp [cycleNext,hlast]
     have hc' : (⟨(cycleNext i).val,by omega⟩ : Fin (l+1))=⟨0,by omega⟩ := by
       apply Fin.ext; exact hc
     change G.adj (p.vertex _) (p.vertex _)=true
     rw [hi,hc',G.symm]
     exact he
   · have hil : i.val<l := by omega
     have hc : (cycleNext i).val=i.val+1 := by
       simp [cycleNext,Nat.mod_eq_of_lt (show i.val+1<k+3 by omega)]
     have hh := p.consecutive (⟨i.val,hil⟩ : Fin l)
     have hc' : (⟨(cycleNext i).val,by omega⟩ : Fin (l+1))=
         (⟨i.val,hil⟩ : Fin l).succ := by apply Fin.ext; exact hc
     change G.adj (p.vertex _) (p.vertex _)=true
     rw [hc']
     exact hh

def singletonPath {n : Nat} (G : Graph n) (v : Fin n) : SimplePath G 0 where
 vertex := fun _ => v
 injective := by intro i j h; apply Fin.ext; omega
 consecutive := by intro i; exact Fin.elim0 i

def prependPath {n l : Nat} {G : Graph n} (p : SimplePath G l) (v : Fin n)
 (hn : ∀ i, v≠p.vertex i) (he : G.adj v (p.vertex ⟨0,by omega⟩)=true) :
 SimplePath G (l+1) where
 vertex := Fin.cases v p.vertex
 injective := by
   intro i j
   refine Fin.cases ?_ (fun i => ?_) i
   · refine Fin.cases ?_ (fun j => ?_) j
     · intro; rfl
     · intro h; exact False.elim (hn j h)
   · refine Fin.cases ?_ (fun j => ?_) j
     · intro h; exact False.elim (hn i h.symm)
     · intro h; exact congrArg Fin.succ (p.injective i j h)
 consecutive := by
   intro i
   refine Fin.cases ?_ (fun j => ?_) i
   · exact he
   · exact p.consecutive j

theorem bounded_maximum (P : Nat → Prop) (N : Nat)
 (hex : ∃ k, P k) (hbound : ∀ k, P k → k≤N) :
 ∃ k, P k ∧ ∀ j, P j → j≤k := by
 induction N with
 | zero =>
   obtain ⟨k,hk⟩ := hex
   refine ⟨k,hk,?_⟩
   intro j hj; have := hbound j hj; omega
 | succ N ih =>
   by_cases htop : P (N+1)
   · exact ⟨N+1,htop,hbound⟩
   · apply ih
     intro k hk
     have := hbound k hk
     by_cases he : k=N+1
     · subst k; contradiction
     · omega

theorem exists_longest_path {n : Nat} (G : Graph n) (hn : 0<n) :
 ∃ l, ∃ _p : SimplePath G l, ∀ k, Nonempty (SimplePath G k) → k≤l := by
 obtain ⟨l,⟨p⟩,hmax⟩ := bounded_maximum
   (fun k => Nonempty (SimplePath G k)) n
   ⟨0,⟨singletonPath G ⟨0,hn⟩⟩⟩
   (by intro k hk; obtain ⟨p⟩ := hk; have := path_order_bound p; omega)
 exact ⟨l,p,hmax⟩

theorem longest_path_neighbor_present {n l : Nat} {G : Graph n}
 (p : SimplePath G l) (hmax : ∀ k, Nonempty (SimplePath G k) → k≤l)
 (v : Fin n) (he : G.adj (p.vertex ⟨0,by omega⟩) v=true) :
 ∃ i, v=p.vertex i := by
 classical
 by_cases hex : ∃ i, v=p.vertex i
 · exact hex
 · have hn : ∀ i, v≠p.vertex i := by intro i hi; exact hex ⟨i,hi⟩
   have hp := prependPath p v hn (by rw [G.symm]; exact he)
   have hh := hmax (l+1) ⟨hp⟩
   omega

theorem longest_path_endpoint_leaf {n l : Nat} {G : Graph n} (hf : IsForest G)
 (p : SimplePath G l) (hmax : ∀ k, Nonempty (SimplePath G k) → k≤l) :
 ∀ u w, G.adj (p.vertex ⟨0,by omega⟩) u=true →
   G.adj (p.vertex ⟨0,by omega⟩) w=true → u=w := by
 intro u w hu hw
 obtain ⟨i,hi⟩ := longest_path_neighbor_present p hmax u hu
 obtain ⟨j,hj⟩ := longest_path_neighbor_present p hmax w hw
 have indices : ∀ t : Fin (l+1), G.adj (p.vertex ⟨0,by omega⟩) (p.vertex t)=true → t.val=1 := by
   intro t ht
   have h0 : t.val≠0 := by
     intro he
     have hz : t=⟨0,by omega⟩ := by apply Fin.ext; exact he
     rw [hz,G.loopless] at ht
     contradiction
   have h2 : ¬2≤t.val := by
     intro he
     rw [path_no_endpoint_chord hf p t he] at ht
     contradiction
   omega
 have hival := indices i (by rw [←hi]; exact hu)
 have hjval := indices j (by rw [←hj]; exact hw)
 have hij : i=j := by apply Fin.ext; omega
 rw [hi,hj,hij]

theorem forest_has_leaf_or_isolate {n : Nat} (G : Graph n) (hf : IsForest G) (hn : 0<n) :
 ∃ v : Fin n, ∀ u w, G.adj v u=true → G.adj v w=true → u=w := by
 obtain ⟨l,p,hmax⟩ := exists_longest_path G hn
 exact ⟨p.vertex ⟨0,by omega⟩,longest_path_endpoint_leaf hf p hmax⟩

def reversePath {n l : Nat} {G : Graph n} (p : SimplePath G l) : SimplePath G l where
 vertex := fun i => p.vertex i.rev
 injective := by
   intro i j h
   have hh := p.injective _ _ h
   have hv := congrArg Fin.rev hh
   simpa using hv
 consecutive := by
   intro i
   let j : Fin l := ⟨l-1-i.val,by omega⟩
   have h1 : i.castSucc.rev=j.succ := by apply Fin.ext; simp [Fin.rev,j]; omega
   have h2 : i.succ.rev=j.castSucc := by apply Fin.ext; simp [Fin.rev,j]; omega
   rw [h1,h2,G.symm]
   exact p.consecutive j

theorem forest_leaf_away_from_root {n : Nat} (G : Graph n) (hf : IsForest G)
 (hn : 2≤n) (root : Fin n) :
 ∃ v : Fin n, v≠root ∧ ∀ u w, G.adj v u=true → G.adj v w=true → u=w := by
 obtain ⟨l,p,hmax⟩ := exists_longest_path G (by omega)
 by_cases hl : l=0
 · let v : Fin n := if root.val=0 then ⟨1,by omega⟩ else ⟨0,by omega⟩
   have hv : v≠root := by
     intro he
     have hh := congrArg Fin.val he
     dsimp [v] at hh
     split at hh <;> simp_all
   refine ⟨v,hv,?_⟩
   exact longest_path_endpoint_leaf hf (singletonPath G v)
     (by intro k hk; have := hmax k hk; omega)
 · by_cases hroot : p.vertex ⟨0,by omega⟩=root
   · refine ⟨(reversePath p).vertex ⟨0,by omega⟩,?_,
       longest_path_endpoint_leaf hf (reversePath p) hmax⟩
     intro he
     have hh := p.injective _ _ (he.trans hroot.symm)
     have hv := congrArg Fin.val hh
     simp [Fin.rev] at hv
     omega
   · exact ⟨p.vertex ⟨0,by omega⟩,hroot,longest_path_endpoint_leaf hf p hmax⟩

def deleteVertices {n : Nat} (v : Fin n) : List (Fin n) := (List.finRange n).erase v

theorem deleteVertices_nodup {n : Nat} (v : Fin n) : (deleteVertices v).Nodup :=
 List.Sublist.nodup List.erase_sublist (finRange_nodup n)

theorem deleteVertices_length {n : Nat} (v : Fin n) : (deleteVertices v).length=n-1 := by
 simp [deleteVertices,List.length_erase_of_mem (List.mem_finRange v)]

def deleteVertex {n : Nat} (G : Graph n) (v : Fin n) := inducedOn G (deleteVertices v)

theorem deleteVertex_isForest {n : Nat} (G : Graph n) (hf : IsForest G) (v : Fin n) :
 IsForest (deleteVertex G v) := inducedOn_isForest G hf _ (deleteVertices_nodup v)

theorem root_survives_deletion {n : Nat} (v root : Fin n) (hv : v≠root) :
 ∃ i : Fin (deleteVertices v).length, (deleteVertices v)[i.val]=root := by
 have hm : root∈deleteVertices v := by
   apply (List.mem_erase_of_ne (Ne.symm hv)).mpr
   exact List.mem_finRange root
 obtain ⟨i,hi,he⟩ := List.getElem_of_mem hm
 exact ⟨⟨i,hi⟩,he⟩

/-- Root-preserving induction on actual acyclic graphs. The base has one vertex.
The surviving root is identified by its original vertex, not just its label. -/
theorem forest_rooted_leaf_induction (P : {n : Nat} → (G : Graph n) → Fin n → Prop)
 (single : ∀ (G : Graph 1) (root : Fin 1), P G root)
 (step : ∀ {n : Nat} (G : Graph n) (_hf : IsForest G) (root v : Fin n),
   v≠root → (∀ u w, G.adj v u=true → G.adj v w=true → u=w) →
   ∀ i : Fin (deleteVertices v).length, (deleteVertices v)[i.val]=root →
   P (deleteVertex G v) i → P G root) :
 ∀ {n : Nat} (G : Graph n), IsForest G → ∀ root : Fin n, P G root := by
 intro n
 induction n using Nat.strongRecOn with
 | ind n ih =>
   intro G hf root
   by_cases hn : n=1
   · subst n; exact single G root
   · have htwo : 2≤n := by have := root.isLt; omega
     obtain ⟨v,hv,hleaf⟩ := forest_leaf_away_from_root G hf htwo root
     obtain ⟨i,hi⟩ := root_survives_deletion v root hv
     apply step G hf root v hv hleaf i hi
     apply ih (deleteVertices v).length
     · rw [deleteVertices_length]; omega
     · exact deleteVertex_isForest G hf v

/-- Induction by deleting an actual leaf or isolate, derived from absence of cycles.
The extension step must prove its property for the parent; it is not assumed U. -/
theorem forest_leaf_induction (P : {n : Nat} → Graph n → Prop)
 (empty : ∀ G : Graph 0, P G)
 (step : ∀ {n : Nat} (G : Graph n) (_hf : IsForest G) (v : Fin n),
   (∀ u w, G.adj v u=true → G.adj v w=true → u=w) →
   P (deleteVertex G v) → P G) :
 ∀ {n : Nat} (G : Graph n), IsForest G → P G := by
 intro n
 induction n using Nat.strongRecOn with
 | ind n ih =>
   intro G hf
   cases n with
   | zero => exact empty G
   | succ n =>
     obtain ⟨v,hv⟩ := forest_has_leaf_or_isolate G hf (by omega)
     apply step G hf v hv
     apply ih (deleteVertices v).length
     · rw [deleteVertices_length]; omega
     · exact deleteVertex_isForest G hf v

theorem nodup_length_le_one {α : Type} (xs : List α) (hx : xs.Nodup)
 (hu : ∀ a∈xs, ∀ b∈xs, a=b) : xs.length≤1 := by
 cases xs with
 | nil => simp
 | cons a xs =>
   cases xs with
   | nil => simp
   | cons b xs =>
     have he : a=b := hu a (by simp) b (by simp)
     have hh := (List.nodup_cons.mp hx).1
     exact False.elim (hh (by simp [he]))

theorem degree_le_one {n : Nat} (G : Graph n) (v : Fin n)
 (hv : ∀ u w, G.adj v u=true → G.adj v w=true → u=w) : degree G v≤1 := by
 unfold degree
 apply nodup_length_le_one
 · exact List.Sublist.nodup List.filter_sublist (finRange_nodup n)
 · intro u hu w hw
   exact hv u w (List.mem_filter.mp hu).2 (List.mem_filter.mp hw).2

theorem forest_has_degree_le_one {n : Nat} (G : Graph n) (hf : IsForest G) (hn : 0<n) :
 ∃ v : Fin n, degree G v≤1 := by
 obtain ⟨v,hv⟩ := forest_has_leaf_or_isolate G hf hn
 exact ⟨v,degree_le_one G v hv⟩

theorem rankCount_congr {α : Type} (P Q : List α → Bool) (xs : List α) (r : Nat)
 (h : ∀ s, P s=Q s) : rankCount P xs r=rankCount Q xs r := by
 unfold rankCount
 apply sumBy_congr
 intro s hs
 rw [h s]

theorem rankCount_perm {α : Type} {xs ys : List α} (h : xs.Perm ys)
 (P : List α → Bool) (hp : PermInvariant P) (r : Nat) :
 rankCount P xs r=rankCount P ys r := by
 induction h generalizing P r with
 | nil => rfl
 | cons a h ih =>
   cases r with
   | zero => simp [rankCount_zero]
   | succ r =>
     rw [rankCount_cons_succ,rankCount_cons_succ,
       ih P hp (r+1),ih (fun s => P (a::s)) (permInvariant_cons P hp a) r]
 | swap a b xs =>
   cases r with
   | zero => simp [rankCount_zero]
   | succ r =>
     rw [rankCount_cons_succ,rankCount_cons_succ]
     cases r with
     | zero => simp [rankCount_cons_succ,rankCount_zero,Nat.add_comm,Nat.add_left_comm]
     | succ r =>
       simp only [rankCount_cons_succ]
       have hh := rankCount_congr (fun s => P (a::b::s)) (fun s => P (b::a::s)) xs r
         (fun s => hp _ _ (List.Perm.swap b a s))
       omega
 | trans h1 h2 ih1 ih2 => exact (ih1 P hp r).trans (ih2 P hp r)

/-- Deletion recurrence at any chosen vertex, not only at label zero. -/
theorem coefficient_vertex_recurrence {n : Nat} (G : Graph n) (v : Fin n) (r : Nat) :
 coefficient G (r+1)=coefficient (deleteVertex G v) (r+1)+
   coefficient (inducedOn G ((deleteVertices v).filter (fun u => !(G.adj v u)))) r := by
 rw [coefficient_inducedOn]
 change coefficient G (r+1)=coefficient (inducedOn G (deleteVertices v)) (r+1)+_
 rw [coefficient_inducedOn,←rankCount_graph]
 rw [rankCount_perm (List.perm_cons_erase (List.mem_finRange v))
   (independent G) (independent_permInvariant G) (r+1)]
 exact graph_root_recurrence G v (deleteVertices v) r

end Erdos993.Structure
