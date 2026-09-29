import GraphExtensionUpper
namespace Erdos993.LeafBoundary
open Counting Structure CurvatureProof

theorem unimodal_tail_of_fall (a : Nat → Nat) (hu : Unimodal a)
 (M : Nat) (hf : a (M+1)<a M) : ∀ i, M≤i → a (i+1)≤a i := by
 obtain ⟨m,up,down⟩ := hu
 have hm : m≤M := by
   by_cases hn : m≤M
   · exact hn
   · have hh := up M (by omega)
     omega
 intro i hi
 exact down i (by omega)

/-- The two proper-child tails block a returning rise. The previous-rank
 certificate is explicit; ordinary child unimodality alone is not enough. -/
theorem leaf_transfer_no_return (f g h q : Nat → Nat) (M b : Nat)
 (hM : 1≤M) (hb : M<b)
 (fg : ∀ r, f (r+1)=g (r+1)+h r)
 (gh : ∀ r, g (r+1)=h (r+1)+q r)
 (fall : f (M+1)<f M)
 (hp : h (M-1)≤h M)
 (hc : h (M-1)+q (M-1)≤h M+q M)
 (ug : Unimodal g) (uh : Unimodal h) : f (b+1)≤f b := by
 have he : M-1+1=M := by omega
 have e1 := fg M
 have e2 := fg (M-1)
 have e3 := gh M
 have e4 := gh (M-1)
 rw [he] at e2 e4
 have hg : g (M+1)<g M := by omega
 have hh : h (M+1)<h M := by omega
 have tg := unimodal_tail_of_fall g ug M hg b (by omega)
 have th := unimodal_tail_of_fall h uh M hh (b-1) (by omega)
 have eb := fg (b-1)
 have ei : b-1+1=b := by omega
 rw [ei] at eb th
 have en := fg b
 omega

theorem forest_prefix_step {n : Nat} (G : Graph n) (hf : IsForest G) (r : Nat)
 (hr : 4*r<n) : coefficient G r≤coefficient G (r+1) := by
 by_cases hn : coefficient G r≤coefficient G (r+1)
 · exact hn
 · have hh := forest_first_fall_quarter_bound G hf r (by omega)
   omega

theorem rankCount_vertex_recurrence {n : Nat} (G : Graph n)
 (xs : List (Fin n)) (v : Fin n) (hv : v∈xs) (r : Nat) :
 rankCount (independent G) xs (r+1)=
 rankCount (independent G) (xs.erase v) (r+1)+
 rankCount (independent G) ((xs.erase v).filter (fun u => !(G.adj v u))) r := by
 rw [rankCount_perm (List.perm_cons_erase hv) (independent G)
   (independent_permInvariant G) (r+1)]
 exact graph_root_recurrence G v (xs.erase v) r

theorem sublist_eq_of_members {α : Type} [DecidableEq α]
 (xs s t : List α) (hx : xs.Nodup) (hs : s.Sublist xs) (ht : t.Sublist xs)
 (hm : ∀ v, v∈s ↔ v∈t) : s=t := by
 rw [←FiniteMarked.canonical_sublist xs s hx hs,
     ←FiniteMarked.canonical_sublist xs t hx ht]
 apply List.filter_congr
 intro v hv
 simp only [hm v]

def leafPairVertices {n : Nat} (l v : Fin n) : List (Fin n) :=
 (deleteVertices l).erase v

theorem leaf_residual_eq {n : Nat} (G : Graph n) (l v : Fin n)
 (hl : ∀ u, G.adj l u=true ↔ u=v) :
 (deleteVertices l).filter (fun u => !(G.adj l u))=leafPairVertices l v := by
 unfold leafPairVertices
 rw [List.Nodup.erase_eq_filter (deleteVertices_nodup l)]
 apply List.filter_congr
 intro u hu
 have hh := hl u
 cases he : G.adj l u <;> simp_all

/-- Both leaf recurrences use the same actual two-vertex deletion. -/
theorem actual_leaf_recurrences {n : Nat} (G : Graph n) (l v : Fin n)
 (hlv : l≠v) (hl : ∀ u, G.adj l u=true ↔ u=v) (r : Nat) :
 coefficient G (r+1)=coefficient (deleteVertex G l) (r+1)+
     coefficient (inducedOn G (leafPairVertices l v)) r ∧
 coefficient (deleteVertex G l) (r+1)=
     coefficient (inducedOn G (leafPairVertices l v)) (r+1)+
     coefficient (inducedOn G ((leafPairVertices l v).filter (fun u => !(G.adj v u)))) r := by
 constructor
 · have h := coefficient_vertex_recurrence G l r
   simp only [coefficient_inducedOn] at h ⊢
   rw [leaf_residual_eq G l v hl] at h
   exact h
 · change coefficient (inducedOn G (deleteVertices l)) (r+1)=_
   simp only [coefficient_inducedOn]
   apply rankCount_vertex_recurrence
   simp [deleteVertices,List.mem_erase_of_ne (Ne.symm hlv)]

theorem leafPair_nodup {n : Nat} (l v : Fin n) : (leafPairVertices l v).Nodup :=
 List.Sublist.nodup List.erase_sublist (deleteVertices_nodup l)

theorem leafPair_length {n : Nat} (l v : Fin n) (hlv : l≠v) :
 (leafPairVertices l v).length+2=n := by
 have hv : v∈deleteVertices l := by
   simp [deleteVertices,List.mem_erase_of_ne (Ne.symm hlv)]
 have he := List.length_erase_of_mem hv
 have hn := deleteVertices_length l
 have hp := List.length_pos_of_mem hv
 change ((deleteVertices l).erase v).length+2=n
 omega

/-- A minimal counterexample cannot pass a certified actual leaf transfer. -/
theorem critical_leaf_certificate_impossible (w : Closure.CriticalWitness)
 (l v : Fin w.n) (hlv : l≠v) (hl : ∀ u, w.graph.adj l u=true ↔ u=v)
 (hp : coefficient (inducedOn w.graph (leafPairVertices l v)) (w.M-1)≤
       coefficient (inducedOn w.graph (leafPairVertices l v)) w.M)
 (hc : coefficient (inducedOn w.graph (leafPairVertices l v)) (w.M-1)+
       coefficient (inducedOn w.graph ((leafPairVertices l v).filter (fun u => !(w.graph.adj v u)))) (w.M-1)≤
       coefficient (inducedOn w.graph (leafPairVertices l v)) w.M+
       coefficient (inducedOn w.graph ((leafPairVertices l v).filter (fun u => !(w.graph.adj v u)))) w.M) : False := by
 have recs := actual_leaf_recurrences w.graph l v hlv hl
 have ug := critical_inducedOn_unimodal w (deleteVertices l) (deleteVertices_nodup l)
   (by have := deleteVertices_length l; have := l.isLt; omega)
 have uh := critical_inducedOn_unimodal w (leafPairVertices l v) (leafPair_nodup l v)
   (by have := leafPair_length l v hlv; omega)
 have hh := leaf_transfer_no_return (coefficient w.graph) (coefficient (deleteVertex w.graph l))
   (coefficient (inducedOn w.graph (leafPairVertices l v)))
   (coefficient (inducedOn w.graph ((leafPairVertices l v).filter (fun u => !(w.graph.adj v u)))))
   w.M w.b w.positiveFallIndex w.returnAfterFall
   (fun r => (recs r).1) (fun r => (recs r).2) w.firstFall hp hc ug uh
 have hr := w.returningRise
 omega

theorem filter_complement_lengths {α : Type} (xs : List α) (p : α → Bool) :
 (xs.filter p).length+(xs.filter (fun x => !(p x))).length=xs.length := by
 induction xs with
 | nil => simp
 | cons a xs ih => cases hp : p a <;> simp [hp] <;> omega

theorem leaf_closed_residual_length {n : Nat} (G : Graph n) (l v : Fin n)
 (hlv : l≠v) (hl : ∀ u, G.adj l u=true ↔ u=v) :
 ((leafPairVertices l v).filter (fun u => !(G.adj v u))).length+degree G v+1=n := by
 have ha : G.adj v l=true := by rw [G.symm]; exact (hl v).mpr rfl
 have hm : l∈(List.finRange n).filter (fun u => G.adj v u) := by simp [ha]
 have hn : v∉((List.finRange n).filter (fun u => G.adj v u)).erase l := by
   intro h
   have hh := List.mem_filter.mp (List.mem_of_mem_erase h)
   have he := G.loopless v
   simp [he] at hh
 have hd := List.length_erase_of_mem hm
 have he : ((leafPairVertices l v).filter (fun u => G.adj v u)).length+1=degree G v := by
   unfold leafPairVertices deleteVertices
   rw [←List.erase_filter,←List.erase_filter,List.erase_of_not_mem hn]
   change _+1=((List.finRange n).filter (fun u => G.adj v u)).length
   have hp := List.length_pos_of_mem hm
   omega
 have hc := filter_complement_lengths (leafPairVertices l v) (fun u => G.adj v u)
 have ht := leafPair_length l v hlv
 omega

/-- Actual graph exclusion of every quarter-boundary critical witness with
 a leaf whose neighbour has degree at most two. -/
theorem critical_quarter_leaf_degree_two_impossible (w : Closure.CriticalWitness)
 (hn : w.n=4*w.M) (l v : Fin w.n) (hlv : l≠v)
 (hl : ∀ u, w.graph.adj l u=true ↔ u=v) (hd : degree w.graph v≤2) : False := by
 have hh := leafPair_length l v hlv
 have hq := leaf_closed_residual_length w.graph l v hlv hl
 have hp := w.positiveFallIndex
 have hf := inducedOn_isForest w.graph w.forest (leafPairVertices l v) (leafPair_nodup l v)
 have hqf := inducedOn_isForest w.graph w.forest
   ((leafPairVertices l v).filter (fun u => !(w.graph.adj v u)))
   (List.Sublist.nodup List.filter_sublist (leafPair_nodup l v))
 have h1 := forest_prefix_step _ hf (w.M-1) (by omega)
 have h2 := forest_prefix_step _ hqf (w.M-1) (by omega)
 have hi : w.M-1+1=w.M := by omega
 rw [hi] at h1 h2
 exact critical_leaf_certificate_impossible w l v hlv hl h1 (by omega)

theorem rankCount_filter_le {α : Type} (P : List α → Bool) (xs : List α)
 (allowed : α → Bool) (r : Nat) : rankCount P (xs.filter allowed) r≤rankCount P xs r := by
 rw [←rankCount_restrict]
 unfold rankCount
 apply sumBy_le
 intro s hs
 by_cases hr : s.length=r <;> cases hp : P s <;> simp [hr,hp]
 split <;> omega

theorem induced_filter_coefficient_le {n : Nat} (G : Graph n) (xs : List (Fin n))
 (p : Fin n → Bool) (r : Nat) :
 coefficient (inducedOn G (xs.filter p)) r≤coefficient (inducedOn G xs) r := by
 simp only [coefficient_inducedOn]
 exact rankCount_filter_le _ _ _ _

theorem forest_slope_growth {n : Nat} (G : Graph n) (hf : IsForest G) (r : Nat) :
 ((n:Int)-4*(r:Int)-1)*(coefficient G r:Int)≤
 ((r:Int)+1)*((coefficient G (r+1):Int)-(coefficient G r:Int)) := by
 have hg := graph_curvature_growth G r
 have hc := forest_curvature_nonnegative G hf r
 grind

/-- Degree-three supports are excluded using actual induced containment,
 including the empty closed-neighbourhood residual. -/
theorem critical_quarter_leaf_degree_three_impossible (w : Closure.CriticalWitness)
 (hn : w.n=4*w.M) (l v : Fin w.n) (hlv : l≠v)
 (hl : ∀ u, w.graph.adj l u=true ↔ u=v) (hd : degree w.graph v≤3) : False := by
 let H := inducedOn w.graph (leafPairVertices l v)
 let Q := inducedOn w.graph ((leafPairVertices l v).filter (fun u => !(w.graph.adj v u)))
 have hh := leafPair_length l v hlv
 have hq := leaf_closed_residual_length w.graph l v hlv hl
 have hp := w.positiveFallIndex
 have hf : IsForest H := inducedOn_isForest w.graph w.forest _ (leafPair_nodup l v)
 have hqf : IsForest Q := inducedOn_isForest w.graph w.forest _
   (List.Sublist.nodup List.filter_sublist (leafPair_nodup l v))
 have h1 := forest_prefix_step H hf (w.M-1) (by omega)
 have gi := forest_slope_growth H hf (w.M-1)
 have gq := forest_slope_growth Q hqf (w.M-1)
 have hc : coefficient Q (w.M-1)≤coefficient H (w.M-1) :=
   induced_filter_coefficient_le w.graph _ _ _
 have hi : w.M-1+1=w.M := by omega
 rw [hi] at h1 gi gq
 have hm : (((w.M-1:Nat):Int)+1)=(w.M:Int) := by omega
 have ho : ((leafPairVertices l v).length:Int)-4*((w.M-1:Nat):Int)-1=1 := by omega
 change (_ : Int)≤_ at gi gq
 rw [ho] at gi
 rw [hm] at gi gq
 have hqo : (-1:Int)≤(((leafPairVertices l v).filter (fun u => !(w.graph.adj v u))).length:Int)-
   4*((w.M-1:Nat):Int)-1 := by omega
 have mulq := Int.mul_le_mul_of_nonneg_right hqo (Int.natCast_nonneg (coefficient Q (w.M-1)))
 have hci := Int.ofNat_le.mpr hc
 have hs : (coefficient H (w.M-1):Int)+(coefficient Q (w.M-1):Int)≤
     (coefficient H w.M:Int)+(coefficient Q w.M:Int) := by
   have hpositive : (0:Int)<(w.M:Int) := by omega
   have hz : 0≤(w.M:Int)*((coefficient H w.M:Int)-(coefficient H (w.M-1):Int)+
       ((coefficient Q w.M:Int)-(coefficient Q (w.M-1):Int))) := by
     rw [Int.mul_add]
     omega
   have hh := Int.nonneg_of_mul_nonneg_right hz hpositive
   omega
 apply critical_leaf_certificate_impossible w l v hlv hl h1
 change coefficient H (w.M-1)+coefficient Q (w.M-1)≤coefficient H w.M+coefficient Q w.M
 omega

end Erdos993.LeafBoundary
