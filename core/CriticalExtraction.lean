import ClosureInterfaces
import NoRecoveryFoundation

/-! Graph-level extraction for the existing minimum-counterexample program.
No smaller-forest MU or LC assumption is introduced. -/
namespace Erdos993.Extraction
open Erdos993.Foundation Erdos993.Closure

theorem zero_filter {n : Nat} (G : Graph n) (xs : List (Fin n)) :
 ((subsets xs).filter (fun s => decide (s.length=0) && independent G s)) = [[]] := by
 induction xs with
 | nil => simp [subsets, independent]
 | cons a xs ih =>
   rw [subsets, List.filter_append, ih, List.filter_map]
   simp [Function.comp_def]

theorem coefficient_zero {n : Nat} (G : Graph n) : coefficient G 0=1 := by
 unfold coefficient
 rw [zero_filter]
 rfl

theorem coefficient_one_positive {n : Nat} (G : Graph n) (hn : 0<n) :
 0 < coefficient G 1 := by
 unfold coefficient
 apply List.length_pos_iff_exists_mem.mpr
 let v : Fin n := ⟨0,hn⟩
 refine ⟨[v], ?_⟩
 simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
 refine ⟨?_,by simp, independent_singleton G v⟩
 apply (mem_subsets _ _).mpr
 exact List.singleton_sublist.mpr (List.mem_finRange v)

theorem order_zero_unimodal (G : Graph 0) : Unimodal (coefficient G) := by
 refine ⟨0,by intro i hi; omega,?_⟩
 intro i hi
 have hz : coefficient G (i+1)=0 := coefficient_above_order G (by omega)
 omega

theorem bad_graph_has_fall_return {n : Nat} (G : Graph n)
 (hbad : ¬ Unimodal (coefficient G)) :
 ∃ p q, p<q ∧ coefficient G (p+1)<coefficient G p ∧
   coefficient G q<coefficient G (q+1) := by
 classical
 by_cases hex : ∃ p q, p<q ∧ coefficient G (p+1)<coefficient G p ∧
     coefficient G q<coefficient G (q+1)
 · exact hex
 · apply False.elim
   apply hbad
   apply (graph_unimodal_iff_noRecovery G).mpr
   intro p q hpq hp
   by_cases hr : coefficient G (q+1)≤coefficient G q
   · exact hr
   · exact False.elim (hex ⟨p,q,hpq,hp,by omega⟩)

/-- The previously missing extraction: all smaller forests are U, with
 first fall and first later rise. Plateaus and disconnected graphs remain. -/
theorem critical_witness_of_not_target (ht : ¬ Target) : Nonempty CriticalWitness := by
 classical
 obtain ⟨n0,G0,hf0,hb0⟩ := counterexample_iff_not_target.mpr ht
 obtain ⟨n,hn,hmin⟩ := least_witness
   (fun n => ∃ G : Graph n, IsForest G ∧ ¬ Unimodal (coefficient G))
   ⟨n0,G0,hf0,hb0⟩
 obtain ⟨G,hf,hbad⟩ := hn
 have hnpos : 0<n := by
   by_cases hz : n=0
   · subst n; exact False.elim (hbad (order_zero_unimodal G))
   · omega
 obtain ⟨p,q,hpq,hp,hq⟩ := bad_graph_has_fall_return G hbad
 obtain ⟨M,hM,hMmin⟩ := least_witness
   (fun i => coefficient G (i+1)<coefficient G i) ⟨p,hp⟩
 have hMp : M≤p := by
   by_cases hh : M≤p
   · exact hh
   · exact False.elim (hMmin p (by omega) hp)
 have hMpos : 1≤M := by
   have hz := coefficient_zero G
   have ho := coefficient_one_positive G hnpos
   by_cases he : M=0
   · subst M
     change coefficient G 1 < coefficient G 0 at hM
     omega
   · omega
 obtain ⟨b,hb,hbmin⟩ := least_witness
   (fun i => M<i ∧ coefficient G i<coefficient G (i+1)) ⟨q,by omega,hq⟩
 refine ⟨{
   n := n
   M := M
   b := b
   graph := G
   forest := hf
   positiveFallIndex := hMpos
   smallerForestUnimodal := ?_
   firstFall := hM
   noEarlierFall := ?_
   returnAfterFall := hb.1
   returningRise := hb.2
   noIntermediateReturn := ?_
 }⟩
 · intro m hm H hH
   by_cases hu : Unimodal (coefficient H)
   · exact hu
   · exact False.elim (hmin m hm ⟨H,hH,hu⟩)
 · intro i hi
   have hh := hMmin i hi
   omega
 · intro i hMi hib
   have hh := hbmin i hib
   by_cases hd : coefficient G (i+1)≤coefficient G i
   · exact hd
   · exact False.elim (hh ⟨hMi,by omega⟩)

theorem critical_witness_iff_not_target : Nonempty CriticalWitness ↔ ¬ Target := by
 constructor
 · rintro ⟨w⟩; exact critical_witness_not_target w
 · exact critical_witness_of_not_target

/-- An induced graph on a selected list of distinct vertices; the injection
 hypothesis appears on the forest theorem rather than in this definition. -/
def inducedGraph {n m : Nat} (G : Graph n) (f : Fin m → Fin n) : Graph m where
 adj := fun u v => G.adj (f u) (f v)
 symm := by intro u v; exact G.symm (f u) (f v)
 loopless := by intro u; exact G.loopless (f u)

theorem inducedGraph_isForest {n m : Nat} (G : Graph n) (hf : IsForest G)
 (f : Fin m → Fin n) (hinj : ∀ u v, f u=f v → u=v) :
 IsForest (inducedGraph G f) := by
 intro k v hv hc
 apply hf k (fun i => f (v i)) ?_ hc
 intro i j hij
 exact hv i j (hinj (v i) (v j) hij)

theorem independent_inducedGraph {n m : Nat} (G : Graph n)
 (f : Fin m → Fin n) (s : List (Fin m)) :
 independent (inducedGraph G f) s = independent G (s.map f) := by
 simp [independent, inducedGraph, List.all_map, Function.comp_def]

/-- The actual proper-induced-minor U hypothesis supplied by minimality.
 No MU, LC, connectedness or special shape of the minor is assumed. -/
theorem critical_proper_induced_unimodal (w : CriticalWitness) (m : Nat)
 (hm : m<w.n) (f : Fin m → Fin w.n) (hinj : ∀ u v, f u=f v → u=v) :
 Unimodal (coefficient (inducedGraph w.graph f)) :=
 w.smallerForestUnimodal m hm (inducedGraph w.graph f)
   (inducedGraph_isForest w.graph w.forest f hinj)

/-- This is the exact graph size bound still needed to finish classification.
 It is a definition of an obligation, not an assumed theorem. -/
def CriticalSizeBound : Prop := ∀ w : CriticalWitness, w.n+2≤4*w.M

theorem classification_of_size_bound (hs : CriticalSizeBound) : CriticalClassification := by
 intro ht
 obtain ⟨w⟩ := critical_witness_of_not_target ht
 have hh := hs w
 by_cases he : w.n+2=4*w.M
 · exact Or.inl ⟨w,he⟩
 · exact Or.inr ⟨w,by omega⟩

theorem target_of_size_and_exclusions (hs : CriticalSizeBound)
 (h2 : Delta2Excluded) (hd : DeeperExcluded) : Target :=
 target_of_critical_children (classification_of_size_bound hs) h2 hd

end Erdos993.Extraction
