import PrefixDegreeSums
namespace Erdos993.PrefixPairDensity
open Counting Structure PrefixRootBudget PrefixCenterPairs PrefixDegreeSums
set_option maxHeartbeats 8000000

def low {n : Nat} (G : Graph n) (v : Fin n) : Bool := decide (degree G v≤3)
def high {n : Nat} (G : Graph n) (v : Fin n) : Bool := !(low G v)
def lowDegree {n : Nat} (G : Graph n) : Fin n → Nat := degreeIn G (low G)
def highDegree {n : Nat} (G : Graph n) : Fin n → Nat := degreeIn G (high G)
def small {n : Nat} (G : Graph n) (v : Fin n) : Bool :=
 decide (degree G v≤1 ∧ ∀u,G.adj v u=true → degree G u≤1)
def internalLow {n : Nat} (G : Graph n) (v : Fin n) : Bool :=
 low G v && decide (2≤lowDegree G v)
def thinLow {n : Nat} (G : Graph n) (v : Fin n) : Bool :=
 low G v && decide (lowDegree G v≤1)

theorem lowDegree_length {n : Nat} (G : Graph n) (v : Fin n) :
 lowDegree G v=(lowNeighbors G v).length := by
 exact sumBy_indicator _ _

theorem degree_parts {n : Nat} (G : Graph n) (v : Fin n) :
 lowDegree G v+highDegree G v=degree G v := degree_split G (low G) v

theorem low_bound {n : Nat} (G : Graph n) (v : Fin n) (hv : low G v=true) :
 lowDegree G v≤3 := by
 have hd : degree G v≤3 := by simpa [low] using hv
 have hh := degree_parts G v
 omega

theorem high_density {n : Nat} (G : Graph n) (hf : IsForest G) :
 2*count (high G)≤mass (high G) (lowDegree G) ∧
 count (high G)≤2*mass (high G) (fun v => lowDegree G v/2) := by
 have hd := mass_le (high G) (fun _ => 4) (degree G) (by
   intro v hv
   have hh : ¬degree G v≤3 := by simpa [high,low] using hv
   dsimp only
   omega)
 have he : mass (high G) (degree G)=
   mass (high G) (lowDegree G)+mass (high G) (highDegree G) := by
   rw [←mass_add]
   apply sumBy_congr
   intro v hv
   dsimp only
   rw [degree_parts]
 have hi := forest_internal_degree G hf (high G)
 have hc : mass (high G) (fun _ => 4)=4*count (high G) :=
   mass_mul (high G) (fun _ => 1) 4
 rw [he,hc] at hd
 change mass (high G) (highDegree G)≤2*count (high G) at hi
 have hb := mass_le (high G) (lowDegree G) (fun v => 2*(lowDegree G v/2)+1)
   (by intro v hv; dsimp only; omega)
 rw [mass_add,mass_mul] at hb
 change mass (high G) (lowDegree G)≤
   2*mass (high G) (fun v => lowDegree G v/2)+count (high G) at hb
 omega

theorem internalLow_count {n : Nat} (G : Graph n) :
 count (internalLow G)=mass (low G) (fun v => lowDegree G v/2) := by
 apply sumBy_congr
 intro v hv
 dsimp only [internalLow]
 by_cases hl : low G v=true
 · have hb := low_bound G v hl
   simp only [hl,Bool.true_and,if_true]
   by_cases ht : 2≤lowDegree G v <;> simp [ht] <;> omega
 · simp [hl]

theorem small_is_low {n : Nat} (G : Graph n) (v : Fin n) (hs : small G v=true) :
 low G v=true := by
 have hh : degree G v≤1 := ((of_decide_eq_true hs)).1
 simp only [low,decide_eq_true_eq]
 omega

/-- A local charging inequality, with no component enumeration. -/
theorem low_charge {n : Nat} (G : Graph n) (v : Fin n) (hv : low G v=true) :
 1≤(if small G v then 1 else 0)+(if internalLow G v then 1 else 0)+
   degreeIn G (internalLow G) v+highDegree G v+
   neighborWeight G (thinLow G) (highDegree G) v := by
 by_cases hs : small G v=true
 · simp only [hs,if_true]; omega
 by_cases ht : 2≤lowDegree G v
 · have hi : internalLow G v=true := by simp [internalLow,hv,ht]
   simp only [hi,if_true]; omega
 have ht' : lowDegree G v≤1 := by omega
 by_cases hh : 1≤highDegree G v
 · omega
 have hh' : highDegree G v=0 := by omega
 have hd : degree G v≤1 := by have h := degree_parts G v; omega
 have hn : ∃u,G.adj v u=true ∧ 2≤degree G u := by
   by_cases he : ∀u,G.adj v u=true → degree G u≤1
   · have he' : small G v=true := by exact decide_eq_true ⟨hd,he⟩
     exact False.elim (hs he')
   · classical
     grind only
 obtain ⟨u,ha,hu⟩ := hn
 have hlu : low G u=true := by
   by_cases hl : low G u=true
   · exact hl
   · have hp : high G u=true := by simp [high,hl]
     have hp' := degreeIn_adj_positive G (high G) v u ha hp
     change 1≤highDegree G v at hp'
     omega
 by_cases hu2 : 2≤lowDegree G u
 · have hi : internalLow G u=true := by simp [internalLow,hlu,hu2]
   have hh := degreeIn_adj_positive G (internalLow G) v u ha hi
   omega
 · have hu1 : lowDegree G u≤1 := by omega
   have hi : thinLow G u=true := by simp [thinLow,hlu,hu1]
   have hp := neighborWeight_member_le G (thinLow G) (highDegree G) v u ha hi
   have hd := degree_parts G u
   omega

theorem mass_indicator_subset {n : Nat} (p q : Fin n → Bool)
 (h : ∀v,q v=true → p v=true) :
 mass p (fun v => if q v then 1 else 0)=count q := by
 apply sumBy_congr
 intro v hv
 dsimp only
 by_cases hq : q v=true
 · simp [hq,h v hq]
 · simp [hq]

theorem low_population {n : Nat} (G : Graph n) :
 count (low G)≤count (small G)+4*count (internalLow G)+
   2*mass (high G) (lowDegree G) := by
 have h := mass_le (low G) (fun _ => 1)
   (fun v => (if small G v then 1 else 0)+(if internalLow G v then 1 else 0)+
     degreeIn G (internalLow G) v+highDegree G v+
     neighborWeight G (thinLow G) (highDegree G) v)
   (by intro v hv; exact low_charge G v hv)
 have hs := mass_indicator_subset (low G) (small G) (small_is_low G)
 have hi := mass_indicator_subset (low G) (internalLow G)
   (by
     intro v hv
     have h : low G v=true ∧ 2≤lowDegree G v := by simpa [internalLow] using hv
     exact h.1)
 have hd := mass_degree_swap G (low G) (internalLow G)
 have hd' := mass_le (internalLow G) (lowDegree G) (fun _ => 3)
   (by
     intro v hv
     have h : low G v=true ∧ 2≤lowDegree G v := by simpa [internalLow] using hv
     exact low_bound G v h.1)
 have hc : mass (internalLow G) (fun _ => 3)=3*count (internalLow G) :=
   mass_mul (internalLow G) (fun _ => 1) 3
 rw [hc] at hd'
 change mass (low G) (degreeIn G (internalLow G))=mass (internalLow G) (lowDegree G) at hd
 have he : mass (low G) (highDegree G)=mass (high G) (lowDegree G) :=
   mass_degree_swap G (low G) (high G)
 have ht := weighted_degree_swap G (low G) (thinLow G) (highDegree G)
 have ht' : mass (thinLow G) (fun u => lowDegree G u*highDegree G u)≤
   mass (low G) (highDegree G) := by
   apply sumBy_le
   intro v hv
   dsimp only
   by_cases hthin : thinLow G v=true
   · have hh : low G v=true ∧ lowDegree G v≤1 := by simpa [thinLow] using hthin
     obtain ⟨hl,hb⟩ := hh
     simp only [hthin,hl,if_true]
     exact Nat.le_trans (Nat.mul_le_mul_right (highDegree G v) hb) (by omega)
   · simp [hthin]
 change mass (low G) (neighborWeight G (thinLow G) (highDegree G))=
   mass (thinLow G) (fun u => lowDegree G u*highDegree G u) at ht
 rw [mass_add,mass_add,mass_add,mass_add,hs,hi,hd,he,ht] at h
 change count (low G)≤_ at h
 omega

/-- The G04 density bound, on every finite forest, including spectators. -/
theorem forest_pair_density {n : Nat} (G : Graph n) (hf : IsForest G) :
 n≤count (small G)+10*pairBudget G := by
 have hh := high_density G hf
 have hl := low_population G
 have hn := count_complement (low G)
 change count (low G)+count (high G)=n at hn
 rw [internalLow_count] at hl
 have he := mass_le (high G) (lowDegree G) (fun v => 2*(lowDegree G v/2)+1)
   (by intro v hv; dsimp only; omega)
 rw [mass_add,mass_mul] at he
 change mass (high G) (lowDegree G)≤
   2*mass (high G) (fun v => lowDegree G v/2)+count (high G) at he
 have hw := mass_complement (low G) (fun v => lowDegree G v/2)
 have hw' : sumBy (List.finRange n) (fun v => lowDegree G v/2)=pairBudget G := by
   exact sumBy_congr _ _ _ (by intro v hv; rw [lowDegree_length])
 rw [hw'] at hw
 change mass (low G) (fun v => lowDegree G v/2)+
   mass (high G) (fun v => lowDegree G v/2)=pairBudget G at hw
 omega

end Erdos993.PrefixPairDensity
