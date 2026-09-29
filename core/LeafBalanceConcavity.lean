import LeafBalanceActual

namespace Erdos993.LeafBalanceConcavity
open BinomialKernel Counting LeafBalanceKernel
set_option maxHeartbeats 4000000

/-- Denominator-cleared exact central second-difference identity. -/
theorem central_identity (e i : Nat) :
 ((i:Int)+2)*((e:Int)-i)*
   ((binom e (i+2):Int)-2*(binom e (i+1):Int)+(binom e i:Int))=
 (((e:Int)-2*((i:Int)+1))^2-((e:Int)+2))*(binom e (i+1):Int) := by
 have h0 := congrArg (fun n : Nat => (n:Int)) (balance e i)
 have h1 := congrArg (fun n : Nat => (n:Int)) (balance e (i+1))
 simp only [Int.natCast_add,Int.natCast_mul,Int.natCast_one] at h0 h1
 have he : i+1+1=i+2 := by omega
 rw [he] at h1
 grind

theorem central_concave (e i : Nat)
 (h : ((e:Int)-2*((i:Int)+1))^2≤(e:Int)+2) :
 binom e (i+2)+binom e i≤2*binom e (i+1) := by
 by_cases hi : i<e
 · have he := central_identity e i
   have hn : (0:Int)≤binom e (i+1) := by omega
   have hm := Int.mul_le_mul_of_nonneg_right h hn
   have hp : (0:Int)<((i:Int)+2)*((e:Int)-i) := by
     apply Int.mul_pos <;> omega
   have hh : ((binom e (i+2):Int)-2*(binom e (i+1):Int)+(binom e i:Int))≤0 := by
     by_cases hh : ((binom e (i+2):Int)-2*(binom e (i+1):Int)+(binom e i:Int))≤0
     · exact hh
     · have ht := Int.mul_pos hp (show (0:Int)<(binom e (i+2):Int)-2*(binom e (i+1):Int)+(binom e i:Int) by omega)
       grind
   omega
 · have he : (e:Int)+2≤2*((i:Int)+1)-e := by omega
   have hn : (0:Int)≤2*((i:Int)+1)-e := by omega
   have h1 := Int.mul_le_mul_of_nonneg_right he hn
   have h2 := Int.mul_le_mul_of_nonneg_left he (show (0:Int)≤(e:Int)+2 by omega)
   have h3 : (e:Int)+2<((e:Int)+2)*((e:Int)+2) := by
     have hm := Int.mul_le_mul_of_nonneg_right (show (2:Int)≤(e:Int)+2 by omega)
       (show (0:Int)≤(e:Int)+2 by omega)
     omega
   have hx : ((e:Int)-2*((i:Int)+1))^2=(2*((i:Int)+1)-e)*(2*((i:Int)+1)-e) := by grind
   rw [hx] at h
   omega

/-- General finite-sequence closure: the undecided departure interval is
 nonincreasing, with an ascending prefix and descending suffix. -/
theorem interval_no_return (a : Nat → Nat) (lo hi : Nat)
 (ascend : ∀ r, r<lo → a r≤a (r+1))
 (suffix : ∀ r, hi≤r → a (r+1)≤a r)
 (concave : ∀ r, lo≤r → r+1<hi → a (r+2)+a r≤2*a (r+1)) :
 Foundation.NoRecovery a := by
 intro M b hb fall
 have hlo : lo≤M := by
   by_cases hh : M<lo
   · have := ascend M hh; omega
   · omega
 by_cases hhi : hi≤b
 · exact suffix b hhi
 · have step : ∀ d, M+d<hi → a (M+d+1)<a (M+d) := by
     intro d
     induction d with
     | zero => intro hh; simpa using fall
     | succ d ih =>
       intro hh
       have h0 := ih (by omega)
       have h1 := concave (M+d) (by omega) (by omega)
       have he0 : M+(d+1)=M+d+1 := by omega
       have he1 : M+(d+1)+1=M+d+2 := by omega
       rw [he1,he0]
       omega
   have h := step (b-M) (by omega)
   have he : M+(b-M)=b := by omega
   rw [he] at h
   omega

theorem outside_impossible (e : Nat) (t : Int) (ht : (e:Int)+2≤t)
 (hs : t^2≤(e:Int)+2) : False := by
 have hn : 0≤t := by omega
 have h1 := Int.mul_le_mul_of_nonneg_right ht hn
 have h2 := Int.mul_le_mul_of_nonneg_left ht (show (0:Int)≤(e:Int)+2 by omega)
 have hm := Int.mul_le_mul_of_nonneg_right (show (2:Int)≤(e:Int)+2 by omega)
   (show (0:Int)≤(e:Int)+2 by omega)
 have he : t^2=t*t := by grind
 rw [he] at hs
 omega

theorem atom_concave (k e r : Nat)
 (h : (2*(k:Int)+(e:Int)-2*((r:Int)+1))^2≤(e:Int)+2) :
 atom k e (r+2)+atom k e r≤2*atom k e (r+1) := by
 by_cases hk : k≤r
 · have h1 : k≤r+1 := by omega
   have h2 : k≤r+2 := by omega
   have e1 : r+1-k=(r-k)+1 := by omega
   have e2 : r+2-k=(r-k)+2 := by omega
   have cast : ((r-k:Nat):Int)=(r:Int)-k := by omega
   have he : (e:Int)-2*(((r-k:Nat):Int)+1)=2*(k:Int)+(e:Int)-2*((r:Int)+1) := by omega
   have hc := central_concave e (r-k) (by rw [he]; exact h)
   simpa only [atom,hk,h1,h2,if_true,e1,e2] using hc
 · by_cases he : k=r+1
   · subst k
     have hd : 2*((r+1:Nat):Int)+(e:Int)-2*((r:Int)+1)=(e:Int) := by omega
     rw [hd] at h
     have he2 : e≤2 := by
       by_cases hn : e≤2
       · exact hn
       · have hm := Int.mul_le_mul_of_nonneg_right (show (3:Int)≤(e:Int) by omega)
           (show (0:Int)≤(e:Int) by omega)
         have hh : (e:Int)^2=(e:Int)*(e:Int) := by grind
         rw [hh] at h
         omega
     have hk2 : r+1≤r+2 := by omega
     have es : r+2-(r+1)=1 := by omega
     simp only [atom,hk,if_false,hk2,if_true,Nat.le_refl,Nat.sub_self,es,
       zero_rank,first_rank,Nat.add_zero,Nat.mul_one]
     exact he2
   · have ht : (e:Int)+2≤2*(k:Int)+(e:Int)-2*((r:Int)+1) := by omega
     exact False.elim (outside_impossible e _ ht h)

theorem mixture_concave (xs : List (Nat × Nat)) (r : Nat)
 (h : ∀ p∈xs, (2*(p.1:Int)+(p.2:Int)-2*((r:Int)+1))^2≤(p.2:Int)+2) :
 mixture xs (r+2)+mixture xs r≤2*mixture xs (r+1) := by
 induction xs with
 | nil => simp [mixture]
 | cons p xs ih =>
   have h1 := atom_concave p.1 p.2 r (h p (by simp))
   have h2 := ih (by intro q hq; exact h q (by simp [hq]))
   simp only [mixture,sumBy_cons] at *
   omega

/-- Uniform central-concavity criterion for mixtures, using a lower bound
 on every binomial exponent. -/
theorem budget_no_return (xs : List (Nat × Nat)) (lo hi tau : Nat)
 (lower : ∀ p∈xs, lo≤2*p.1+p.2)
 (upper : ∀ p∈xs, 2*p.1+p.2≤hi)
 (exponent : ∀ p∈xs, tau≤p.2)
 (budget : ((hi:Int)-(lo:Int)-2)^2≤(tau:Int)+2) :
 Foundation.NoRecovery (mixture xs) := by
 apply interval_no_return (mixture xs) ((lo+1)/2) (hi/2)
 · intro r hr
   exact mixture_rising xs lo r lower (by omega)
 · intro r hr
   exact mixture_falling xs hi r upper (by omega)
 · intro r hr hs
   apply mixture_concave xs r
   intro p hp
   have hl := lower p hp
   have hu := upper p hp
   have ht := exponent p hp
   have hlr : (lo:Int)+2≤2*((r:Int)+1) := by omega
   have hur : 2*((r:Int)+1)≤(hi:Int)-2 := by omega
   let d : Int := (hi:Int)-(lo:Int)-2
   let t : Int := 2*(p.1:Int)+(p.2:Int)-2*((r:Int)+1)
   have h1 : 0≤d-t := by dsimp [d,t]; omega
   have h2 : 0≤d+t := by dsimp [d,t]; omega
   have hm := Int.mul_nonneg h1 h2
   have hsq : t^2≤d^2 := by grind
   have hbd : d^2≤(p.2:Int)+2 := by dsimp [d]; omega
   exact Int.le_trans hsq hbd

theorem actual_budget_unimodal {n : Nat} (G : Graph n) (core ls : List (Fin n))
 (partition : (core++ls).Perm (List.finRange n))
 (hl : ∀ u∈ls, ∀ v∈ls, G.adj u v=false) (lo hi tau : Nat)
 (lower : ∀ s∈subsets core, independent G s=true →
   lo≤2*s.length+(LeafBalanceActual.free G s ls).length)
 (upper : ∀ s∈subsets core, independent G s=true →
   2*s.length+(LeafBalanceActual.free G s ls).length≤hi)
 (exponent : ∀ s∈subsets core, independent G s=true →
   tau≤(LeafBalanceActual.free G s ls).length)
 (budget : ((hi:Int)-(lo:Int)-2)^2≤(tau:Int)+2) :
 Unimodal (coefficient G) := by
 apply (Foundation.graph_unimodal_iff_noRecovery G).mpr
 rw [LeafBalanceActual.expansion G core ls partition hl]
 apply budget_no_return (LeafBalanceActual.terms G core ls) lo hi tau _ _ _ budget
 · intro p hp
   obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hp
   exact lower s (List.mem_filter.mp hs).1 (List.mem_filter.mp hs).2
 · intro p hp
   obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hp
   exact upper s (List.mem_filter.mp hs).1 (List.mem_filter.mp hs).2
 · intro p hp
   obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hp
   exact exponent s (List.mem_filter.mp hs).1 (List.mem_filter.mp hs).2

/-- An actual first-fall/return witness must violate the central budget.
 This does not assert any upper bound on leaf defect or graph order. -/
theorem actual_return_budget_obstruction {n : Nat} (G : Graph n) (core ls : List (Fin n))
 (partition : (core++ls).Perm (List.finRange n))
 (hl : ∀ u∈ls, ∀ v∈ls, G.adj u v=false) (lo hi tau M b : Nat)
 (lower : ∀ s∈subsets core, independent G s=true →
   lo≤2*s.length+(LeafBalanceActual.free G s ls).length)
 (upper : ∀ s∈subsets core, independent G s=true →
   2*s.length+(LeafBalanceActual.free G s ls).length≤hi)
 (exponent : ∀ s∈subsets core, independent G s=true →
   tau≤(LeafBalanceActual.free G s ls).length)
 (hb : M<b) (fall : coefficient G (M+1)<coefficient G M)
 (rise : coefficient G b<coefficient G (b+1)) :
 lo+2*(b-M+1)≤hi ∧ (tau:Int)+3≤((hi:Int)-(lo:Int)-2)^2 := by
 refine ⟨LeafBalanceActual.actual_return_spread G core ls partition hl lo hi M b
   lower upper hb fall rise,?_⟩
 by_cases h : ((hi:Int)-(lo:Int)-2)^2≤(tau:Int)+2
 · have hu := actual_budget_unimodal G core ls partition hl lo hi tau lower upper exponent h
   have ht := Foundation.noRecovery_of_unimodal _ hu M b hb fall
   omega
 · omega

end Erdos993.LeafBalanceConcavity
