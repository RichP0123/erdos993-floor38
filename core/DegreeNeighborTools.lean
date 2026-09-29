import ActualSmallComponents
namespace Erdos993.NeighborTools
open Counting Structure

theorem degree_bound_by_list {n : Nat} (G : Graph n) (v : Fin n)
 (xs : List (Fin n)) (hx : xs.Nodup) (h : ∀u,G.adj v u=true → u∈xs) : degree G v≤xs.length := by
 have ht := sumBy_le (List.finRange n) (fun u => if G.adj v u then 1 else 0)
   (fun u => if u∈xs then 1 else 0) ?_
 · rw [sumBy_indicator,selected_membership_sum xs hx] at ht
   exact ht
 · intro u hu
   cases he : G.adj v u
   · simp [he]
   · simp [he,h u he]

theorem degree_three_neighbors {n : Nat} (G : Graph n) (v w : Fin n)
 (hw : G.adj v w=true) (hd : degree G v=3) :
 ∃a b,a≠b ∧ a≠w ∧ b≠w ∧ (∀u,G.adj v u=true ↔ u=w ∨ u=a ∨ u=b) := by
 let ns := (List.finRange n).filter (fun u => G.adj v u)
 have hnd : ns.Nodup := List.Sublist.nodup List.filter_sublist (finRange_nodup n)
 have hwm : w∈ns := by simp [ns,hw]
 have hlen : (ns.erase w).length=2 := by
   have he := List.length_erase_of_mem hwm
   change ns.length=3 at hd
   omega
 obtain ⟨a,b,he⟩ : ∃a b,ns.erase w=[a,b] := by
   cases hh : ns.erase w with
   | nil => simp [hh] at hlen
   | cons a us =>
     cases us with
     | nil => simp [hh] at hlen
     | cons b us =>
       have hz : us=[] := by cases us <;> simp_all
       exact ⟨a,b,by simp [hz]⟩
 have hn : (ns.erase w).Nodup := List.Sublist.nodup List.erase_sublist hnd
 have hnot := List.Nodup.not_mem_erase hnd (a:=w)
 rw [he] at hn hnot
 have hab : a≠b := by simpa using hn
 have haw : a≠w := by intro hh; subst a; simp at hnot
 have hbw : b≠w := by intro hh; subst b; simp at hnot
 refine ⟨a,b,hab,haw,hbw,?_⟩
 intro u
 constructor
 · intro hu
   by_cases huw : u=w
   · exact Or.inl huw
   · have hum : u∈ns.erase w := (List.Nodup.mem_erase_iff hnd).mpr ⟨huw,by simp [ns,hu]⟩
     rw [he] at hum
     exact Or.inr (by simpa using hum)
 · intro hu
   rcases hu with hu | hu | hu
   · subst u; exact hw
   · subst u
     have hm : a∈ns.erase w := by rw [he]; simp
     exact (List.mem_filter.mp (List.mem_of_mem_erase hm)).2
   · subst u
     have hm : b∈ns.erase w := by rw [he]; simp
     exact (List.mem_filter.mp (List.mem_of_mem_erase hm)).2

theorem forest_no_triangle {n : Nat} (G : Graph n) (hf : IsForest G)
 (a b c : Fin n) (hab : G.adj a b=true) (hbc : G.adj b c=true) (hac : a≠c) : G.adj a c=false := by
 have hneab : a≠b := by intro he; subst b; rw [G.loopless] at hab; contradiction
 have hnebc : b≠c := by intro he; subst c; rw [G.loopless] at hbc; contradiction
 let p := prependPath (singletonPath G c) b (by intro i; exact hnebc) hbc
 have hna : ∀i,a≠p.vertex i := by
   intro i
   exact Fin.cases hneab (fun _ => hac) i
 let q := prependPath p a hna hab
 exact path_no_endpoint_chord hf q ⟨2,by omega⟩ (by decide)

theorem degree_two_neighbors {n : Nat} (G : Graph n) (v a b : Fin n)
 (ha : G.adj v a=true) (hb : G.adj v b=true) (hab : a≠b) (hd : degree G v≤2) :
 ∀u,G.adj v u=true ↔ u=a ∨ u=b := by
 let ns := (List.finRange n).filter (fun u => G.adj v u)
 have hn : ns.Nodup := List.Sublist.nodup List.filter_sublist (finRange_nodup n)
 have ham : a∈ns := by simp [ns,ha]
 have hl : (ns.erase a).length≤1 := by
   have he := List.length_erase_of_mem ham
   change ns.length≤2 at hd
   omega
 have hbm : b∈ns.erase a := (List.Nodup.mem_erase_iff hn).mpr ⟨Ne.symm hab,by simp [ns,hb]⟩
 intro u
 constructor
 · intro hu
   by_cases hua : u=a
   · exact Or.inl hua
   · have hum : u∈ns.erase a := (List.Nodup.mem_erase_iff hn).mpr ⟨hua,by simp [ns,hu]⟩
     exact Or.inr (InteriorDegreeTwo.short_list_members_eq _ hl u b hum hbm)
 · intro hu
   rcases hu with hu | hu <;> subst u <;> assumption

end Erdos993.NeighborTools
