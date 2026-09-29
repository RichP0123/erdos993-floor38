import PrefixLocalCounting
namespace Erdos993.PrefixSubsetTotals
open Counting Structure PrefixRootBudget PrefixLocalCounting
set_option maxHeartbeats 8000000

def totalCount {α : Type} (P : List α → Bool) (xs : List α) : Nat :=
 sumBy (subsets xs) (fun s => if P s then 1 else 0)

theorem totalCount_cons {α : Type} (P : List α → Bool) (a : α) (xs : List α) :
 totalCount P (a::xs)=totalCount P xs+totalCount (fun s => P (a::s)) xs := by
 simp [totalCount,subsets,sumBy_append,sumBy_map]

theorem totalCount_false {α : Type} (xs : List α) : totalCount (fun _ => false) xs=0 := by
 simp [totalCount]

theorem totalCount_perm {α : Type} {xs ys : List α} (h : xs.Perm ys)
 (P : List α → Bool) (hP : PermInvariant P) : totalCount P xs=totalCount P ys := by
 induction h generalizing P with
 | nil => rfl
 | cons a h ih => rw [totalCount_cons,totalCount_cons,ih P hP,ih _ (permInvariant_cons P hP a)]
 | swap a b xs =>
   simp only [totalCount_cons]
   have he : (fun s => P (b::a::s))=(fun s => P (a::b::s)) := by
     funext s; exact hP _ _ (List.Perm.swap a b s)
   rw [he]
   omega
 | trans h1 h2 ih1 ih2 => exact (ih1 P hP).trans (ih2 P hP)

theorem totalCount_restrict {α : Type} (P : List α → Bool) (xs : List α)
 (p : α → Bool) : totalCount (fun s => P s && s.all p) xs=totalCount P (xs.filter p) := by
 induction xs generalizing P with
 | nil => simp [totalCount,subsets]
 | cons a xs ih =>
   rw [totalCount_cons]
   cases hp : p a
   · simp only [List.all_cons,hp,Bool.false_and,Bool.and_false,totalCount_false,Nat.add_zero]
     rw [ih P]
     simp [hp]
   · simp only [List.all_cons,hp,Bool.true_and]
     rw [ih P,ih (fun s => P (a::s))]
     simp [hp,totalCount_cons]

theorem subsets_length {α : Type} (xs : List α) : (subsets xs).length=2^xs.length := by
 induction xs with
 | nil => simp [subsets]
 | cons a xs ih => simp [subsets,ih,Nat.pow_succ]; omega

theorem totalCount_upper {α : Type} (P : List α → Bool) (xs : List α) :
 totalCount P xs≤2^xs.length := by
 have h := sumBy_le (subsets xs) (fun s => if P s then 1 else 0) (fun _ => 1)
   (by intro s hs; dsimp; split <;> omega)
 simpa [totalCount,sumBy_const,subsets_length] using h

theorem totalCount_graph_cons {n : Nat} (G : Graph n) (a : Fin n) (xs : List (Fin n)) :
 totalCount (independent G) (a::xs)=totalCount (independent G) xs+
   totalCount (independent G) (xs.filter (fun v => !(G.adj a v))) := by
 rw [totalCount_cons]
 have he : (fun s => independent G (a::s))=
   (fun s => independent G s && s.all (fun v => !(G.adj a v))) := by
   funext s; exact independent_cons_bool G a s
 rw [he,totalCount_restrict]

theorem totalCount_high_decomposition {n : Nat} (G : Graph n) (xs : List (Fin n)) :
 totalCount (independent G) xs=1+xs.length+higherSubsets G xs := by
 have he := graded_partition_sum G xs 1 1 1
 have hfun : (fun s : List (Fin n) => if independent G s then
   (if s.length=0 then 1 else if s.length=1 then 1 else 1) else 0)=
   (fun s => if independent G s then 1 else 0) := by
   funext s; simp
 rw [hfun] at he
 simpa [totalCount] using he

theorem two_vertex_total {n : Nat} (G : Graph n) (u w : Fin n) (ys : List (Fin n))
 (hn : G.adj u w=false) :
 totalCount (independent G) (u::w::ys)=totalCount (independent G) ys+
   totalCount (independent G) (ys.filter (fun v => !(G.adj w v)))+
   totalCount (independent G) (ys.filter (fun v => !(G.adj u v)))+
   totalCount (independent G) (ys.filter (fun v => !(G.adj u v) && !(G.adj w v))) := by
 rw [totalCount_graph_cons,totalCount_graph_cons]
 simp only [List.filter_cons,hn,Bool.not_false,if_true]
 rw [totalCount_graph_cons]
 have he : ((ys.filter (fun v => !(G.adj u v))).filter (fun v => !(G.adj w v)))=
   ys.filter (fun v => !(G.adj u v) && !(G.adj w v)) := by
   rw [List.filter_filter]
   apply List.filter_congr
   intro v hv
   cases G.adj u v <;> cases G.adj w v <;> rfl
 rw [he]
 omega

end Erdos993.PrefixSubsetTotals
