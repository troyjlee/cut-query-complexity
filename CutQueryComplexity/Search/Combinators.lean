import CutQueryComplexity.Search.Comp
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! # List combinators for oracle computations

`mapList` runs a computation for every element of a public list and `tabulate`
records the results as a partial function. Costs add up.
-/

namespace CutQueryComplexity
namespace Search
namespace Comp

variable {Q A β γ : Type}

/-- Run `f` on each element in order. -/
def mapList (f : β → Comp Q A γ) : List β → Comp Q A (List γ)
  | [] => pure []
  | b :: bs => (f b).bind fun c => (mapList f bs).map (c :: ·)

@[simp] theorem eval_mapList (o : Q → A) (f : β → Comp Q A γ) :
    ∀ L : List β, (mapList f L).eval o = L.map fun b => (f b).eval o
  | [] => rfl
  | b :: bs => by simp [mapList, eval_mapList o f bs]

@[simp] theorem cost_mapList (o : Q → A) (f : β → Comp Q A γ) :
    ∀ L : List β, (mapList f L).cost o = (L.map fun b => (f b).cost o).sum
  | [] => rfl
  | b :: bs => by simp [mapList, cost_mapList o f bs]

theorem cost_mapList_le (o : Q → A) (f : β → Comp Q A γ) (L : List β) {c : ℕ}
    (h : ∀ b ∈ L, (f b).cost o ≤ c) : (mapList f L).cost o ≤ c * L.length := by
  rw [cost_mapList]
  induction L with
  | nil => simp
  | cons b bs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have h1 := h b (by simp)
      have h2 := ih fun x hx => h x (by simp [hx])
      rw [Nat.mul_succ]
      omega

/-- Run `f` on each element and record the results as a partial function. -/
def tabulate [DecidableEq β] (f : β → Comp Q A γ) : List β → Comp Q A (β → Option γ)
  | [] => pure fun _ => none
  | b :: bs => (f b).bind fun c => (tabulate f bs).map fun g v => if v = b then some c else g v

@[simp] theorem eval_tabulate [DecidableEq β] (o : Q → A) (f : β → Comp Q A γ) :
    ∀ (L : List β) (v : β),
      (tabulate f L).eval o v = if v ∈ L then some ((f v).eval o) else none
  | [], v => by simp [tabulate]
  | b :: bs, v => by
      simp only [tabulate, eval_bind, eval_map, List.mem_cons, eval_tabulate o f bs]
      by_cases hv : v = b
      · subst hv; simp
      · simp [hv]

@[simp] theorem cost_tabulate [DecidableEq β] (o : Q → A) (f : β → Comp Q A γ) :
    ∀ L : List β, (tabulate f L).cost o = (L.map fun b => (f b).cost o).sum
  | [] => rfl
  | b :: bs => by simp [tabulate, cost_tabulate o f bs]

theorem cost_tabulate_le [DecidableEq β] (o : Q → A) (f : β → Comp Q A γ) (L : List β)
    {c : ℕ} (h : ∀ b ∈ L, (f b).cost o ≤ c) : (tabulate f L).cost o ≤ c * L.length := by
  have := cost_mapList_le o f L h
  rwa [cost_mapList, ← cost_tabulate] at this

end Comp
end Search
end CutQueryComplexity
