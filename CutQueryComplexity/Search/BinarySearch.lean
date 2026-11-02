import CutQueryComplexity.Search.Comp
import Mathlib.Data.Nat.Log

/-! # Question relabelling, batched questions, and monotone binary search

`Comp.mapQ` implements each question of a program by a single question of
another oracle, preserving outputs and costs. `Comp.askList` asks a public list
of questions. `findFirst` finds the first element of a list satisfying a
monotone test, using at most `c * (Nat.log 2 L.length + 1)` oracle calls when
each test costs at most `c`.
-/

namespace CutQueryComplexity
namespace Search
namespace Comp

variable {Q Q' A β γ : Type}

/-- Implement each question by one question of another oracle. -/
def mapQ (f : Q → Q') : Comp Q A β → Comp Q' A β
  | pure b => pure b
  | query q k => query (f q) fun a => mapQ f (k a)

theorem run_mapQ (o : Q' → A) (f : Q → Q') (c : Comp Q A β) :
    run o (mapQ f c) = run (o ∘ f) c := by
  induction c with
  | pure b => rfl
  | query q k ih => simp only [mapQ, run, ih, Function.comp_apply]

@[simp] theorem eval_mapQ (o : Q' → A) (f : Q → Q') (c : Comp Q A β) :
    (mapQ f c).eval o = c.eval (o ∘ f) := by simp [eval, run_mapQ]

@[simp] theorem cost_mapQ (o : Q' → A) (f : Q → Q') (c : Comp Q A β) :
    (mapQ f c).cost o = c.cost (o ∘ f) := by simp [cost, run_mapQ]

/-- Ask a public list of questions in order. -/
def askList : List Q → Comp Q A (List A)
  | [] => pure []
  | q :: qs => (ask q).bind fun a => (askList qs).map (a :: ·)

@[simp] theorem eval_askList (o : Q → A) : ∀ qs : List Q, (askList qs).eval o = qs.map o
  | [] => rfl
  | q :: qs => by simp [askList, eval_askList o qs]

@[simp] theorem cost_askList (o : Q → A) : ∀ qs : List Q, (askList qs).cost o = qs.length
  | [] => rfl
  | q :: qs => by simp [askList, cost_askList o qs]; omega

end Comp

open Comp

variable {Q A β : Type}

/-- The first element of `L` passing `test`, assuming tests are monotone along `L`. -/
def findFirst (test : β → Comp Q A Bool) (L : List β) : Comp Q A (Option β) :=
  if h : L = [] then Comp.pure none else
    have hm : L.length / 2 < L.length := by
      have : 0 < L.length := List.length_pos_iff.mpr h
      omega
    (test (L[L.length / 2]'hm)).bind fun b =>
      if b then
        (findFirst test (L.take (L.length / 2))).map fun o =>
          match o with
          | some y => some y
          | none => some (L[L.length / 2]'hm)
      else findFirst test (L.drop (L.length / 2 + 1))
termination_by L.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop]
  all_goals omega

theorem findFirst_nil (test : β → Comp Q A Bool) : findFirst test [] = Comp.pure none := by
  rw [findFirst]; simp

theorem findFirst_spec (o : Q → A) (test : β → Comp Q A Bool) (p : β → Prop) [DecidablePred p]
    (c : ℕ) :
    ∀ (n : ℕ) (L : List β), L.length ≤ n →
      (∀ x ∈ L, (test x).eval o = decide (p x) ∧ (test x).cost o ≤ c) →
      L.Pairwise (fun x y => p x → p y) →
      ((∀ x ∈ L, ¬ p x) → (findFirst test L).eval o = none) ∧
      (∀ x ∈ L, p x → ∃ L₁ y L₂, L = L₁ ++ y :: L₂ ∧ p y ∧ (∀ z ∈ L₁, ¬ p z) ∧
        (findFirst test L).eval o = some y) ∧
      (findFirst test L).cost o ≤ c * (Nat.log 2 L.length + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro L hn htest hmono
    by_cases hL : L = []
    · subst hL
      rw [findFirst]
      simp
    have hlen : 0 < L.length := List.length_pos_iff.mpr hL
    set m := L.length / 2 with hm_def
    have hm : m < L.length := by omega
    set x := L[m]'hm with hx_def
    have hsplit : L = L.take m ++ x :: L.drop (m + 1) := by
      conv_lhs => rw [← List.take_append_drop m L]
      rw [List.drop_eq_getElem_cons hm]
    have hxL : x ∈ L := List.getElem_mem hm
    obtain ⟨hxeval, hxcost⟩ := htest x hxL
    have htake : ∀ y ∈ L.take m, y ∈ L := fun y hy => List.mem_of_mem_take hy
    have hdrop : ∀ y ∈ L.drop (m + 1), y ∈ L := fun y hy => List.mem_of_mem_drop hy
    have hmono' := hsplit ▸ hmono
    rw [List.pairwise_append, List.pairwise_cons] at hmono'
    -- every element of the left half precedes `x`, every element of the right follows it
    have hleft : ∀ y ∈ L.take m, p y → p x := fun y hy => hmono'.2.2 y hy x (by simp)
    have hright : ∀ y ∈ L.drop (m + 1), p x → p y := fun y hy => hmono'.2.1.1 y hy
    have hlt : L.length / 2 < n := by omega
    have htakelen : (L.take m).length = m := by simp [List.length_take]; omega
    have hdroplen : (L.drop (m + 1)).length = L.length - (m + 1) := by simp
    have hlog : ∀ k, k ≤ L.length / 2 → 0 < k → Nat.log 2 k + 1 ≤ Nat.log 2 L.length := by
      intro k hk hk0
      have h1 : Nat.log 2 k ≤ Nat.log 2 (L.length / 2) := Nat.log_mono_right hk
      rw [Nat.log_div_base] at h1
      have h2 : 1 ≤ Nat.log 2 L.length :=
        Nat.le_log_of_pow_le (by decide) (by rw [Nat.pow_one]; omega)
      omega
    rw [findFirst, dite_eq_right_of_eq_false (eq_false hL)]
    simp only [eval_bind, cost_bind, ← hm_def, ← hx_def, hxeval]
    by_cases hpx : p x
    · simp only [hpx, decide_true, ↓reduceIte, eval_map, cost_map]
      obtain ⟨hnone, hsome, hcost⟩ := ih m (by omega) (L.take m) (by omega)
        (fun y hy => htest y (htake y hy)) (hmono'.1)
      refine ⟨fun hall => absurd hpx (hall x hxL), fun _ _ _ => ?_, ?_⟩
      · by_cases hex : ∃ y ∈ L.take m, p y
        · obtain ⟨y, hy, hpy⟩ := hex
          obtain ⟨L₁, z, L₂, heq, hpz, hL₁, hev⟩ := hsome y hy hpy
          refine ⟨L₁, z, L₂ ++ x :: L.drop (m + 1), hsplit.trans (by rw [heq]; simp), hpz, hL₁,
            by rw [hev]⟩
        · push Not at hex
          refine ⟨L.take m, x, L.drop (m + 1), hsplit, hpx, hex, ?_⟩
          rw [hnone hex]
      · have := hcost
        rw [htakelen] at this
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · have hnil : L.take m = [] := List.eq_nil_of_length_eq_zero (by omega)
          rw [hnil, findFirst_nil, cost_pure, Nat.add_zero]
          exact le_trans hxcost (Nat.le_mul_of_pos_right c (Nat.succ_pos _))
        · have h3 := hlog m le_rfl h0
          have h4 : c * (Nat.log 2 m + 1) + c ≤ c * (Nat.log 2 L.length + 1) := by
            rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left c (by omega)
          omega
    · simp only [hpx, decide_false, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨hnone, hsome, hcost⟩ := ih (L.length - (m + 1)) (by omega) (L.drop (m + 1))
        (by rw [hdroplen]) (fun y hy => htest y (hdrop y hy)) (hmono'.2.1.2)
      have hleftF : ∀ y ∈ L.take m, ¬ p y := fun y hy hpy => hpx (hleft y hy hpy)
      refine ⟨fun hall => hnone fun y hy => hall y (hdrop y hy), fun y hy hpy => ?_, ?_⟩
      · rw [hsplit] at hy
        rcases List.mem_append.mp hy with hy | hy
        · exact absurd hpy (hleftF y hy)
        · rcases List.mem_cons.mp hy with rfl | hy
          · exact absurd hpy hpx
          · obtain ⟨L₁, z, L₂, heq, hpz, hL₁, hev⟩ := hsome y hy hpy
            refine ⟨L.take m ++ x :: L₁, z, L₂, hsplit.trans (by rw [heq]; simp), hpz, ?_, hev⟩
            · intro w hw
              rcases List.mem_append.mp hw with hw | hw
              · exact hleftF w hw
              · rcases List.mem_cons.mp hw with rfl | hw
                · exact hpx
                · exact hL₁ w hw
      · rw [hdroplen] at hcost
        rcases Nat.eq_zero_or_pos (L.length - (m + 1)) with h0 | h0
        · have hnil : L.drop (m + 1) = [] := List.eq_nil_of_length_eq_zero (by omega)
          rw [hnil, findFirst_nil, cost_pure, Nat.add_zero]
          exact le_trans hxcost (Nat.le_mul_of_pos_right c (Nat.succ_pos _))
        · have h3 := hlog (L.length - (m + 1)) (by omega) h0
          have h4 : c * (Nat.log 2 (L.length - (m + 1)) + 1) + c ≤
              c * (Nat.log 2 L.length + 1) := by
            rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left c (by omega)
          omega

/-- The cost bound of `findFirst` needs no monotonicity or correctness assumption. -/
theorem findFirst_cost (o : Q → A) (test : β → Comp Q A Bool) (c : ℕ) :
    ∀ (n : ℕ) (L : List β), L.length ≤ n → (∀ x ∈ L, (test x).cost o ≤ c) →
      (findFirst test L).cost o ≤ c * (Nat.log 2 L.length + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro L hn htest
    by_cases hL : L = []
    · subst hL; rw [findFirst_nil]; simp
    have hlen : 0 < L.length := List.length_pos_iff.mpr hL
    have hm : L.length / 2 < L.length := by omega
    have hxcost := htest _ (List.getElem_mem hm)
    have hlog : ∀ k, k ≤ L.length / 2 → 0 < k → Nat.log 2 k + 1 ≤ Nat.log 2 L.length := by
      intro k hk hk0
      have h1 : Nat.log 2 k ≤ Nat.log 2 (L.length / 2) := Nat.log_mono_right hk
      rw [Nat.log_div_base] at h1
      have h2 : 1 ≤ Nat.log 2 L.length :=
        Nat.le_log_of_pow_le (by decide) (by rw [Nat.pow_one]; omega)
      omega
    have step : ∀ L' : List β, L'.length ≤ L.length / 2 → L'.length < n →
        (∀ x ∈ L', (test x).cost o ≤ c) →
        (test L[L.length / 2]).cost o + (findFirst test L').cost o ≤
          c * (Nat.log 2 L.length + 1) := by
      intro L' hL' hn' ht'
      rcases Nat.eq_zero_or_pos L'.length with h0 | h0
      · rw [List.eq_nil_of_length_eq_zero h0, findFirst_nil, cost_pure, Nat.add_zero]
        exact le_trans hxcost (Nat.le_mul_of_pos_right c (Nat.succ_pos _))
      · have h3 := hlog L'.length hL' h0
        have h4 : c * (Nat.log 2 L'.length + 1) + c ≤ c * (Nat.log 2 L.length + 1) := by
          rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left c (by omega)
        have := ih L'.length (by omega) L' le_rfl ht'
        omega
    rw [findFirst, dite_eq_right_of_eq_false (eq_false hL)]
    simp only [cost_bind]
    split
    · simp only [cost_map]
      exact step _ (by simp [List.length_take]) (by simp [List.length_take]; omega)
        fun x hx => htest x (List.mem_of_mem_take hx)
    · exact step _ (by simp; omega) (by simp; omega)
        fun x hx => htest x (List.mem_of_mem_drop hx)

end Search
end CutQueryComplexity
