import CutQueryComplexity.Discovery.Normalization

/-! # Relative-heavy row search (Lemma 3)

`explore thr W m` searches a group `W` of a nonnegative vector `x` whose mass `m` is
known, using an oracle for the mass of any set. A group is split only when its mass
exceeds `thr`. `explore_spec` shows that it returns exactly the entries above `thr`,
with their values, and that `thr * cost ≤ m * ⌈log₂ |W|⌉`. With `thr = M / b` this
is at most `b ⌈log₂ |W|⌉` mass queries.

`implement` replaces each question of a program by a subprogram. `rowMass` evaluates
the mass of a set in the row of `v` of the residual graph `G - K`, for an explicit
`K ≤ G`, with two cut queries via `2 w_R(v, X) = r_v + c_R(X) - c_R(X ∪ {v})`.
`residualRow_spec` is Lemma 3 for a residual row: all residual edges at `v` heavier
than `r_v / b` are found, with exact weights, using at most
`2 b ⌈log₂ (N - 1)⌉` cut queries to `G`.
-/

namespace CutQueryComplexity
namespace Discovery

open Search Search.Comp WeightedGraph Finset

section Implement

variable {Q Q' A A' β : Type}

/-- Implement each question of a program by a subprogram of another oracle. -/
def implement (impl : Q → Comp Q' A' A) : Comp Q A β → Comp Q' A' β
  | .pure b => .pure b
  | .query q k => (impl q).bind fun a => implement impl (k a)

theorem eval_implement (impl : Q → Comp Q' A' A) (o : Q' → A') (o' : Q → A)
    (h : ∀ q, (impl q).eval o = o' q) (c : Comp Q A β) :
    (implement impl c).eval o = c.eval o' := by
  induction c with
  | pure b => rfl
  | query q k ih => simp [implement, h, ih]

theorem cost_implement (impl : Q → Comp Q' A' A) (o : Q' → A') (o' : Q → A)
    (h : ∀ q, (impl q).eval o = o' q) {m : ℕ} (hm : ∀ q, (impl q).cost o ≤ m)
    (c : Comp Q A β) : (implement impl c).cost o ≤ m * c.cost o' := by
  induction c with
  | pure b => simp [implement]
  | query q k ih =>
      simp only [implement, cost_bind, h, cost_query, Nat.mul_succ]
      have := hm q
      have := ih (o' q)
      omega

end Implement

variable {V : Type} [Fintype V] [DecidableEq V]

section Explore

/-- Search the group `W` of known mass `m` for the entries above `thr`, returned as a
function supported on them. -/
noncomputable def explore (thr : ℝ) (W : List V) (m : ℝ) : Comp (Finset V) ℝ (V → ℝ) :=
  if m ≤ thr then Comp.pure 0 else
  if W.length ≤ 1 then Comp.pure fun u => if u ∈ W then m else 0 else
    (ask (W.take (W.length / 2)).toFinset).bind fun a =>
      (explore thr (W.take (W.length / 2)) a).bind fun f₁ =>
        (explore thr (W.drop (W.length / 2)) (m - a)).map fun f₂ => f₁ + f₂
termination_by W.length
decreasing_by all_goals simp only [List.length_take, List.length_drop]; omega

omit [Fintype V] in
/-- Lemma 3, abstract form: for a nonnegative vector `x` and a subset-sum oracle,
`explore` returns exactly the entries of `W` exceeding `thr`, and
`thr * cost ≤ m * ⌈log₂ |W|⌉`. -/
theorem explore_spec (x : V → ℝ) (hx : ∀ u, 0 ≤ x u) (thr : ℝ) :
    ∀ (n : ℕ) (W : List V) (m : ℝ), W.length ≤ n → W.Nodup →
      m = ∑ u ∈ W.toFinset, x u →
      (explore thr W m).eval (fun S => ∑ u ∈ S, x u) =
          (fun u => if u ∈ W ∧ thr < x u then x u else 0) ∧
        thr * (explore thr W m).cost (fun S => ∑ u ∈ S, x u) ≤
          m * Nat.clog 2 W.length := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W m hn hnd hm
    have hm0 : 0 ≤ m := hm ▸ Finset.sum_nonneg fun u _ => hx u
    rw [explore]
    by_cases hthr : m ≤ thr
    · simp only [hthr, ↓reduceIte, eval_pure, cost_pure, CharP.cast_eq_zero, mul_zero]
      refine ⟨funext fun u => ?_, by positivity⟩
      have : u ∈ W → x u ≤ thr := fun hu => by
        have := Finset.single_le_sum (fun y _ => hx y) (List.mem_toFinset.mpr hu)
        linarith
      by_cases hu : u ∈ W
      · simp [hu, (this hu).not_gt]
      · simp [hu]
    simp only [hthr, ↓reduceIte]
    by_cases hW : W.length ≤ 1
    · simp only [hW, ↓reduceIte, eval_pure, cost_pure, CharP.cast_eq_zero, mul_zero]
      refine ⟨funext fun u => ?_, by positivity⟩
      match W, hW with
      | [], _ => simp
      | [w], _ =>
          simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
            sum_singleton] at hm
          subst hm
          by_cases hu : u = w
          · subst hu; simp [lt_of_not_ge hthr]
          · simp [hu]
    simp only [hW, ↓reduceIte, eval_bind, cost_bind, eval_ask, cost_ask, eval_map, cost_map]
    set L := W.length
    set W₁ := W.take (L / 2)
    set W₂ := W.drop (L / 2)
    have hl₁ : W₁.length = L / 2 := by simp only [W₁, List.length_take, L]; omega
    have hl₂ : W₂.length = L - L / 2 := by simp only [W₂, List.length_drop, L]
    have hsplit : W = W₁ ++ W₂ := (List.take_append_drop _ _).symm
    have hnd' := hsplit ▸ hnd
    rw [List.nodup_append] at hnd'
    have hdisj : Disjoint W₁.toFinset W₂.toFinset :=
      List.disjoint_toFinset_iff_disjoint.mpr fun a h₁ h₂ => hnd'.2.2 a h₁ a h₂ rfl
    set a := ∑ u ∈ W₁.toFinset, x u
    have ha : m - a = ∑ u ∈ W₂.toFinset, x u := by
      rw [hm, hsplit, List.toFinset_append, Finset.sum_union hdisj]; ring
    obtain ⟨he₁, hc₁⟩ := ih (L / 2) (by omega) W₁ a (by omega) hnd'.1 rfl
    obtain ⟨he₂, hc₂⟩ := ih (L - L / 2) (by omega) W₂ (m - a) (by omega) hnd'.2.1 ha
    have ha0 : 0 ≤ a := Finset.sum_nonneg fun u _ => hx u
    have ha1 : 0 ≤ m - a := ha ▸ Finset.sum_nonneg fun u _ => hx u
    refine ⟨?_, ?_⟩
    · rw [he₁, he₂]
      funext u
      simp only [Pi.add_apply]
      by_cases hu₁ : u ∈ W₁
      · have hu₂ : u ∉ W₂ := fun h => hnd'.2.2 u hu₁ u h rfl
        have hu : u ∈ W := hsplit ▸ List.mem_append_left _ hu₁
        simp [hu₁, hu₂, hu]
      · by_cases hu₂ : u ∈ W₂
        · have hu : u ∈ W := hsplit ▸ List.mem_append_right _ hu₂
          simp [hu₁, hu₂, hu]
        · have hu : u ∉ W := fun h => by
            rw [hsplit, List.mem_append] at h; tauto
          simp [hu₁, hu₂, hu]
    · have hD₁ := clog_half_succ_le (L := L) (l := W₁.length) (by omega) (by omega)
      have hD₂ := clog_half_succ_le (L := L) (l := W₂.length) (by omega) (by omega)
      have hD₁' : ((Nat.clog 2 W₁.length : ℕ) : ℝ) ≤ (Nat.clog 2 L : ℝ) - 1 := by
        have : (Nat.clog 2 W₁.length : ℝ) + 1 ≤ Nat.clog 2 L := by exact_mod_cast hD₁
        linarith
      have hD₂' : ((Nat.clog 2 W₂.length : ℕ) : ℝ) ≤ (Nat.clog 2 L : ℝ) - 1 := by
        have : (Nat.clog 2 W₂.length : ℝ) + 1 ≤ Nat.clog 2 L := by exact_mod_cast hD₂
        linarith
      have h1 : a * Nat.clog 2 W₁.length ≤ a * ((Nat.clog 2 L : ℝ) - 1) :=
        mul_le_mul_of_nonneg_left hD₁' ha0
      have h2 : (m - a) * Nat.clog 2 W₂.length ≤ (m - a) * ((Nat.clog 2 L : ℝ) - 1) :=
        mul_le_mul_of_nonneg_left hD₂' ha1
      push_cast
      push Not at hthr
      nlinarith

end Explore

section Residual

/-- The mass of `X` (with `v` removed) in the row of `v` of `G - K`, from two cut
queries to `G`, given the residual degree `r = r_v`. -/
noncomputable def rowMass (K : WeightedGraph V) (v : V) (r : ℝ) (X : Finset V) :
    Comp (Finset V) ℝ ℝ :=
  (ask (X.erase v)).bind fun a => (ask (insert v (X.erase v))).bind fun b =>
    Comp.pure ((r + (a - K.cut (X.erase v)) - (b - K.cut (insert v (X.erase v)))) / 2)

theorem degree_subtract (G K : WeightedGraph V) (h : ∀ u v, K.w u v ≤ G.w u v) (v : V) :
    (G.subtract K).degree v = G.degree v - K.degree v := by
  rw [← cut_singleton, cut_subtract G K h, cut_singleton, cut_singleton]

theorem rowMass_spec (G K : WeightedGraph V) (h : ∀ u v, K.w u v ≤ G.w u v) (v : V)
    (X : Finset V) :
    (rowMass K v ((G.subtract K).degree v) X).eval G.cut =
        ∑ u ∈ X, (G.subtract K).w v u ∧
      (rowMass K v ((G.subtract K).degree v) X).cost G.cut = 2 := by
  refine ⟨?_, by simp [rowMass]⟩
  simp only [rowMass, eval_bind, eval_ask, eval_pure]
  have hv : Disjoint ({v} : Finset V) (X.erase v) := by simp
  have e := (G.subtract K).cross_eq_three_cuts hv
  rw [cut_subtract G K h, cut_subtract G K h, cut_subtract G K h, cut_singleton,
    cut_singleton, ← Finset.insert_eq] at e
  have hsum : ∑ u ∈ X, (G.subtract K).w v u = ∑ u ∈ X.erase v, (G.subtract K).w v u := by
    by_cases hvX : v ∈ X
    · rw [← Finset.sum_erase _ ((G.subtract K).diag v)]
    · rw [Finset.erase_eq_of_notMem hvX]
  rw [hsum, show ∑ u ∈ X.erase v, (G.subtract K).w v u = (G.subtract K).cross {v} (X.erase v)
    by simp [cross], e, degree_subtract G K h]

/-- Find the residual row entries at `v` heavier than `r / b`, where `r = r_v`. -/
noncomputable def residualRow (K : WeightedGraph V) (v : V) (r b : ℝ) :
    Comp (Finset V) ℝ (V → ℝ) :=
  implement (rowMass K v r) (explore (r / b) (univ.erase v).toList r)

/-- Lemma 3 for a residual row of `R = G - K`, with `K ≤ G` explicit: the output is the
part of the row of `v` strictly above `r_v / b`, with exact weights, and the search uses
at most `2 b ⌈log₂ (N - 1)⌉` cut queries to `G`. -/
theorem residualRow_spec (G K : WeightedGraph V) (h : ∀ u v, K.w u v ≤ G.w u v) (v : V)
    {b : ℕ} (hb : 0 < b) :
    (residualRow K v ((G.subtract K).degree v) b).eval G.cut =
        (fun u => if (G.subtract K).degree v / b < (G.subtract K).w v u
          then (G.subtract K).w v u else 0) ∧
      (residualRow K v ((G.subtract K).degree v) b).cost G.cut ≤
        2 * b * Nat.clog 2 (Fintype.card V - 1) := by
  set R := G.subtract K
  set r := R.degree v
  have hmass : r = ∑ u ∈ (univ.erase v).toList.toFinset, R.w v u := by
    rw [Finset.toList_toFinset, Finset.sum_erase _ (R.diag v)]; rfl
  have hlen : (univ.erase v).toList.length = Fintype.card V - 1 := by
    rw [Finset.length_toList, Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]
  have hr0 : 0 ≤ r := hmass ▸ Finset.sum_nonneg fun u _ => R.nonneg v u
  obtain ⟨he, hc⟩ := explore_spec (fun u => R.w v u) (fun u => R.nonneg v u) (r / b) _ _ r
    le_rfl (Finset.nodup_toList _) hmass
  have himpl : ∀ X, (rowMass K v r X).eval G.cut = ∑ u ∈ X, R.w v u :=
    fun X => (rowMass_spec G K h v X).1
  have hcost1 : ∀ X, (rowMass K v r X).cost G.cut ≤ 2 := fun X => (rowMass_spec G K h v X).2.le
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb
  refine ⟨?_, ?_⟩
  · unfold residualRow
    rw [eval_implement _ _ _ himpl, he]
    funext u
    by_cases hu : u = v
    · subst hu
      have : ¬ r / b < R.w u u := by rw [R.diag]; exact not_lt.mpr (by positivity)
      simp [this]
    · simp [hu]
  · unfold residualRow
    have h1 := cost_implement _ _ _ himpl hcost1 (explore (r / b) (univ.erase v).toList r)
    rw [hlen] at hc
    have h2 : (explore (r / b) (univ.erase v).toList r).cost (fun S => ∑ u ∈ S, R.w v u) ≤
        b * Nat.clog 2 (Fintype.card V - 1) := by
      rcases hr0.lt_or_eq with hr | hr
      · have hthr : 0 < r / b := div_pos hr hbpos
        have : ((explore (r / b) (univ.erase v).toList r).cost
            (fun S => ∑ u ∈ S, R.w v u) : ℝ) ≤ b * Nat.clog 2 (Fintype.card V - 1) := by
          rw [← mul_le_mul_iff_of_pos_left hthr]
          calc _ ≤ _ := hc
            _ = _ := by rw [← mul_assoc, div_mul_cancel₀ _ hbpos.ne']
        exact_mod_cast this
      · have : explore (r / b) (univ.erase v).toList r = Comp.pure 0 := by
          rw [explore, ← hr]; simp
        rw [this]; simp
    calc _ ≤ 2 * _ := h1
      _ ≤ 2 * (b * Nat.clog 2 (Fintype.card V - 1)) := Nat.mul_le_mul_left 2 h2
      _ = _ := (Nat.mul_assoc _ _ _).symm

end Residual

end Discovery
end CutQueryComplexity
