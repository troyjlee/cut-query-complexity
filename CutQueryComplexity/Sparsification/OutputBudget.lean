import CutQueryComplexity.Sparsification.OutputCorrect

/-! # The query cost of output sampling

`eventCount` recomputes, for the fixed graph, the number of output draws an event
takes. `outRun_cost` shows that every supported execution of `outRun` makes at
most `Σ_e (1 + residualDrawCost·eventCount e)` queries.

After a successful estimation run, `outDraws_total_le` bounds the total number of
output draws by `4c(n−1) + n`. Each draw count is at most `cM/β + 1`. Since every
bucket pair has `β > k/4`, the sum `Σ_e M_e/β_e` is at most `2 Σ w/k ≤ 4(n−1)`.
-/

namespace CutQueryComplexity.WeightedGraph
noncomputable section
open scoped Classical ENNReal
open Probability
variable {V : Type} [Fintype V]

/-- Output draws of an event, recomputed from the hidden graph. -/
def eventCount (G : WeightedGraph V) (c : ℝ) (R₂ : ℕ) (e : MergeEvent V) : ℕ :=
  if 0 < cachedMass e.cache e.group (G.cut (pull e.π e.group)) then
    if outCount c e (cachedMass e.cache e.group (G.cut (pull e.π e.group))) ≤ R₂ then
      outCount c e (cachedMass e.cache e.group (G.cut (pull e.π e.group)))
    else 0
  else 0

def outAcc (G : WeightedGraph V) (c : ℝ) (R₂ : ℕ) (L : List (MergeEvent V)) : ℕ :=
  (L.map (fun e => 1 + residualDrawCost (searchDepth V) (searchDepth V) * eventCount G c R₂ e)).sum

theorem eventDraws_cost (G : WeightedGraph V) (c : ℝ) (R₂ : ℕ) (e : MergeEvent V)
    {p : Option (WeightedGraph V) × ℕ}
    (hp : p ∈ (RTree.run G.cut (eventDraws c R₂ e)).support) :
    p.2 ≤ 1 + residualDrawCost (searchDepth V) (searchDepth V) * eventCount G c R₂ e := by
  rw [eventDraws, RTree.run_query] at hp
  obtain ⟨⟨o, k⟩, hok, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
  simp only [eventCount]
  by_cases h1 : 0 < cachedMass e.cache e.group (G.cut (pull e.π e.group))
  · by_cases h2 : outCount c e (cachedMass e.cache e.group (G.cut (pull e.π e.group))) ≤ R₂
    · simp only [h1, h2, ↓reduceDIte, ↓reduceIte] at hok ⊢
      rw [RTree.run_map', RTree.run_weaken] at hok
      obtain ⟨⟨o', k'⟩, hok', he⟩ := (PMF.mem_support_map_iff _ _ _).mp hok
      simp only [Prod.mk.injEq] at he
      obtain ⟨-, rfl⟩ := he
      have := RTree.cost_le _ _ hok'
      simp only [residualDrawCost] at this ⊢
      rw [Nat.mul_comm] at this
      omega
    · simp only [h1, h2, ↓reduceDIte, ↓reduceIte] at hok ⊢
      rw [RTree.run_pure, PMF.pure_map, PMF.mem_support_pure_iff] at hok
      cases hok
      simp
  · simp only [h1, ↓reduceDIte, ↓reduceIte] at hok ⊢
    rw [RTree.run_pure, PMF.pure_map, PMF.mem_support_pure_iff] at hok
    cases hok
    simp

/-- **Cost of output sampling** on every supported execution. -/
theorem outRun_cost (G : WeightedGraph V) (c : ℝ) (R₂ : ℕ) (L : List (MergeEvent V))
    {p : Option (WeightedGraph V) × ℕ} (hp : p ∈ (RTree.run G.cut (outRun c R₂ L)).support) :
    p.2 ≤ outAcc G c R₂ L := by
  induction L generalizing p with
  | nil =>
      rw [outRun, RTree.run_pure, PMF.pure_map, PMF.mem_support_pure_iff] at hp
      subst hp
      simp [outAcc]
  | cons e L ih =>
      rw [outRun, RTree.run_cast, RTree.run_bind] at hp
      obtain ⟨⟨o, k⟩, hok, hp⟩ := (PMF.mem_support_bind_iff _ _ _).mp hp
      obtain ⟨⟨o', k'⟩, hok', rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
      have h1 := eventDraws_cost G c R₂ e hok
      simp only [outAcc, List.map_cons, List.sum_cons] at ih ⊢
      cases o with
      | none =>
          simp only [RTree.run_pure, PMF.pure_map, PMF.mem_support_pure_iff,
            Prod.mk.injEq] at hok'
          obtain ⟨-, rfl⟩ := hok'
          omega
      | some X =>
          simp only [RTree.run_map', PMF.mem_support_map_iff] at hok'
          obtain ⟨⟨o'', k''⟩, hk'', he⟩ := hok'
          simp only [Prod.mk.injEq] at he
          obtain ⟨-, rfl⟩ := he
          have h2 := ih hk''
          simp only at h1 h2 ⊢
          omega

/-! ### Total output draws -/

theorem eventCount_le (G : WeightedGraph V) {c : ℝ} (hc : 0 < c) (R₂ : ℕ) {e : MergeEvent V}
    (hcache : ∀ b, e.cache b = G.cut (fiber e.π b)) (hβ : 0 < e.β) :
    (eventCount G c R₂ e : ℝ) ≤ c * ((G.contract e.π).internalMass e.group / e.β) + 1 := by
  have hm := cachedMass_eq G e.π e.cache hcache e.group
  have hM0 := (G.contract e.π).internalMass_nonneg e.group
  unfold eventCount
  rw [hm]
  have hpos : 0 ≤ c * ((G.contract e.π).internalMass e.group / e.β) := by positivity
  split_ifs
  · have := Nat.ceil_lt_add_one (show 0 ≤ c * (G.contract e.π).internalMass e.group / e.β by
      positivity)
    simp only [outCount]
    rw [mul_div_assoc] at this ⊢
    linarith
  all_goals simp only [Nat.cast_zero]; linarith

/-- `Σ_e M_e/β_e ≤ 4(n−1)` after a successful estimation run. -/
theorem sum_mass_div_label_le {G H : WeightedGraph V} {s : EstState V} (h : EstSuccess G H s) :
    (s.events.map (fun e => (G.contract e.π).internalMass e.group / e.β)).sum ≤
      4 * (Fintype.card V - 1 : ℕ) := by
  -- Per event, the mass over the label is at most a half-sum of `4w/k` over its bucket.
  have hper : ∀ e ∈ s.events, (G.contract e.π).internalMass e.group / e.β ≤
      (∑ u, ∑ v, if InBucket u v e then 4 * (G.w u v / G.strength u v) else 0) / 2 := by
    intro e he
    have hβ := (h.2.1.exact e he).2.2.2
    rw [internalMass_eq_sum, div_div, mul_comm 2 e.β, ← div_div, div_le_div_iff_of_pos_right
      (by norm_num : (0 : ℝ) < 2), Finset.sum_div]
    apply Finset.sum_le_sum
    intro u _
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro v _
    by_cases hb : InBucket u v e
    · have hcond : e.π u ∈ e.group ∧ e.π v ∈ e.group ∧ e.π u ≠ e.π v := ⟨hb.2.1, hb.2.2, hb.1⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true hcond), ite_eq_left_of_eq_true _ _ (eq_true hb)]
      have hl := (h.2.1.label e he u v hb).1
      have hk : 0 < G.strength u v := by
        have := (h.2.1.label e he u v hb).2
        linarith
      rw [div_le_iff₀ hβ]
      have : G.w u v / G.strength u v * G.strength u v = G.w u v := by field_simp
      nlinarith [G.nonneg u v, div_nonneg (G.nonneg u v) hk.le]
    · have hcond : ¬(e.π u ∈ e.group ∧ e.π v ∈ e.group ∧ e.π u ≠ e.π v) :=
        fun hc => hb ⟨hc.2.2, hc.1, hc.2.1⟩
      rw [ite_eq_right_iff.mpr (fun hh => absurd hh hcond),
        ite_eq_right_iff.mpr (fun hh => absurd hh hb)]
      simp
  have hswap : (s.events.map (fun e => (∑ u, ∑ v,
      if InBucket u v e then 4 * (G.w u v / G.strength u v) else 0) / 2)).sum =
      (∑ u, ∑ v, (s.events.map (fun e =>
        if InBucket u v e then 4 * (G.w u v / G.strength u v) else 0)).sum) / 2 := by
    generalize s.events = L
    induction L with
    | nil => simp
    | cons e L ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [ih, ← add_div, ← Finset.sum_add_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro u _
        rw [← Finset.sum_add_distrib]
  have hcount : ∀ u v, (s.events.map (fun e =>
      if InBucket u v e then 4 * (G.w u v / G.strength u v) else 0)).sum ≤
      4 * (G.w u v / G.strength u v) := by
    intro u v
    rw [sum_ite_eq_countP]
    have hx : 0 ≤ 4 * (G.w u v / G.strength u v) :=
      mul_nonneg (by norm_num) (div_nonneg (G.nonneg u v) (G.strength_nonneg u v))
    by_cases huv : u = v
    · subst huv
      simp [G.diag]
    · have hc := h.2.1.count u v huv
      have hle : (s.events.countP (fun e => decide (InBucket u v e)) : ℝ) ≤ 1 := by
        rw [hc]
        split_ifs <;> norm_num
      nlinarith
  have hsum := G.strength_sum_le
  calc
    _ ≤ (s.events.map (fun e => (∑ u, ∑ v,
          if InBucket u v e then 4 * (G.w u v / G.strength u v) else 0) / 2)).sum :=
      List.sum_le_sum (fun e he => hper e he)
    _ = _ := hswap
    _ ≤ (∑ u, ∑ v, 4 * (G.w u v / G.strength u v)) / 2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => hcount u v
    _ = 4 * ((∑ u, ∑ v, G.w u v / G.strength u v) / 2) := by
      have : (∑ u, ∑ v, 4 * (G.w u v / G.strength u v)) =
          4 * ∑ u, ∑ v, G.w u v / G.strength u v := by
        simp_rw [Finset.mul_sum]
      rw [this]
      ring
    _ ≤ _ := by linarith

/-- **Total output draws** after a successful estimation run. -/
theorem outDraws_total_le {G H : WeightedGraph V} {s : EstState V} (h : EstSuccess G H s) {c : ℝ} (hc : 0 < c) (R₂ : ℕ) :
    ((s.events.map (eventCount G c R₂)).sum : ℝ) ≤
      4 * c * (Fintype.card V - 1 : ℕ) + Fintype.card V := by
  have hper : ∀ e ∈ s.events, (eventCount G c R₂ e : ℝ) ≤
      c * ((G.contract e.π).internalMass e.group / e.β) + 1 := fun e he =>
    eventCount_le G hc R₂ (h.2.1.exact e he).2.1 (h.2.1.exact e he).2.2.2
  have hlen : (s.events.length : ℝ) ≤ Fintype.card V := by
    have := h.2.1.length
    exact_mod_cast (Nat.le_add_right _ _).trans this
  have hmass := sum_mass_div_label_le h
  calc
    ((s.events.map (eventCount G c R₂)).sum : ℝ)
        = (s.events.map (fun e => (eventCount G c R₂ e : ℝ))).sum := by
      rw [Nat.cast_list_sum, List.map_map]
      rfl
    _ ≤ (s.events.map (fun e => c * ((G.contract e.π).internalMass e.group / e.β) + 1)).sum :=
      List.sum_le_sum (fun e he => hper e he)
    _ = c * (s.events.map (fun e => (G.contract e.π).internalMass e.group / e.β)).sum +
          s.events.length := by
      rw [List.sum_map_add, List.sum_map_mul_left]
      simp
    _ ≤ _ := by nlinarith

end
end CutQueryComplexity.WeightedGraph
