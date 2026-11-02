import CutQueryComplexity.Sparsification.OutputRun

/-! # Correctness of output sampling after a successful estimation run

Let `s` be a successful finished estimation state. Its events satisfy:

* **Exact reference.** Every positive edge lies in exactly one bucket, so the
  buckets' reference graph is `G` (`eventBuckets_reference`).
* **Admissibility.** Every bucket pair has strength at least its label `β`, and
  `r = ⌈cM/β⌉` gives `c·M/r ≤ β`, so each bucket's draws are admissible
  (`eventBuckets_admissible`).
* **Caps.** Each pair in a bucket has `w ≤ k < 4β`, so `M/β ≤ 2n²` and the cap
  `R₂ = ⌈2cn²⌉` never binds (`outCount_le_cap`).

`outRun_sparsifier` concludes: if `ε²c ≥ 8(2 log 2n + log(4/δ))`, the output is a
`1 ± ε` cut sparsifier of `G` with probability at least `1 − (n−1)δ`.
-/

namespace CutQueryComplexity.WeightedGraph
noncomputable section
open scoped Classical ENNReal
open Probability
variable {V : Type} [Fintype V]

/-! ### Bucket graphs -/

omit [Fintype V] in
theorem bucketGraph_w (G : WeightedGraph V) (e : MergeEvent V) (u v : V) :
    (bucketGraph G e.π e.group).w u v = if InBucket u v e then G.w u v else 0 := by
  by_cases hb : InBucket u v e
  · have h : e.π u ∈ e.group ∧ e.π v ∈ e.group ∧ e.π u ≠ e.π v := ⟨hb.2.1, hb.2.2, hb.1⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true hb)]
    show (if e.π u ∈ e.group ∧ e.π v ∈ e.group ∧ e.π u ≠ e.π v then G.w u v else 0) = G.w u v
    rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
  · have h : ¬(e.π u ∈ e.group ∧ e.π v ∈ e.group ∧ e.π u ≠ e.π v) :=
      fun h => hb ⟨h.2.2, h.1, h.2.1⟩
    rw [ite_eq_right_iff.mpr (fun hh => absurd hh hb)]
    show (if e.π u ∈ e.group ∧ e.π v ∈ e.group ∧ e.π u ≠ e.π v then G.w u v else 0) = 0
    rw [ite_eq_right_iff.mpr (fun hh => absurd hh h)]

/-- A bucket with no residual mass has no positive edge. -/
theorem bucketGraph_eq_zero (G : WeightedGraph V) (e : MergeEvent V)
    (hM : ¬0 < (G.contract e.π).internalMass e.group) : bucketGraph G e.π e.group = 0 := by
  have hz : (G.contract e.π).internalMass e.group = 0 :=
    le_antisymm (not_lt.mp hM) ((G.contract e.π).internalMass_nonneg _)
  rw [internalMass_eq_sum] at hz
  have hsum : ∑ u, ∑ v, (if e.π u ∈ e.group ∧ e.π v ∈ e.group ∧ e.π u ≠ e.π v then G.w u v
      else 0) = 0 := by linarith
  have hnn (u v : V) : 0 ≤ (if e.π u ∈ e.group ∧ e.π v ∈ e.group ∧ e.π u ≠ e.π v then G.w u v
      else 0) := by split <;> simp [G.nonneg]
  ext u v
  have hu := (Finset.sum_eq_zero_iff_of_nonneg (fun u _ =>
    Finset.sum_nonneg (fun v _ => hnn u v))).mp hsum u (Finset.mem_univ _)
  have huv := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => hnn u v)).mp hu v (Finset.mem_univ _)
  simpa [bucketGraph] using huv

theorem sum_ite_eq_countP {α : Type} (L : List α) (P : α → Prop) (x : ℝ) :
    (L.map (fun e => if P e then x else 0)).sum = (L.countP (fun e => decide (P e)) : ℝ) * x := by
  induction L with
  | nil => simp
  | cons e L ih =>
      simp only [List.map_cons, List.sum_cons, ih, List.countP_cons]
      by_cases h : P e <;> simp [h]; ring

theorem eventBuckets_reference_w (G : WeightedGraph V) {c : ℝ} (hc : 0 < c)
    (L : List (MergeEvent V)) (hL : ∀ e ∈ L, 0 < e.β) (u v : V) :
    (CountedBucket.reference (eventBuckets G c hc L)).w u v =
      (L.map (fun e => (bucketGraph G e.π e.group).w u v)).sum := by
  induction L with
  | nil => simp [CountedBucket.reference, eventBuckets, sumGraphs]
  | cons e L ih =>
      have ih' := ih (fun e' he' => hL e' (List.mem_cons_of_mem _ he'))
      have hβ := hL e List.mem_cons_self
      simp only [CountedBucket.reference, eventBuckets, sumGraphs_w, List.map_map] at ih' ⊢
      by_cases hM : 0 < (G.contract e.π).internalMass e.group
      · have hb : eventBucket G c hc e = some (outBucket G e.π e.group
            (outCount c e ((G.contract e.π).internalMass e.group)) (outCount_pos hc hβ hM) hM) := by
          simp only [eventBucket, hM, hβ, and_self, ↓reduceDIte]
        simp only [List.filterMap_cons, hb, List.map_cons, List.sum_cons, Function.comp_apply,
          CountedBucket.outBucket_graph, ih']
      · have hb : eventBucket G c hc e = none := by
          have : ¬(0 < (G.contract e.π).internalMass e.group ∧ 0 < e.β) := fun h => hM h.1
          simp only [eventBucket, this, ↓reduceDIte]
        simp only [List.filterMap_cons, hb, List.map_cons, List.sum_cons, ih',
          bucketGraph_eq_zero G e hM, zero_w, _root_.zero_add]

/-- **The buckets reproduce the input graph.** -/
theorem eventBuckets_reference {G H : WeightedGraph V} (hH : IsApproxKruskalForest G H)
    {s : EstState V} (h : EstSuccess G H s) {c : ℝ} (hc : 0 < c) :
    CountedBucket.reference (eventBuckets G c hc s.events) = G := by
  ext u v
  rw [eventBuckets_reference_w G hc s.events (fun e he => (h.2.1.exact e he).2.2.2)]
  simp only [bucketGraph_w]
  rw [sum_ite_eq_countP]
  by_cases huv : u = v
  · subst huv
    simp [G.diag]
  by_cases hw : G.w u v = 0
  · rw [hw, mul_zero]
  · have hpos : 0 < G.w u v := lt_of_le_of_ne (G.nonneg u v) (Ne.symm hw)
    have hk : 0 < G.strength u v := hpos.trans_le (G.weight_le_strength u v)
    rw [h.2.1.count u v huv, ite_eq_left_of_eq_true _ _ (eq_true (h.same_block hH hk))]
    simp


theorem mem_eventBuckets {G : WeightedGraph V} {c : ℝ} {hc : 0 < c} {L : List (MergeEvent V)}
    {b : CountedBucket V} (hb : b ∈ eventBuckets G c hc L) :
    ∃ e ∈ L, ∃ (hM : 0 < (G.contract e.π).internalMass e.group) (hβ : 0 < e.β),
      b = outBucket G e.π e.group (outCount c e ((G.contract e.π).internalMass e.group))
        (outCount_pos hc hβ hM) hM := by
  obtain ⟨e, he, hbe⟩ := List.mem_filterMap.mp hb
  unfold eventBucket at hbe
  split_ifs at hbe with h
  · exact ⟨e, he, h.1, h.2, (Option.some.inj hbe).symm⟩

/-- **Admissibility of the output buckets.** -/
theorem eventBuckets_admissible {G H : WeightedGraph V} (hH : IsApproxKruskalForest G H)
    {s : EstState V} (h : EstSuccess G H s) {c : ℝ} (hc : 0 < c) :
    ∀ b ∈ eventBuckets G c hc s.events,
      b.Admissible (CountedBucket.reference (eventBuckets G c hc s.events)) c := by
  rw [eventBuckets_reference hH h hc]
  intro b hb
  obtain ⟨e, he, hM, hβ, rfl⟩ := mem_eventBuckets hb
  apply CountedBucket.admissible_of_count _ G c hβ
  · intro p hp
    have hp' : 0 < bucketWeight G e.π e.group p := hp
    unfold bucketWeight at hp'
    split_ifs at hp' with hcond
    · exact (h.2.1.label e he p.val.1 p.val.2 ⟨hcond.2.2, hcond.1, hcond.2.1⟩).2
    · exact absurd hp' (lt_irrefl 0)
  · simp only [CountedBucket.outBucket_mass, CountedBucket.outBucket_count, outCount]
    exact Nat.le_ceil _

/-- Output caps never bind on a successful run. -/
theorem outCount_le_cap {G H : WeightedGraph V} {s : EstState V} (h : EstSuccess G H s)
    {c : ℝ} (hc : 0 < c) {e : MergeEvent V} (he : e ∈ s.events) :
    outCount c e ((G.contract e.π).internalMass e.group) ≤
      ⌈2 * c * (Fintype.card V : ℝ) ^ 2⌉₊ := by
  have hβ := (h.2.1.exact e he).2.2.2
  apply Nat.ceil_mono
  rw [div_le_iff₀ hβ, internalMass_eq_sum]
  -- Every bucket pair has weight below `4β`.
  have hterm : ∀ u v, (if e.π u ∈ e.group ∧ e.π v ∈ e.group ∧ e.π u ≠ e.π v then G.w u v
      else 0) ≤ 4 * e.β := by
    intro u v
    split_ifs with hcond
    · have hl := (h.2.1.label e he u v ⟨hcond.2.2, hcond.1, hcond.2.1⟩).1
      linarith [G.weight_le_strength u v]
    · linarith
  have hsum : ∑ u, ∑ v, (if e.π u ∈ e.group ∧ e.π v ∈ e.group ∧ e.π u ≠ e.π v then G.w u v
      else 0) ≤ (Fintype.card V : ℝ) ^ 2 * (4 * e.β) := by
    calc
      _ ≤ ∑ _u : V, ∑ _v : V, 4 * e.β := Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => hterm u v
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]; ring
  nlinarith

/-- **Output sparsifier guarantee** after a successful estimation run. -/
theorem outRun_sparsifier {G H : WeightedGraph V} (hH : IsApproxKruskalForest G H)
    {s : EstState V} (h : EstSuccess G H s) {c ε δ : ℝ} (hc : 0 < c) (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ2 : δ ≤ 2)
    (hlog : 8 * (2 * Real.log (2 * Fintype.card V) + Real.log (4 / δ)) ≤ ε ^ 2 * c) :
    1 - (Fintype.card V - 1 : ℕ) * δ ≤
      (Probability.mass ((outRun c ⌈2 * c * (Fintype.card V : ℝ) ^ 2⌉₊ s.events).eval G.cut)
        (fun o => ∃ X, o = some X ∧ IsCutSparsifier ε G X)).toReal := by
  rw [outRun_eval G c hc _ s.events (fun e he =>
    ⟨(h.2.1.exact e he).2.1, (h.2.1.exact e he).2.2.2, fun _ => outCount_le_cap h hc he⟩),
    mass_map]
  have hsucc := CountedBucket.sampleLaw_success_of_log (eventBuckets G c hc s.events) hε hε1 hc
    hδ hδ2 (eventBuckets_admissible hH h hc) hlog
  rw [eventBuckets_reference hH h hc] at hsucc
  simpa using hsucc

end
end CutQueryComplexity.WeightedGraph
