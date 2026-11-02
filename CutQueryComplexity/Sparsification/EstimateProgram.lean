import CutQueryComplexity.Sparsification.EstimateResidual

/-! # Repeated residual draws as a cut-query program

`residualDraws n` calls the ordered residual sampler `n` times and adds the
block-level draws. Its budget is `n` times the sampler's budget. With draw weight
`M/r` and `n = r`, its output law is exactly the counted sample of the residual
bucket, so the estimation soundness and completeness theorems apply to the
program's output. Strong sets are stated in the quotient itself; inside the region
the induced quotient has the same local cuts.

The rounding `r = ⌈ρM/κ⌉` makes every draw weigh at most `κ/ρ`.
-/

namespace CutQueryComplexity.WeightedGraph
noncomputable section
open scoped Classical ENNReal
open Probability
variable {V B : Type} [Fintype V] [DecidableEq V] [Fintype B]

/-- Budget of one ordered residual draw. -/
abbrev residualDrawCost (kb kv : ℕ) : ℕ := (2 * kb + 1) * 3 + 6 * (2 * kv + 1)

/-- `n` independent residual draws, summed at the block level. -/
def residualDraws (kb kv : ℕ) (π : V → B) (cache : B → ℝ) (T : Finset B) (a : ℝ)
    (ha : 0 ≤ a) : (n : ℕ) → RTree (Finset V) ℝ (WeightedGraph B) (n * residualDrawCost kb kv)
  | 0 => RTree.pure (PMF.pure 0)
  | n + 1 => ((sampleResidual kb kv π cache T).bind fun o =>
      (residualDraws kb kv π cache T a ha n).map (fun Y => blockDraw π a ha o + Y)).cast
        (by ring)

theorem residualDraws_eval (G : WeightedGraph V) (kb kv : ℕ) (π : V → B) (cache : B → ℝ)
    (T : Finset B) (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    (residualDraws kb kv π cache T a ha n).eval G.cut =
      independentGraphSum (List.replicate n
        (((sampleResidual kb kv π cache T).eval G.cut).map (blockDraw π a ha))) := by
  induction n with
  | zero => simp [residualDraws, independentGraphSum]
  | succ n ih =>
      rw [residualDraws, RTree.eval_cast, RTree.eval_bind, List.replicate_succ,
        independentGraphSum, PMF.bind_map]
      congr 1
      funext o
      rw [RTree.eval_map, ih]
      rfl

namespace CountedBucket

omit [DecidableEq V] in
theorem sampleLaw_singleton (b : CountedBucket V) :
    sampleLaw [b] = independentGraphSum (List.replicate b.count b.drawLaw) := by
  simp [sampleLaw, expanded, List.map_replicate]

/-- The program's output law is the counted sample of the residual bucket. -/
theorem residualDraws_eval_eq_sampleLaw (G : WeightedGraph V) (kb kv : ℕ) (π : V → B)
    (cache : B → ℝ) (hc : ∀ b, cache b = G.cut (fiber π b)) (T : Finset B)
    (hB : Fintype.card B ≤ 2 ^ kb) (hV : Fintype.card V ≤ 2 ^ kv) (r : ℕ) (hr : 0 < r)
    (hM : 0 < (G.contract π).internalMass T) :
    (residualDraws kb kv π cache T ((G.contract π).internalMass T / r) (by positivity) r).eval
        G.cut = sampleLaw [residualBucket G π T r hr hM] := by
  rw [residualDraws_eval, sampleLaw_singleton, residualBucket_count,
    residualBucket_drawLaw G kb kv π cache hc T hB hV r hr hM]

end CountedBucket

/-! ### Strong sets inside the region -/

omit [Fintype B] in
theorem isStrong_induce_iff (Q : WeightedGraph B) {T W : Finset B} (hW : W ⊆ T) (κ : ℝ) :
    (Q.induce T).IsStrong κ W ↔ Q.IsStrong κ W := by
  have he (S : Finset B) : (Q.induce T).localCut W S = Q.localCut W S := by
    unfold localCut cross
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    change (if u ∈ T ∧ v ∈ T then Q.w u v else 0) = Q.w u v
    exact ite_eq_left ⟨hW (Finset.mem_inter.mp hu).2, hW (Finset.mem_sdiff.mp hv).1⟩
  simp only [IsStrong, he]

/-! ### Rounding the number of draws -/

theorem drawCount_pos {ρ M κ : ℝ} (hρ : 0 < ρ) (hM : 0 < M) (hκ : 0 < κ) :
    0 < ⌈ρ * M / κ⌉₊ := Nat.ceil_pos.mpr (by positivity)

theorem drawCount_smooth {ρ M κ : ℝ} (hρ : 0 < ρ) (hM : 0 < M) (hκ : 0 < κ) :
    ρ * (M / ⌈ρ * M / κ⌉₊) ≤ κ := by
  have hr : (0 : ℝ) < ⌈ρ * M / κ⌉₊ := by exact_mod_cast drawCount_pos hρ hM hκ
  rw [← mul_div_assoc, div_le_iff₀ hr]
  have := Nat.le_ceil (ρ * M / κ)
  rw [div_le_iff₀ hκ] at this
  linarith

/-- In a call that samples, `M ≥ κ/2`, so rounding up at most doubles the count. -/
theorem drawCount_le {ρ M κ : ℝ} (hρ : 2 ≤ ρ) (hκ : 0 < κ) (hMκ : κ / 2 ≤ M) :
    (⌈ρ * M / κ⌉₊ : ℝ) ≤ 2 * (ρ * M / κ) := by
  have h1 : 1 ≤ ρ * M / κ := by
    rw [le_div_iff₀ hκ]
    nlinarith
  have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ ρ * M / κ)
  linarith

/-! ### The estimation contracts for the program -/

/-- **Soundness for the residual program.** Sampled `3κ/4`-strong block sets in the
region lie in `κ/2`-strong block sets of the quotient. -/
theorem residualDraws_sound (G : WeightedGraph V) (kb kv : ℕ) (π : V → B)
    (cache : B → ℝ) (hc : ∀ b, cache b = G.cut (fiber π b)) (T : Finset B)
    (hB : Fintype.card B ≤ 2 ^ kb) (hV : Fintype.card V ≤ 2 ^ kv)
    (hM : 0 < (G.contract π).internalMass T) {κ ρ : ℝ} (hκ : 0 < κ) (hρ : 0 < ρ) :
    Probability.mass
      ((residualDraws kb kv π cache T
        ((G.contract π).internalMass T / ⌈ρ * (G.contract π).internalMass T / κ⌉₊)
        (by positivity) ⌈ρ * (G.contract π).internalMass T / κ⌉₊).eval G.cut)
      (fun X => ¬∀ K ⊆ T, X.IsStrong (3 * κ / 4) K →
        ∃ W, K ⊆ W ∧ W ⊆ T ∧ (G.contract π).IsStrong (κ / 2) W) ≤
      ((T.card - 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(ρ / 32))) := by
  have hr := drawCount_pos hρ hM hκ
  rw [CountedBucket.residualDraws_eval_eq_sampleLaw G kb kv π cache hc T hB hV _ hr hM]
  have h := CountedBucket.sampleLaw_sound [residualBucket G π T _ hr hM] hκ hρ.le
    (fun b hb => by
      rw [List.mem_singleton.mp hb, CountedBucket.residualBucket_mass,
        CountedBucket.residualBucket_count]
      exact drawCount_smooth hρ hM hκ) T
  rw [CountedBucket.residualBucket_reference] at h
  refine le_trans (mass_mono _ (fun X hX => ?_)) h
  intro hall
  apply hX
  intro K hKT hK
  obtain ⟨W, hKW, hWT, hW⟩ := hall K hKT hK
  exact ⟨W, hKW, hWT, (isStrong_induce_iff _ hWT _).mp hW⟩

/-- **Completeness for the residual program.** A `κ`-strong block set inside the
region stays `3κ/4`-strong in the sample. -/
theorem residualDraws_complete (G : WeightedGraph V) (kb kv : ℕ) (π : V → B)
    (cache : B → ℝ) (hc : ∀ b, cache b = G.cut (fiber π b)) (T : Finset B)
    (hB : Fintype.card B ≤ 2 ^ kb) (hV : Fintype.card V ≤ 2 ^ kv)
    (hM : 0 < (G.contract π).internalMass T) {κ ρ δ : ℝ} (hκ : 0 < κ) (hρ : 0 < ρ)
    (hδ : 0 ≤ δ) (hδ2 : δ ≤ 2)
    (hexp : ((2 * Fintype.card B : ℕ) : ℝ) ^ 2 * Real.exp (-(ρ / 128)) ≤ δ / 4)
    {C : Finset B} (hCT : C ⊆ T) (hC : (G.contract π).IsStrong κ C) :
    1 - (Fintype.card B - 1 : ℕ) * δ ≤
      (Probability.mass
        ((residualDraws kb kv π cache T
          ((G.contract π).internalMass T / ⌈ρ * (G.contract π).internalMass T / κ⌉₊)
          (by positivity) ⌈ρ * (G.contract π).internalMass T / κ⌉₊).eval G.cut)
        (fun X => X.IsStrong (3 * κ / 4) C)).toReal := by
  have hr := drawCount_pos hρ hM hκ
  rw [CountedBucket.residualDraws_eval_eq_sampleLaw G kb kv π cache hc T hB hV _ hr hM]
  apply CountedBucket.sampleLaw_complete [residualBucket G π T _ hr hM] hρ hδ hδ2
    (fun b hb => by
      rw [List.mem_singleton.mp hb, CountedBucket.residualBucket_mass,
        CountedBucket.residualBucket_count]
      exact drawCount_smooth hρ hM hκ) _ hexp
  rw [CountedBucket.residualBucket_reference]
  exact (isStrong_induce_iff _ hCT _).mpr hC

end
end CutQueryComplexity.WeightedGraph
