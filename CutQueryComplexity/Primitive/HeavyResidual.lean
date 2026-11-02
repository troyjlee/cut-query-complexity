import CutQueryComplexity.Primitive.HeavyCross
import CutQueryComplexity.Primitive.Residual

/-! # A heavy original residual edge from cached block cuts

Weighted averaging finds a block whose cut density is at least `2M/n²`.
Two binary searches then find an original edge with at least that weight.
Block selection uses only the public partition and already observed cache.
-/

namespace CutQueryComplexity
noncomputable section
open scoped Classical
open WeightedGraph
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]

private theorem exists_weighted_average (w d : B → ℝ) (hw : ∀ b, 0 ≤ w b)
    (hd : ∀ b, 0 ≤ d b) (hp : 0 < ∑ b, w b) :
    ∃ b, 0 < w b ∧ (∑ c, w c) * d b ≤ (∑ c, d c) * w b := by
  by_contra! h
  have hle (b : B) : (∑ c, d c) * w b ≤ (∑ c, w c) * d b := by
    by_cases hb : 0 < w b
    · exact (h b hb).le
    · have hz : w b = 0 := le_antisymm (le_of_not_gt hb) (hw b)
      rw [hz, mul_zero]
      exact mul_nonneg hp.le (hd b)
  obtain ⟨b, hb, hpos⟩ := (Finset.sum_pos_iff_of_nonneg (fun b _ => hw b)).mp hp
  have hs := Finset.sum_lt_sum (fun b _ => hle b) ⟨b, hb, h b hpos⟩
  simp only [← Finset.mul_sum] at hs
  nlinarith

/-- Number of possible original endpoint pairs across a block cut. -/
def blockPairCount (π : V → B) (b : B) : ℕ := (fiber π b).card * (fiber π b)ᶜ.card

theorem sum_fiber_card (π : V → B) : ∑ b, (fiber π b).card = Fintype.card V := by
  have h := Finset.card_eq_sum_card_fiberwise (f := π)
    (s := (Finset.univ : Finset V)) (t := (Finset.univ : Finset B))
    (fun v _ => Finset.mem_univ (π v))
  simpa [fiber, pull] using h.symm

/-- The total number of candidate endpoint pairs is at most `n²`. -/
theorem sum_blockPairCount_le (π : V → B) :
    ∑ b, blockPairCount π b ≤ Fintype.card V * Fintype.card V := by
  calc
    _ ≤ ∑ b, (fiber π b).card * Fintype.card V := by
      apply Finset.sum_le_sum
      intro b _
      exact Nat.mul_le_mul_left _ (Finset.card_le_univ (fiber π b)ᶜ)
    _ = _ := by rw [← Finset.sum_mul, sum_fiber_card]

theorem cache_sum_eq_twice_mass (G : WeightedGraph V) (π : V → B) (cache : B → ℝ)
    (hc : ∀ b, cache b = G.cut (fiber π b)) :
    ∑ b, cache b = 2 * (G.contract π).internalMass Finset.univ := by
  have h := G.residual_mass_formula π Finset.univ
  simp only [hc]
  simp [pull] at h
  rw [internalMass_univ]
  linarith

/-- Select a block with a sufficiently large observed density, with a total
fallback on inconsistent transcripts. No new graph query occurs here. -/
def chooseHeavyBlock (π : V → B) (cache : B → ℝ) : Option B :=
  if h : ∃ b, 0 < cache b ∧
      (∑ c, cache c) * (blockPairCount π b : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 * cache b
  then some (Classical.choose h) else none

theorem chooseHeavyBlock_positive (G : WeightedGraph V) (π : V → B) (cache : B → ℝ)
    (hc : ∀ b, cache b = G.cut (fiber π b))
    (hp : 0 < (G.contract π).internalMass Finset.univ) :
    ∃ b, chooseHeavyBlock π cache = some b ∧ 0 < G.cut (fiber π b) ∧
      (2 * (G.contract π).internalMass Finset.univ) * (blockPairCount π b : ℝ) ≤
        (Fintype.card V : ℝ) ^ 2 * G.cut (fiber π b) := by
  have hs := cache_sum_eq_twice_mass G π cache hc
  have hw (b : B) : 0 ≤ cache b := by rw [hc]; exact G.cut_nonneg _
  have hd : (∑ b, (blockPairCount π b : ℝ)) ≤ (Fintype.card V : ℝ) ^ 2 := by
    exact_mod_cast (show ∑ b, blockPairCount π b ≤ Fintype.card V ^ 2 by
      simpa [pow_two] using sum_blockPairCount_le π)
  have hex : ∃ b, 0 < cache b ∧
      (∑ c, cache c) * (blockPairCount π b : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 * cache b := by
    obtain ⟨b, hb, hav⟩ := exists_weighted_average cache (fun b => (blockPairCount π b : ℝ))
      hw (fun _ => Nat.cast_nonneg _) (by rw [hs]; positivity)
    exact ⟨b, hb, hav.trans (mul_le_mul_of_nonneg_right hd hb.le)⟩
  have hbound (b : B)
      (h : (∑ c, cache c) * (blockPairCount π b : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 * cache b) :
      (2 * (G.contract π).internalMass Finset.univ) * (blockPairCount π b : ℝ) ≤
        (Fintype.card V : ℝ) ^ 2 * G.cut (fiber π b) := by
    rw [hs] at h
    simpa only [hc] using h
  refine ⟨Classical.choose hex, by rw [chooseHeavyBlock, dite_eq_left hex], ?_, ?_⟩
  · simpa only [hc] using (Classical.choose_spec hex).1
  · exact hbound _ (Classical.choose_spec hex).2

theorem chooseHeavyBlock_zero (G : WeightedGraph V) (π : V → B) (cache : B → ℝ)
    (hc : ∀ b, cache b = G.cut (fiber π b))
    (hz : (G.contract π).internalMass Finset.univ = 0) : chooseHeavyBlock π cache = none := by
  have hs : ∑ b, cache b = 0 := by rw [cache_sum_eq_twice_mass G π cache hc, hz, mul_zero]
  have hw (b : B) : 0 ≤ cache b := by rw [hc]; exact G.cut_nonneg _
  have he (b : B) : cache b = 0 := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hw b)).mp hs
    b (Finset.mem_univ _)
  simp [chooseHeavyBlock, he]

/-- Find a positive surviving edge with weight at least `2M/n²` in `6*(k+1)`
original cut queries, given correct cached block cuts. -/
def findHeavyResidual (k : ℕ) (π : V → B) (cache : B → ℝ) :
    DTree (Finset V) ℝ (Option (V × V)) (6 * (k + 1)) :=
  match chooseHeavyBlock π cache with
  | none => DTree.pure none
  | some b => findHeavyCross k (fiber π b) (fiber π b)ᶜ

def HeavyResidualResult (G : WeightedGraph V) (π : V → B) : Option (V × V) → Prop
  | none => (G.contract π).internalMass Finset.univ = 0
  | some (u, v) => π u ≠ π v ∧ 0 < G.w u v ∧
      2 * (G.contract π).internalMass Finset.univ ≤ (Fintype.card V : ℝ) ^ 2 * G.w u v

theorem findHeavyResidual_positive (G : WeightedGraph V) (k : ℕ) (π : V → B)
    (cache : B → ℝ) (hc : ∀ b, cache b = G.cut (fiber π b))
    (hn : Fintype.card V ≤ 2 ^ k) (hp : 0 < (G.contract π).internalMass Finset.univ) :
    ∃ u v, (findHeavyResidual k π cache).eval G.cut = some (u, v) ∧
      π u ≠ π v ∧ 0 < G.w u v ∧
        2 * (G.contract π).internalMass Finset.univ ≤ (Fintype.card V : ℝ) ^ 2 * G.w u v := by
  obtain ⟨b, he, hb, hav⟩ := chooseHeavyBlock_positive G π cache hc hp
  obtain ⟨u, v, huv, hu, hv, hw, hpair⟩ := findHeavyCross_positive G k
    (disjoint_compl_right : Disjoint (fiber π b) (fiber π b)ᶜ) hn (by simpa using hb)
  have hd : 0 < (blockPairCount π b : ℝ) := by
    exact_mod_cast Nat.mul_pos (Finset.card_pos.mpr ⟨u, hu⟩) (Finset.card_pos.mpr ⟨v, hv⟩)
  have hpair' : G.cut (fiber π b) ≤ (blockPairCount π b : ℝ) * G.w u v := by
    simpa [blockPairCount, Nat.cast_mul, mul_assoc] using hpair
  refine ⟨u, v, by simpa [findHeavyResidual, he] using huv, ?_, hw, ?_⟩
  · have hu' := (mem_fiber π b u).mp hu
    have hv' : π v ≠ b := by simpa using hv
    intro h
    exact hv' (h ▸ hu')
  · apply (mul_le_mul_iff_right₀ hd).mp
    calc
      _ = (2 * (G.contract π).internalMass Finset.univ) * (blockPairCount π b : ℝ) :=
        mul_comm _ _
      _ ≤ (Fintype.card V : ℝ) ^ 2 * G.cut (fiber π b) := hav
      _ ≤ (Fintype.card V : ℝ) ^ 2 * ((blockPairCount π b : ℝ) * G.w u v) :=
        mul_le_mul_of_nonneg_left hpair' (sq_nonneg _)
      _ = (blockPairCount π b : ℝ) * ((Fintype.card V : ℝ) ^ 2 * G.w u v) := by ring

theorem findHeavyResidual_correct (G : WeightedGraph V) (k : ℕ) (π : V → B)
    (cache : B → ℝ) (hc : ∀ b, cache b = G.cut (fiber π b))
    (hn : Fintype.card V ≤ 2 ^ k) :
    HeavyResidualResult G π ((findHeavyResidual k π cache).eval G.cut) := by
  by_cases hp : 0 < (G.contract π).internalMass Finset.univ
  · obtain ⟨u, v, he, huv, hw, hav⟩ := findHeavyResidual_positive G k π cache hc hn hp
    rw [he]
    exact ⟨huv, hw, hav⟩
  · have hz := le_antisymm (le_of_not_gt hp) ((G.contract π).internalMass_nonneg Finset.univ)
    simp only [findHeavyResidual, chooseHeavyBlock_zero G π cache hc hz, DTree.eval_pure]
    exact hz

/-- A standalone deterministic program, including cache initialization. -/
def findHeavyResidualFresh (π : V → B) :
    DTree (Finset V) ℝ (Option (V × V)) (Fintype.card B + 6 * (searchDepth V + 1)) :=
  (cacheBlockCuts π).bind (fun cache => findHeavyResidual (searchDepth V) π cache)

theorem findHeavyResidualFresh_eval (G : WeightedGraph V) (π : V → B) :
    (findHeavyResidualFresh π).eval G.cut =
      (findHeavyResidual (searchDepth V) π (fun b => G.cut (fiber π b))).eval G.cut := by
  simp only [findHeavyResidualFresh, DTree.eval, DTree.run_bind, cacheBlockCuts_run]

theorem findHeavyResidualFresh_solves (π : V → B) :
    (findHeavyResidualFresh π).Solves WeightedGraph.cut (fun G o => HeavyResidualResult G π o) := by
  intro G
  rw [findHeavyResidualFresh_eval]
  exact findHeavyResidual_correct G _ π _ (fun _ => rfl) (Nat.le_pow_clog (by decide) _)

end
end CutQueryComplexity
