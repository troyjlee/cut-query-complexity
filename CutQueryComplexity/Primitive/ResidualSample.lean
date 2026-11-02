import CutQueryComplexity.Primitive.ResidualDegree
import CutQueryComplexity.Primitive.WeightedSample
import CutQueryComplexity.Probability.OptionBind

/-! # Sampling an original residual edge in logarithmically many cut queries

Choose a block according to its residual degree inside the public region,
then sample an original edge crossing from that block to the rest of the
region. Each undirected edge has probability `w/M`, with each orientation
carrying half that probability. No quotient-edge identity is substituted for
the original endpoints. All query choices use the public map and observed cache.
-/

namespace CutQueryComplexity
noncomputable section
open scoped Classical ENNReal
open Probability WeightedGraph
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]

/-- Choose the first block using the exact additive residual-degree oracle. -/
def sampleResidualBlock (k : ℕ) (π : V → B) (cache : B → ℝ) (T : Finset B) :
    RTree (Finset V) ℝ (Option B) ((2 * k + 1) * 3) :=
  (sampleSubset k Finset.univ).substitute (residualDegreeQuery π cache T)

theorem sampleResidualBlock_eval (G : WeightedGraph V) (k : ℕ) (π : V → B)
    (cache : B → ℝ) (hc : ∀ b, cache b = G.cut (fiber π b)) (T : Finset B) :
    (sampleResidualBlock k π cache T).eval G.cut =
      (sampleSubset k Finset.univ).eval (subsetSum (G.residualDegree π T)) := by
  simp only [sampleResidualBlock, RTree.eval_substitute, residualDegreeQuery_eval G π cache hc]

theorem sampleResidualBlock_scaled (G : WeightedGraph V) (k : ℕ) (π : V → B)
    (cache : B → ℝ) (hc : ∀ b, cache b = G.cut (fiber π b)) (T : Finset B)
    (hn : Fintype.card B ≤ 2 ^ k) (o : Option B) :
    ENNReal.ofReal (2 * (G.contract π).internalMass T) *
      ((sampleResidualBlock k π cache T).eval G.cut) o =
        outputMass (G.residualDegree π T) Finset.univ o := by
  rw [sampleResidualBlock_eval G k π cache hc]
  simpa only [residualDegree_total] using sampleSubset_scaled (G.residualDegree π T)
    (G.residualDegree_nonneg π T) k Finset.univ (by simpa using hn) o

theorem fiber_disjoint_pull_sdiff (π : V → B) (T : Finset B) (b : B) :
    Disjoint (fiber π b) (pull π (T \ {b})) := by
  apply Finset.disjoint_left.mpr
  intro v hv ht
  have hb := (mem_fiber π b v).mp hv
  have hT := (mem_pull π (T \ {b}) v).mp ht
  simpa [hb] using hT

/-- Sample original endpoints. With both label sets of size at most `n`, the
budget is `18 * ceil(log₂ n) + 9`, after the block cuts have been cached. -/
def sampleResidual (kb kv : ℕ) (π : V → B) (cache : B → ℝ) (T : Finset B) :
    RTree (Finset V) ℝ (Option (V × V)) ((2 * kb + 1) * 3 + 6 * (2 * kv + 1)) :=
  (sampleResidualBlock kb π cache T).bind fun ob => match ob with
    | none => RTree.pure (PMF.pure none)
    | some b => sampleCross kv (fiber π b) (pull π (T \ {b}))

theorem sampleResidual_eval (G : WeightedGraph V) (kb kv : ℕ) (π : V → B)
    (cache : B → ℝ) (T : Finset B) :
    (sampleResidual kb kv π cache T).eval G.cut =
      bindOption ((sampleResidualBlock kb π cache T).eval G.cut)
        (fun b => (sampleCross kv (fiber π b) (pull π (T \ {b}))).eval G.cut) := by
  rw [sampleResidual, RTree.eval_bind, bindOption]
  congr 1
  funext ob
  cases ob <;> simp

/-- Exact unnormalized law for every orientation, including zero total mass. -/
theorem sampleResidual_scaled (G : WeightedGraph V) (kb kv : ℕ) (π : V → B)
    (cache : B → ℝ) (hc : ∀ b, cache b = G.cut (fiber π b)) (T : Finset B)
    (hB : Fintype.card B ≤ 2 ^ kb) (hV : Fintype.card V ≤ 2 ^ kv) (u v : V) :
    ENNReal.ofReal (2 * (G.contract π).internalMass T) *
      ((sampleResidual kb kv π cache T).eval G.cut) (some (u, v)) =
        if π u ∈ T ∧ π v ∈ T ∧ π u ≠ π v then ENNReal.ofReal (G.w u v) else 0 := by
  rw [sampleResidual_eval, bindOption_some, Finset.mul_sum]
  calc
    _ = ∑ b : B, if π u = b then
        (if π u ∈ T ∧ π v ∈ T ∧ π u ≠ π v then ENNReal.ofReal (G.w u v) else 0)
        else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      rw [← mul_assoc, sampleResidualBlock_scaled G kb π cache hc T hB]
      simp only [outputMass, Finset.mem_univ, ↓reduceIte]
      by_cases hbT : b ∈ T
      · rw [G.residualDegree_cross π hbT,
          sampleCross_scaled G kv (fiber_disjoint_pull_sdiff π T b) hV]
        by_cases hb : π u = b <;> simp [mem_fiber, mem_pull, hb, hbT, ne_comm]
      · simp only [residualDegree, ite_eq_right hbT, ENNReal.ofReal_zero, zero_mul]
        by_cases hb : π u = b <;> simp [hb, hbT]
    _ = _ := by simp

theorem sampleResidual_none_scaled (G : WeightedGraph V) (kb kv : ℕ) (π : V → B)
    (cache : B → ℝ) (hc : ∀ b, cache b = G.cut (fiber π b)) (T : Finset B)
    (hB : Fintype.card B ≤ 2 ^ kb) (hV : Fintype.card V ≤ 2 ^ kv) :
    ENNReal.ofReal (2 * (G.contract π).internalMass T) *
      ((sampleResidual kb kv π cache T).eval G.cut) none = 0 := by
  rw [sampleResidual_eval, bindOption_none, mul_add,
    sampleResidualBlock_scaled G kb π cache hc T hB]
  simp only [outputMass, zero_add, Finset.mul_sum, ← mul_assoc]
  apply Finset.sum_eq_zero
  intro b _
  rw [sampleResidualBlock_scaled G kb π cache hc T hB]
  simp only [outputMass, Finset.mem_univ, ↓reduceIte]
  by_cases hb : b ∈ T
  · rw [G.residualDegree_cross π hb,
      sampleCross_none_scaled G kv (fiber_disjoint_pull_sdiff π T b) hV]
  · simp [residualDegree, hb]

/-- If no original edge survives inside the region, absence is certain. -/
theorem sampleResidual_zero (G : WeightedGraph V) (kb kv : ℕ) (π : V → B)
    (cache : B → ℝ) (hc : ∀ b, cache b = G.cut (fiber π b)) (T : Finset B)
    (hz : (G.contract π).internalMass T = 0) :
    (sampleResidual kb kv π cache T).eval G.cut = PMF.pure none := by
  rw [sampleResidual_eval, sampleResidualBlock_eval G kb π cache hc]
  rw [sampleSubset_zero _ _ _ (by rw [G.residualDegree_total, hz, mul_zero])]
  exact bindOption_pure_none _

/-- Positive residual mass never returns absence. -/
theorem sampleResidual_none (G : WeightedGraph V) (kb kv : ℕ) (π : V → B)
    (cache : B → ℝ) (hc : ∀ b, cache b = G.cut (fiber π b)) (T : Finset B)
    (hB : Fintype.card B ≤ 2 ^ kb) (hV : Fintype.card V ≤ 2 ^ kv)
    (hp : 0 < (G.contract π).internalMass T) :
    ((sampleResidual kb kv π cache T).eval G.cut) none = 0 := by
  exact (mul_eq_zero.mp (sampleResidual_none_scaled G kb kv π cache hc T hB hV)).resolve_left
    (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity)))

/-- Each orientation has probability `w/(2M)`; internal-to-block and out-of-region
pairs have probability zero. -/
theorem sampleResidual_law (G : WeightedGraph V) (kb kv : ℕ) (π : V → B)
    (cache : B → ℝ) (hc : ∀ b, cache b = G.cut (fiber π b)) (T : Finset B)
    (hB : Fintype.card B ≤ 2 ^ kb) (hV : Fintype.card V ≤ 2 ^ kv)
    (hp : 0 < (G.contract π).internalMass T) (u v : V) :
    ((sampleResidual kb kv π cache T).eval G.cut) (some (u, v)) =
      (if π u ∈ T ∧ π v ∈ T ∧ π u ≠ π v then ENNReal.ofReal (G.w u v) else 0) /
        ENNReal.ofReal (2 * (G.contract π).internalMass T) := by
  have hn : ENNReal.ofReal (2 * (G.contract π).internalMass T) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  apply (ENNReal.mul_right_inj hn ENNReal.ofReal_ne_top).mp
  rw [sampleResidual_scaled G kb kv π cache hc T hB hV, div_eq_mul_inv, mul_left_comm,
    ENNReal.mul_inv_cancel hn ENNReal.ofReal_ne_top, mul_one]

end
end CutQueryComplexity
