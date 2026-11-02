import CutQueryComplexity.Primitive.ResidualSample
import CutQueryComplexity.Probability.UndirectedPair

/-! # Unordered residual-edge sampling and cache initialization

The cached sampler costs `6*clog₂ |B| + 12*clog₂ |V| + 9` original cut
queries. Its output is an unordered pair of original vertices. The standalone
program initializes the cache in `|B|` queries and works uniformly for every
nonnegative weighted input, with no supplied information about that input.
-/

namespace CutQueryComplexity
noncomputable section
open scoped Classical ENNReal
open Probability WeightedGraph
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]

/-- Forgetting orientation is free and retains the original edge identity. -/
def sampleResidualEdge (kb kv : ℕ) (π : V → B) (cache : B → ℝ) (T : Finset B) :
    RTree (Finset V) ℝ (Option (Sym2 V)) ((2 * kb + 1) * 3 + 6 * (2 * kv + 1)) :=
  (sampleResidual kb kv π cache T).map (Option.map fun uv => s(uv.1, uv.2))

theorem sampleResidualEdge_eval (G : WeightedGraph V) (kb kv : ℕ) (π : V → B)
    (cache : B → ℝ) (T : Finset B) :
    (sampleResidualEdge kb kv π cache T).eval G.cut =
      forgetOrientation ((sampleResidual kb kv π cache T).eval G.cut) := by
  rw [sampleResidualEdge, RTree.eval_map]
  rfl

/-- The unordered edge carries its original weight as unnormalized mass. -/
theorem sampleResidualEdge_scaled (G : WeightedGraph V) (kb kv : ℕ) (π : V → B)
    (cache : B → ℝ) (hc : ∀ b, cache b = G.cut (fiber π b)) (T : Finset B)
    (hB : Fintype.card B ≤ 2 ^ kb) (hV : Fintype.card V ≤ 2 ^ kv)
    {u v : V} (hne : u ≠ v) :
    ENNReal.ofReal ((G.contract π).internalMass T) *
      ((sampleResidualEdge kb kv π cache T).eval G.cut) (some s(u, v)) =
        if π u ∈ T ∧ π v ∈ T ∧ π u ≠ π v then ENNReal.ofReal (G.w u v) else 0 := by
  rw [sampleResidualEdge_eval, forgetOrientation_some _ hne]
  have ht : ENNReal.ofReal (2 * (G.contract π).internalMass T) =
      2 * ENNReal.ofReal ((G.contract π).internalMass T) := by
    rw [ENNReal.ofReal_mul (by norm_num)]
    norm_num
  apply (ENNReal.mul_right_inj (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num)).mp
  rw [← mul_assoc, ← ht, mul_add,
    sampleResidual_scaled G kb kv π cache hc T hB hV,
    sampleResidual_scaled G kb kv π cache hc T hB hV, G.symm v u, two_mul]
  congr 1
  simp only [ne_comm, and_comm, and_left_comm, and_assoc]

/-- Exact `w/M` probability for each surviving original edge. -/
theorem sampleResidualEdge_law (G : WeightedGraph V) (kb kv : ℕ) (π : V → B)
    (cache : B → ℝ) (hc : ∀ b, cache b = G.cut (fiber π b)) (T : Finset B)
    (hB : Fintype.card B ≤ 2 ^ kb) (hV : Fintype.card V ≤ 2 ^ kv)
    (hp : 0 < (G.contract π).internalMass T) {u v : V} (hne : u ≠ v) :
    ((sampleResidualEdge kb kv π cache T).eval G.cut) (some s(u, v)) =
      (if π u ∈ T ∧ π v ∈ T ∧ π u ≠ π v then ENNReal.ofReal (G.w u v) else 0) /
        ENNReal.ofReal ((G.contract π).internalMass T) := by
  have hn : ENNReal.ofReal ((G.contract π).internalMass T) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hp)
  apply (ENNReal.mul_right_inj hn ENNReal.ofReal_ne_top).mp
  rw [sampleResidualEdge_scaled G kb kv π cache hc T hB hV hne,
    div_eq_mul_inv, mul_left_comm, ENNReal.mul_inv_cancel hn ENNReal.ofReal_ne_top, mul_one]

theorem sampleResidualEdge_zero (G : WeightedGraph V) (kb kv : ℕ) (π : V → B)
    (cache : B → ℝ) (hc : ∀ b, cache b = G.cut (fiber π b)) (T : Finset B)
    (hz : (G.contract π).internalMass T = 0) :
    (sampleResidualEdge kb kv π cache T).eval G.cut = PMF.pure none := by
  rw [sampleResidualEdge_eval, sampleResidual_zero G kb kv π cache hc T hz,
    forgetOrientation_pure_none]

theorem sampleResidualEdge_none (G : WeightedGraph V) (kb kv : ℕ) (π : V → B)
    (cache : B → ℝ) (hc : ∀ b, cache b = G.cut (fiber π b)) (T : Finset B)
    (hB : Fintype.card B ≤ 2 ^ kb) (hV : Fintype.card V ≤ 2 ^ kv)
    (hp : 0 < (G.contract π).internalMass T) :
    ((sampleResidualEdge kb kv π cache T).eval G.cut) none = 0 := by
  rw [sampleResidualEdge_eval, forgetOrientation_none]
  exact sampleResidual_none G kb kv π cache hc T hB hV hp

theorem sampleResidualEdge_diag (G : WeightedGraph V) (kb kv : ℕ) (π : V → B)
    (cache : B → ℝ) (hc : ∀ b, cache b = G.cut (fiber π b)) (T : Finset B)
    (hB : Fintype.card B ≤ 2 ^ kb) (hV : Fintype.card V ≤ 2 ^ kv) (u : V) :
    ((sampleResidualEdge kb kv π cache T).eval G.cut) (some s(u, u)) = 0 := by
  by_cases hz : (G.contract π).internalMass T = 0
  · rw [sampleResidualEdge_zero G kb kv π cache hc T hz]
    simp [PMF.pure_apply]
  · have hp := lt_of_le_of_ne ((G.contract π).internalMass_nonneg T) (Ne.symm hz)
    rw [sampleResidualEdge_eval, forgetOrientation_diag,
      sampleResidual_law G kb kv π cache hc T hB hV hp]
    simp

/-- An explicit absence certificate, or a positive surviving original edge. -/
def ResidualEdgeResult (G : WeightedGraph V) (π : V → B) (T : Finset B) :
    Option (Sym2 V) → Prop
  | none => (G.contract π).internalMass T = 0
  | some e => ∃ u v, e = s(u, v) ∧ π u ∈ T ∧ π v ∈ T ∧ π u ≠ π v ∧ 0 < G.w u v

theorem sampleResidualEdge_correct (G : WeightedGraph V) (kb kv : ℕ) (π : V → B)
    (cache : B → ℝ) (hc : ∀ b, cache b = G.cut (fiber π b)) (T : Finset B)
    (hB : Fintype.card B ≤ 2 ^ kb) (hV : Fintype.card V ≤ 2 ^ kv)
    (o : Option (Sym2 V)) (ho : o ∈ ((sampleResidualEdge kb kv π cache T).eval G.cut).support) :
    ResidualEdgeResult G π T o := by
  have hprob : ((sampleResidualEdge kb kv π cache T).eval G.cut) o ≠ 0 := by
    simpa only [PMF.mem_support_iff] using ho
  by_cases hz : (G.contract π).internalMass T = 0
  · rw [sampleResidualEdge_zero G kb kv π cache hc T hz] at ho
    have he := (PMF.mem_support_pure_iff _ _).mp ho
    subst o
    exact hz
  · have hp := lt_of_le_of_ne ((G.contract π).internalMass_nonneg T) (Ne.symm hz)
    cases o with
    | none => exact (hprob (sampleResidualEdge_none G kb kv π cache hc T hB hV hp)).elim
    | some e =>
        induction e using Sym2.ind with
        | _ u v =>
          by_cases huv : u = v
          · subst v
            exact (hprob (sampleResidualEdge_diag G kb kv π cache hc T hB hV u)).elim
          · have hm : (if π u ∈ T ∧ π v ∈ T ∧ π u ≠ π v then
                ENNReal.ofReal (G.w u v) else 0) ≠ 0 := by
              rw [← sampleResidualEdge_scaled G kb kv π cache hc T hB hV huv]
              exact mul_ne_zero (ne_of_gt (ENNReal.ofReal_pos.mpr hp)) hprob
            have he : π u ∈ T ∧ π v ∈ T ∧ π u ≠ π v := by
              by_contra hh; simp [hh] at hm
            rw [ite_eq_left he] at hm
            exact ⟨u, v, rfl, he.1, he.2.1, he.2.2,
              lt_of_not_ge (fun hw => hm (ENNReal.ofReal_eq_zero.mpr hw))⟩

/-- Public worst-case budget after caching the block cuts. -/
def residualSampleBudget (V B : Type) [Fintype V] [Fintype B] : ℕ :=
  (2 * searchDepth B + 1) * 3 + 6 * (2 * searchDepth V + 1)

theorem residualSampleBudget_eq : residualSampleBudget V B =
    6 * searchDepth B + 12 * searchDepth V + 9 := by unfold residualSampleBudget; omega

/-- A complete sampler that obtains its own cache before observing the input graph. -/
def sampleResidualFresh (π : V → B) (T : Finset B) :
    RTree (Finset V) ℝ (Option (Sym2 V)) (Fintype.card B + residualSampleBudget V B) :=
  (RTree.ofDeterministic (cacheBlockCuts π)).bind fun cache =>
    sampleResidualEdge (searchDepth B) (searchDepth V) π cache T

theorem sampleResidualFresh_eval (G : WeightedGraph V) (π : V → B) (T : Finset B) :
    (sampleResidualFresh π T).eval G.cut =
      (sampleResidualEdge (searchDepth B) (searchDepth V) π
        (fun b => G.cut (fiber π b)) T).eval G.cut := by
  simp only [sampleResidualFresh, RTree.eval_bind, RTree.eval_ofDeterministic,
    DTree.eval, cacheBlockCuts_run, PMF.pure_bind]

theorem sampleResidualFresh_law (G : WeightedGraph V) (π : V → B) (T : Finset B)
    (hp : 0 < (G.contract π).internalMass T) {u v : V} (hne : u ≠ v) :
    ((sampleResidualFresh π T).eval G.cut) (some s(u, v)) =
      (if π u ∈ T ∧ π v ∈ T ∧ π u ≠ π v then ENNReal.ofReal (G.w u v) else 0) /
        ENNReal.ofReal ((G.contract π).internalMass T) := by
  rw [sampleResidualFresh_eval]
  exact sampleResidualEdge_law G _ _ π _ (fun _ => rfl) T
    (Nat.le_pow_clog (by decide) _) (Nat.le_pow_clog (by decide) _) hp hne

theorem sampleResidualFresh_correct (G : WeightedGraph V) (π : V → B) (T : Finset B)
    (o : Option (Sym2 V)) (ho : o ∈ ((sampleResidualFresh π T).eval G.cut).support) :
    ResidualEdgeResult G π T o := by
  rw [sampleResidualFresh_eval] at ho
  exact sampleResidualEdge_correct G _ _ π _ (fun _ => rfl) T
    (Nat.le_pow_clog (by decide) _) (Nat.le_pow_clog (by decide) _) o ho

/-- One fixed program works for every hidden weighted graph, with zero error. -/
theorem sampleResidualFresh_solves (π : V → B) (T : Finset B) :
    (sampleResidualFresh π T).SolvesWithError WeightedGraph.cut
      (fun G o => ResidualEdgeResult G π T o) 0 := by
  intro G
  have hm : ((sampleResidualFresh π T).eval G.cut).toOuterMeasure
      {o | ResidualEdgeResult G π T o} = 1 := by
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    exact fun o ho => sampleResidualFresh_correct G π T o ho
  rw [RTree.successProb_eq, hm]
  norm_num

end
end CutQueryComplexity
