import CutQueryComplexity.Sparsification.KruskalInvariant
import CutQueryComplexity.Primitive.HeavyResidual

/-! # A deterministic approximate Kruskal forest from cut queries

Initialize the block cache once. Each iteration finds a heavy surviving
original edge, learns its weight with three cuts, and updates the merged block
cache with one cut. The public horizon is `n-1`; zero residual mass halts early.
The resulting explicit weighted forest estimates all pair strengths at once.
-/

namespace CutQueryComplexity
noncomputable section
open scoped Classical
open WeightedGraph
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {V : Type} [Fintype V] [DecidableEq V]

def kruskalStepBudget (V : Type) [Fintype V] : ℕ := 6 * (searchDepth V + 1) + 4

/-- Bounded merging with an explicit graph and observed block-cut cache. -/
def approxKruskalGrow : (steps : ℕ) → WeightedGraph V → (V → V) → (V → ℝ) →
    DTree (Finset V) ℝ (WeightedGraph V) (steps * kruskalStepBudget V)
  | 0, H, _, _ => DTree.pure H
  | steps + 1, H, π, cache =>
      ((findHeavyResidual (searchDepth V) π cache).bind fun answer => match answer with
        | none => DTree.pure H
        | some (u, v) => (edgeRecovery u v).bind fun weight =>
            (mergeBlockCache π {π u, π v} (π u) cache).bind fun cache' =>
              approxKruskalGrow steps (H.withEdge u v weight) (pairMerge π u v) cache').cast
                (by unfold kruskalStepBudget; ring)

theorem approxKruskalGrow_correct (G : WeightedGraph V) (steps : ℕ) (H : WeightedGraph V)
    (π : V → V) (cache : V → ℝ) (hc : ∀ b, cache b = G.cut (fiber π b))
    (h : KruskalInvariant G H π) (hbudget : (liveBlocks π).card ≤ steps + 1) :
    IsApproxKruskalForest G ((approxKruskalGrow steps H π cache).eval G.cut) := by
  induction steps generalizing H π cache with
  | zero =>
      simpa only [approxKruskalGrow, DTree.eval_pure] using h.finish_one_block hbudget
  | succ steps ih =>
      have hsearch := findHeavyResidual_correct G (searchDepth V) π cache hc
        (Nat.le_pow_clog (by decide) _)
      rw [approxKruskalGrow, DTree.eval_cast, DTree.eval_bind]
      cases he : (findHeavyResidual (searchDepth V) π cache).eval G.cut with
      | none =>
          have hz : (G.contract π).internalMass Finset.univ = 0 := by
            simpa only [he, HeavyResidualResult] using hsearch
          simpa only [DTree.eval_pure] using h.finish_zero hz
      | some edge =>
          rcases edge with ⟨u, v⟩
          have hp : π u ≠ π v ∧ 0 < G.w u v ∧
              2 * (G.contract π).internalMass Finset.univ ≤
                (Fintype.card V : ℝ) ^ 2 * G.w u v := by
            simpa only [he, HeavyResidualResult] using hsearch
          have huv : u ≠ v := fun heq => hp.1 (congrArg π heq)
          have hw : (edgeRecovery u v).eval G.cut = G.w u v :=
            congrArg Prod.fst (edgeRecovery_run G huv)
          have hcache : (mergeBlockCache π {π u, π v} (π u) cache).eval G.cut =
              (fun b => G.cut (fiber (pairMerge π u v) b)) := by
            rw [DTree.eval, mergeBlockCache_run G π {π u, π v} (by simp) cache hc]
            rfl
          rw [DTree.eval_bind, hw, DTree.eval_bind, hcache]
          apply ih _ _ _ (fun _ => rfl) (h.merge hp.1 hp.2.1 hp.2.2)
          have hdec := (isBlockMerge_pair π hp.1).card_lt
          omega

/-- Cache initialization, followed by at most `n-1` search/recovery/merge rounds. -/
def approxKruskalBudget (V : Type) [Fintype V] : ℕ :=
  Fintype.card V + (Fintype.card V - 1) * kruskalStepBudget V

theorem approxKruskalBudget_le :
    approxKruskalBudget V ≤ Fintype.card V * (6 * searchDepth V + 11) := by
  calc
    _ ≤ Fintype.card V + Fintype.card V * kruskalStepBudget V :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) _
    _ = _ := by unfold kruskalStepBudget; ring

def approxKruskal : DTree (Finset V) ℝ (WeightedGraph V) (approxKruskalBudget V) :=
  (cacheBlockCuts (id : V → V)).bind fun cache =>
    approxKruskalGrow (Fintype.card V - 1) 0 id cache

theorem approxKruskal_eval (G : WeightedGraph V) :
    (approxKruskal (V := V)).eval G.cut =
      (approxKruskalGrow (Fintype.card V - 1) 0 id
        (fun b => G.cut (fiber id b))).eval G.cut := by
  simp only [approxKruskal, DTree.eval, DTree.run_bind, cacheBlockCuts_run]

theorem approxKruskal_correct (G : WeightedGraph V) :
    IsApproxKruskalForest G (approxKruskal.eval G.cut) := by
  rw [approxKruskal_eval]
  apply approxKruskalGrow_correct G _ _ _ _ (fun _ => rfl) (kruskalInvariant_initial G)
  have := card_liveBlocks_le (id : V → V)
  omega

/-- The program is chosen before quantifying over the hidden weighted graph. -/
theorem approxKruskal_solves :
    (approxKruskal (V := V)).Solves WeightedGraph.cut IsApproxKruskalForest :=
  approxKruskal_correct

theorem approxKruskal_query_bound (G : WeightedGraph V) :
    (approxKruskal (V := V)).cost G.cut ≤
      Fintype.card V + (Fintype.card V - 1) * (6 * (searchDepth V + 1) + 4) :=
  approxKruskal.cost_le G.cut

theorem approxKruskal_pair_bounds (G : WeightedGraph V) (u v : V) :
    (approxKruskal.eval G.cut).bottleneck u v ≤ G.strength u v ∧
      G.strength u v ≤ ((Fintype.card V : ℝ) ^ 2 / 2) *
        (approxKruskal.eval G.cut).bottleneck u v :=
  (approxKruskal_correct G).bottleneck_bounds u v

theorem approxKruskal_edge_bound (G : WeightedGraph V) :
    (approxKruskal.eval G.cut).edgeCount ≤ Fintype.card V - 1 :=
  (approxKruskal_correct G).edge_bound

end
end CutQueryComplexity
