import CutQueryComplexity.Graph.Mass
import CutQueryComplexity.Primitive.Reductions
import CutQueryComplexity.Primitive.Learn

/-! # Cached cuts and residual mass

A public map `π` records contraction blocks. Edges keep their original
endpoints; only edges internal to one block disappear. The original cut of
each block can be cached. The residual mass of a union of blocks then costs
one new cut query, independently of the number of blocks and of the weights.
-/

namespace CutQueryComplexity

noncomputable section
open scoped Classical
variable {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]

namespace WeightedGraph

/-- Delete edges already internal to a contraction block, retaining original endpoints. -/
def residual (G : WeightedGraph V) (π : V → B) : WeightedGraph V where
  w u v := if π u = π v then 0 else G.w u v
  symm u v := by simp only [eq_comm, G.symm u v]
  nonneg u v := by split <;> simp [G.nonneg]
  diag v := by simp

theorem residual_subgraph (G : WeightedGraph V) (π : V → B) :
    (G.residual π).IsSubgraph G := by
  intro u v
  change (if π u = π v then 0 else G.w u v) ≤ G.w u v
  split <;> simp [G.nonneg]

/-- A quotient singleton cut is the original block cut, also for empty fibers. -/
theorem degree_contract (G : WeightedGraph V) (π : V → B) (b : B) :
    (G.contract π).degree b = G.cut (fiber π b) := by
  rw [← cut_singleton, cut_contract]
  rfl

/-- The sum of cached block cuts counts each residual internal edge twice. -/
theorem residual_mass_formula (G : WeightedGraph V) (π : V → B) (T : Finset B) :
    (G.contract π).internalMass T =
      ((∑ b ∈ T, G.cut (fiber π b)) - G.cut (pull π T)) / 2 := by
  have h := (G.contract π).cut_add_internal T
  simp only [cut_contract, degree_contract] at h
  unfold internalMass cross
  linarith

/-- Contracting and retaining original residual edge identities give the same mass. -/
theorem residual_internalMass (G : WeightedGraph V) (π : V → B) (T : Finset B) :
    (G.residual π).internalMass (pull π T) = (G.contract π).internalMass T := by
  have hf : (G.residual π).contract π = G.contract π := by
    ext b c
    change (if b = c then 0 else _) = (if b = c then 0 else _)
    split_ifs with h
    · rfl
    · apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      have hu' := (mem_fiber π b u).mp hu
      have hv' := (mem_fiber π c v).mp hv
      simp [residual, hu', hv', h]
  have hdiag (b : B) : (G.residual π).cross (fiber π b) (fiber π b) = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    apply Finset.sum_eq_zero
    intro v hv
    simp [residual, (mem_fiber π b u).mp hu, (mem_fiber π b v).mp hv]
  rw [← hf]
  unfold internalMass
  congr 1
  rw [← cross_fibers]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  change _ = if b = c then 0 else _
  split_ifs with h
  · subst c; exact hdiag b
  · rfl

/-- Residual edge mass splits into two internal masses and the original cross mass. -/
theorem residual_mass_split (G : WeightedGraph V) (π : V → B)
    {S T : Finset B} (h : Disjoint S T) :
    (G.contract π).internalMass (S ∪ T) =
      (G.contract π).internalMass S + (G.contract π).internalMass T +
        G.cross (pull π S) (pull π T) := by
  rw [internalMass_union _ h, ← cross_fibers]
  congr 1
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  have hne : b ≠ c := by intro he; exact Finset.disjoint_left.mp h hb (he ▸ hc)
  simp [contract, hne]

end WeightedGraph

/-- Cache all block cuts with one original query per public block label. In
particular, the initial singleton partition uses exactly `card V` queries. -/
def cacheBlockCuts (π : V → B) : DTree (Finset V) ℝ (B → ℝ) (Fintype.card B) :=
  DTree.queryAll (WeightedGraph.fiber π) (fun _ => 0)

theorem cacheBlockCuts_run (G : WeightedGraph V) (π : V → B) :
    (cacheBlockCuts π).run G.cut =
      ((fun b => G.cut (WeightedGraph.fiber π b)), Fintype.card B) :=
  DTree.queryAll_run _ _ _

/-- With the block cuts cached, one query recovers residual internal mass. The
program depends only on public blocks and observed cached answers. -/
def residualMassQuery (π : V → B) (cache : B → ℝ) (T : Finset B) :
    DTree (Finset V) ℝ ℝ 1 :=
  DTree.query (WeightedGraph.pull π T) fun a => DTree.pure ((∑ b ∈ T, cache b) - a) |>.map
    (fun x => x / 2)

theorem residualMassQuery_run (G : WeightedGraph V) (π : V → B) (cache : B → ℝ)
    (hcache : ∀ b, cache b = G.cut (WeightedGraph.fiber π b)) (T : Finset B) :
    (residualMassQuery π cache T).run G.cut = ((G.contract π).internalMass T, 1) := by
  simp only [residualMassQuery, DTree.run_map, DTree.run_query, DTree.run_pure,
    hcache, WeightedGraph.residual_mass_formula]

theorem residualMassQuery_eval (G : WeightedGraph V) (π : V → B) (cache : B → ℝ)
    (hcache : ∀ b, cache b = G.cut (WeightedGraph.fiber π b)) (T : Finset B) :
    (residualMassQuery π cache T).eval G.cut = (G.contract π).internalMass T := by
  rw [DTree.eval, residualMassQuery_run G π cache hcache]

end
end CutQueryComplexity
