import CutQueryComplexity.Sparsification.EstimationEvents

/-! # Actual query costs of the estimation run

The call log records the labeling, cache, region and scale of each call and the
number of group-cut queries after it. For the fixed hidden graph,
`callDraws` recomputes the number of residual draws of a call from the same
cached-mass formula the program uses. A call costs

```text
callCost = 1 + residualDrawCost·callDraws + groups,
```

and `runAcc` sums `callCost` over the log. `estStep_cost` proves that on every
supported execution, the actual number of queries of one step is at most the
increase of `runAcc`. `RTree.iterate_cost` then bounds the cost of the whole run by
`runAcc` of its final state. Bounding `runAcc` on good histories is a separate
charging argument.
-/

namespace CutQueryComplexity.WeightedGraph
noncomputable section
open scoped Classical
open Probability
variable {V : Type} [Fintype V]

/-- Draws of a logged call, recomputed from the hidden graph. -/
def callDraws (G : WeightedGraph V) (ρ : ℝ) (R : ℕ) (c : CallRecord V) : ℕ :=
  if cachedMass c.cache c.T (G.cut (pull c.π c.T)) < c.κ / 2 then 0
  else if ⌈ρ * cachedMass c.cache c.T (G.cut (pull c.π c.T)) / c.κ⌉₊ ≤ R then
    ⌈ρ * cachedMass c.cache c.T (G.cut (pull c.π c.T)) / c.κ⌉₊
  else 0

def callCost (G : WeightedGraph V) (ρ : ℝ) (R : ℕ) (c : CallRecord V) : ℕ :=
  1 + residualDrawCost (searchDepth V) (searchDepth V) * callDraws G ρ R c + c.groups

def runAcc (G : WeightedGraph V) (ρ : ℝ) (R : ℕ) (s : EstState V) : ℕ :=
  (s.calls.map (callCost G ρ R)).sum

/-! ### Run-level cost lemmas -/

theorem RTree.run_map' {I A O P : Type} {q : ℕ} (f : O → P) (T : RTree I A O q)
    (read : I → A) : RTree.run read (T.map f) = (RTree.run read T).map (fun p => (f p.1, p.2)) := by
  simp only [RTree.map, RTree.run_cast, RTree.run_bind, RTree.run_pure, PMF.pure_map,
    Nat.add_zero]
  rw [PMF.map, Function.comp_def]

theorem estimateCall_cost (G : WeightedGraph V) (kb kv : ℕ) (π : V → V) (cache : V → ℝ)
    (T : Finset V) {κ : ℝ} (hκ : 0 < κ) (ρ : ℝ) (R : ℕ) {p : Option (WeightedGraph V) × ℕ}
    (hp : p ∈ (RTree.run G.cut (estimateCall kb kv π cache T hκ ρ R)).support) :
    p.2 ≤ 1 + residualDrawCost kb kv * callDraws G ρ R ⟨π, cache, T, κ, 0⟩ := by
  rw [estimateCall, RTree.run_query] at hp
  obtain ⟨⟨o, c⟩, hoc, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
  simp only [callDraws]
  by_cases h1 : cachedMass cache T (G.cut (pull π T)) < κ / 2
  · simp only [h1, ↓reduceDIte, ↓reduceIte] at hoc ⊢
    rw [RTree.run_pure, PMF.pure_map, PMF.mem_support_pure_iff] at hoc
    cases hoc
    simp
  · by_cases h2 : ⌈ρ * cachedMass cache T (G.cut (pull π T)) / κ⌉₊ ≤ R
    · simp only [h1, h2, ↓reduceDIte, ↓reduceIte] at hoc ⊢
      rw [RTree.run_map', RTree.run_weaken] at hoc
      obtain ⟨⟨o', c'⟩, hoc', he⟩ := (PMF.mem_support_map_iff _ _ _).mp hoc
      simp only [Prod.mk.injEq] at he
      obtain ⟨-, rfl⟩ := he
      have := RTree.cost_le _ _ hoc'
      simp only at this ⊢
      rw [Nat.mul_comm] at this
      omega
    · simp only [h1, h2, ↓reduceDIte, ↓reduceIte] at hoc ⊢
      rw [RTree.run_pure, PMF.pure_map, PMF.mem_support_pure_iff] at hoc
      cases hoc
      simp

omit [Fintype V] in
theorem queryCuts_cost (read : Finset V → ℝ) (L : List (Finset V)) {p : (Finset V → ℝ) × ℕ}
    (hp : p ∈ (RTree.run read (queryCuts L)).support) : p.2 ≤ L.length :=
  RTree.cost_le _ _ hp

/-- **Cost of one step**, against the call log. -/
theorem estStep_cost (G H : WeightedGraph V) (ρ : ℝ) (R : ℕ) (s : EstState V)
    (p : EstState V × ℕ) (hp : p ∈ (RTree.run G.cut (estStep H ρ R s)).support) :
    runAcc G ρ R s + p.2 ≤ runAcc G ρ R p.1 := by
  unfold estStep at hp
  rcases hst : s.status with _ | _ | _ <;> rw [hst] at hp
  · rcases hpd : s.pending with _ | ⟨S, rest⟩ <;> rw [hpd] at hp
    · rw [RTree.run_pure, PMF.pure_map, PMF.mem_support_pure_iff] at hp
      subst hp
      simp only [Nat.add_zero, runAcc, boundary]
      split_ifs <;> rfl
    · split_ifs at hp with hκ
      · simp only [regionStep] at hp
        rw [RTree.run_bind] at hp
        obtain ⟨⟨o, c⟩, hoc, hp⟩ := (PMF.mem_support_bind_iff _ _ _).mp hp
        obtain ⟨⟨s', c'⟩, hsc, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
        have h1 := estimateCall_cost G _ _ s.π s.cache _ hκ ρ R hoc
        cases o with
        | none =>
            simp only [RTree.run_pure, PMF.pure_map, PMF.mem_support_pure_iff,
              Prod.mk.injEq] at hsc
            obtain ⟨rfl, rfl⟩ := hsc
            simp only [runAcc, List.map_append, List.sum_append, List.map_cons, List.map_nil,
              List.sum_cons, List.sum_nil, callCost]
            simp only [callDraws] at h1 ⊢
            omega
        | some X =>
            simp only [RTree.run_weaken, RTree.run_map'] at hsc
            obtain ⟨⟨g, c''⟩, hg, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hsc
            simp only [Prod.mk.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            have h2 := queryCuts_cost G.cut _ hg
            rw [List.length_map, Finset.length_toList] at h2
            simp only [runAcc, afterCall, List.map_append, List.sum_append, List.map_cons,
              List.map_nil, List.sum_cons, List.sum_nil, callCost]
            simp only [callDraws] at h1 ⊢
            omega
      · rw [RTree.run_pure, PMF.pure_map, PMF.mem_support_pure_iff] at hp
        subst hp
        simp [runAcc]
  · rw [RTree.run_pure, PMF.pure_map, PMF.mem_support_pure_iff] at hp
    subst hp
    simp
  · rw [RTree.run_pure, PMF.pure_map, PMF.mem_support_pure_iff] at hp
    subst hp
    simp

/-- **Cost of the whole run** is at most the accounting sum of its final state. -/
theorem estRun_cost (G H : WeightedGraph V) (ρ : ℝ) (R N : ℕ) (s : EstState V)
    {p : EstState V × ℕ} (hp : p ∈ (RTree.run G.cut (estRun H ρ R N s)).support) :
    runAcc G ρ R s + p.2 ≤ runAcc G ρ R p.1 :=
  RTree.iterate_cost (estStep H ρ R) G.cut (runAcc G ρ R) (estStep_cost G H ρ R) N s p hp

end
end CutQueryComplexity.WeightedGraph
