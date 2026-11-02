import CutQueryComplexity.Sparsification.OutputEdges
import CutQueryComplexity.Sparsification.ApproxKruskal
import CutQueryComplexity.Probability.Truncation

/-! # Weighted cut sparsification with a hard query cap

The algorithm, chosen before the hidden graph:

1. `approxKruskal` builds the approximate maximum spanning forest `H`, and
   `cacheBlockCuts id` reads the singleton cuts. Both are deterministic.
2. `estRun` runs the adaptive estimation with fixed fuel.
3. If the run finished, `outRun` samples the output from the recorded events.
4. The whole program is truncated at the public budget `Q`.

`sparsify_correct` proves, for every nonnegative real-weighted graph `G`:

```text
Pr[output is a 1±ε cut sparsifier of G] ≥ 1 − N·callFailure − (n−1)δ,
```

with no weight-ratio, integrality, or connectivity assumption. The cap `Q` is
chosen so that it never binds on a successful history: there the actual number of
queries is at most the forest budget plus `n`, plus the estimation budget of
`runAcc_le`, plus the output budget of `outDraws_total_le`.
-/

namespace CutQueryComplexity.WeightedGraph
noncomputable section
open scoped Classical ENNReal
open Probability
variable {V : Type} [Fintype V]

/-! ### Parameters -/

/-- Fuel for the estimation run, at least the initial potential. -/
def fuelBound (V : Type) [Fintype V] : ℕ :=
  1 + (Fintype.card V + 1) * ((Fintype.card V + 1) * potWidth V)

theorem runPot_init_le (H : WeightedGraph V) (cache : V → ℝ) :
    runPot H (initState H cache) ≤ fuelBound V := by
  simp only [runPot, initState, ↓reduceIte, List.length_nil, Nat.add_zero, fuelBound]
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  unfold batchPot
  have hL : (liveLabels (id : V → V)).card ≤ Fintype.card V := Finset.card_le_univ _
  have hm := min_le_right (scaleLevel H (id : V → V) (initScale H)) (potWidth V - 1)
  have hK : 2 ≤ potWidth V := by simp [potWidth]
  have : ((liveLabels (id : V → V)).card - 1) * potWidth V ≤ (Fintype.card V - 1) * potWidth V :=
    Nat.mul_le_mul_right _ (Nat.sub_le_sub_right hL 1)
  have h1 : (Fintype.card V - 1) * potWidth V ≤ Fintype.card V * potWidth V :=
    Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have h2 : (Fintype.card V + 1) * potWidth V = Fintype.card V * potWidth V + potWidth V :=
    Nat.succ_mul _ _
  omega

/-! ### The program -/

/-- Forest and singleton cuts, deterministically. -/
def preProgram : DTree (Finset V) ℝ (WeightedGraph V × (V → ℝ))
    (approxKruskalBudget V + Fintype.card V) :=
  (approxKruskal (V := V)).bind fun H => (cacheBlockCuts (id : V → V)).map fun cache => (H, cache)

theorem preProgram_run (G : WeightedGraph V) :
    (preProgram (V := V)).run G.cut =
      ((approxKruskal.eval G.cut, fun b => G.cut (fiber (id : V → V) b)),
        approxKruskal.cost G.cut + Fintype.card V) := by
  simp only [preProgram, DTree.run_bind, DTree.run_map, cacheBlockCuts_run]

/-- The output stage after the estimation run. -/
def outStage (c : ℝ) (R₂ : ℕ) (s : EstState V) :
    RTree (Finset V) ℝ (Option (WeightedGraph V)) (Fintype.card V * outStepBudget V R₂) :=
  if h : s.status = .done ∧ s.events.length ≤ Fintype.card V then
    (outRun c R₂ s.events).weaken (Nat.mul_le_mul_right _ h.2)
  else RTree.pure (PMF.pure none)

abbrev coreBudget (V : Type) [Fintype V] (R R₂ : ℕ) : ℕ :=
  (approxKruskalBudget V + Fintype.card V) +
    (fuelBound V * estStepBudget V R + Fintype.card V * outStepBudget V R₂)

/-- The untruncated algorithm, reporting the forest, the final state, and the output. -/
def sparsifyCore (ρ c : ℝ) (R R₂ : ℕ) :
    RTree (Finset V) ℝ (WeightedGraph V × EstState V × Option (WeightedGraph V))
      (coreBudget V R R₂) :=
  (RTree.ofDeterministic (preProgram (V := V))).bind fun hc =>
    (estRun hc.1 ρ R (fuelBound V) (initState hc.1 hc.2)).bind fun s =>
      (outStage c R₂ s).map fun o => (hc.1, s, o)

/-- **The algorithm**: the core program under the hard cap `Q`. -/
def sparsify (ρ c : ℝ) (R R₂ Q : ℕ) : RTree (Finset V) ℝ (Option (WeightedGraph V)) Q :=
  ((sparsifyCore ρ c R R₂).truncate Q).map fun t => t.bind fun p => p.2.2


/-! ### Semantics of the core -/

theorem preProgram_eval (G : WeightedGraph V) :
    (preProgram (V := V)).eval G.cut =
      (approxKruskal.eval G.cut, fun b => G.cut (fiber (id : V → V) b)) := by
  simp only [DTree.eval, preProgram_run]

theorem sparsifyCore_eval (G : WeightedGraph V) (ρ c : ℝ) (R R₂ : ℕ) :
    (sparsifyCore ρ c R R₂).eval G.cut =
      ((estRun (approxKruskal.eval G.cut) ρ R (fuelBound V)
        (initState (approxKruskal.eval G.cut) fun b => G.cut (fiber (id : V → V) b))).eval
          G.cut).bind fun s =>
        ((outStage c R₂ s).eval G.cut).map fun o => (approxKruskal.eval G.cut, s, o) := by
  rw [sparsifyCore, RTree.eval_bind, RTree.eval_ofDeterministic, PMF.pure_bind, preProgram_eval]
  simp only [RTree.eval_bind, RTree.eval_map]

/-- The good outcome of the core: a successful estimation run and a sparsifier. -/
def CoreGood (G : WeightedGraph V) (ε : ℝ) (t : WeightedGraph V × EstState V ×
    Option (WeightedGraph V)) : Prop :=
  IsApproxKruskalForest G t.1 ∧ EstSuccess' G t.1 t.2.1 ∧
    ∃ X, t.2.2 = some X ∧ IsCutSparsifier ε G X

/-- **Success of the core program.** -/
theorem sparsifyCore_success (G : WeightedGraph V) {ρ c ε δ δ₀ : ℝ} (hρ : 0 < ρ) {R : ℕ}
    (hR : ρ * (Fintype.card V : ℝ) ^ 2 ≤ R) (hδ₀ : 0 ≤ δ₀) (hδ₀2 : δ₀ ≤ 2)
    (hexp : ((2 * Fintype.card V : ℕ) : ℝ) ^ 2 * Real.exp (-(ρ / 128)) ≤ δ₀ / 4)
    (hc : 0 < c) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ2 : δ ≤ 2)
    (hlog : 8 * (2 * Real.log (2 * Fintype.card V) + Real.log (4 / δ)) ≤ ε ^ 2 * c) :
    Probability.mass ((sparsifyCore ρ c R ⌈2 * c * (Fintype.card V : ℝ) ^ 2⌉₊).eval G.cut)
      (fun t => ¬CoreGood G ε t) ≤
        fuelBound V * callFailure V ρ δ₀ + ENNReal.ofReal ((Fintype.card V - 1 : ℕ) * δ) := by
  have hH := approxKruskal_correct G
  rw [sparsifyCore_eval]
  apply mass_bind_le_add _ _ (fun s => ¬EstSuccess' G (approxKruskal.eval G.cut) s)
  · exact estRun_correct' hH hρ hR hδ₀ hδ₀2 hexp (fun _ => rfl) (runPot_init_le _ _)
  · intro s hs
    have hs' : EstSuccess' G (approxKruskal.eval G.cut) s := not_not.mp hs
    have hlen : s.events.length ≤ Fintype.card V :=
      (Nat.le_add_right _ _).trans hs'.1.2.1.length
    have hout : (outStage c ⌈2 * c * (Fintype.card V : ℝ) ^ 2⌉₊ s).eval G.cut =
        (outRun c ⌈2 * c * (Fintype.card V : ℝ) ^ 2⌉₊ s.events).eval G.cut := by
      simp only [outStage, hs'.1.2.2, hlen, and_self, ↓reduceDIte, RTree.eval_weaken]
    rw [hout, mass_map]
    have hsp := outRun_sparsifier hH hs'.1 hc hε hε1 hδ hδ2 hlog
    refine le_trans (mass_mono _ (fun o hbad => ?_))
      (failure_le_of_success _ _ (by positivity) hsp)
    intro hgood
    exact hbad ⟨hH, hs', hgood⟩

/-! ### Cost of the core -/

/-- Budget of the estimation phase on a successful run. -/
def estBound (V : Type) [Fintype V] (ρ : ℝ) : ℝ :=
  2 * (Fintype.card V - 1 : ℕ) * Nat.log 2 (2 * Fintype.card V ^ 4) +
    residualDrawCost (searchDepth V) (searchDepth V) * (8 * ρ * (Fintype.card V - 1 : ℕ)) +
      Fintype.card V

/-- Budget of the output phase on a successful run. -/
def outBound (V : Type) [Fintype V] (c : ℝ) : ℝ :=
  Fintype.card V + residualDrawCost (searchDepth V) (searchDepth V) *
    (4 * c * (Fintype.card V - 1 : ℕ) + Fintype.card V)

/-- The public hard cap. -/
def capQ (V : Type) [Fintype V] (ρ c : ℝ) : ℕ :=
  approxKruskalBudget V + Fintype.card V + ⌈estBound V ρ⌉₊ + ⌈outBound V c⌉₊

theorem sparsifyCore_cost (G : WeightedGraph V) (ρ c : ℝ) (R R₂ : ℕ)
    {p : (WeightedGraph V × EstState V × Option (WeightedGraph V)) × ℕ}
    (hp : p ∈ (RTree.run G.cut (sparsifyCore ρ c R R₂)).support) :
    p.2 ≤ approxKruskalBudget V + Fintype.card V + runAcc G ρ R p.1.2.1 +
      outAcc G c R₂ p.1.2.1.events := by
  rw [sparsifyCore] at hp
  obtain ⟨hc, k₁, hk₁, k₂, hp, he⟩ := RTree.mem_support_run_bind _ _ G.cut hp
  rw [RTree.run_ofDeterministic, PMF.mem_support_pure_iff, preProgram_run] at hk₁
  simp only [Prod.mk.injEq] at hk₁
  obtain ⟨rfl, rfl⟩ := hk₁
  obtain ⟨s, k₃, hk₃, k₄, hp4, he2⟩ := RTree.mem_support_run_bind _ _ G.cut hp
  have hest := estRun_cost G _ ρ R (fuelBound V) _ hk₃
  have hinit : runAcc G ρ R (initState (approxKruskal.eval G.cut)
      fun b => G.cut (fiber (id : V → V) b)) = 0 := by simp [runAcc, initState]
  rw [hinit, Nat.zero_add] at hest
  rw [RTree.run_map'] at hp4
  obtain ⟨⟨o, k₅⟩, hk₅, he3⟩ := (PMF.mem_support_map_iff _ _ _).mp hp4
  simp only [Prod.mk.injEq] at he3
  obtain ⟨hp1, rfl⟩ := he3
  have hkr := DTree.cost_le approxKruskal G.cut
  have hout : k₅ ≤ outAcc G c R₂ s.events := by
    unfold outStage at hk₅
    split_ifs at hk₅ with hdone
    · rw [RTree.run_weaken] at hk₅
      exact outRun_cost G c R₂ s.events hk₅
    · rw [RTree.run_pure, PMF.pure_map, PMF.mem_support_pure_iff] at hk₅
      simp only [Prod.mk.injEq] at hk₅
      rw [hk₅.2]
      exact Nat.zero_le _
  rw [← hp1]
  simp only [DTree.cost] at hkr he
  simp only at he he2 hest ⊢
  unfold approxKruskalBudget at *
  omega


theorem outAcc_cast (G : WeightedGraph V) (c : ℝ) (R₂ : ℕ) (L : List (MergeEvent V)) :
    (outAcc G c R₂ L : ℝ) = L.length + residualDrawCost (searchDepth V) (searchDepth V) *
      ((L.map (eventCount G c R₂)).sum : ℝ) := by
  induction L with
  | nil => simp [outAcc]
  | cons e L ih =>
      simp only [outAcc, List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_mul,
        List.length_cons, Nat.cast_succ] at ih ⊢
      rw [ih]
      push_cast
      ring

/-- **The cap never binds on a good outcome.** -/
theorem coreGood_cost_le (G : WeightedGraph V) {ρ c ε : ℝ} (hρ : 2 ≤ ρ) (hc : 0 < c) (R : ℕ)
    {t : WeightedGraph V × EstState V × Option (WeightedGraph V)} (hg : CoreGood G ε t) :
    approxKruskalBudget V + Fintype.card V + runAcc G ρ R t.2.1 +
      outAcc G c ⌈2 * c * (Fintype.card V : ℝ) ^ 2⌉₊ t.2.1.events ≤ capQ V ρ c := by
  obtain ⟨hH, hs, -⟩ := hg
  have h1 : runAcc G ρ R t.2.1 ≤ ⌈estBound V ρ⌉₊ := by
    have := runAcc_le hH hs hρ R
    have h' : (runAcc G ρ R t.2.1 : ℝ) ≤ ⌈estBound V ρ⌉₊ :=
      this.trans (by rw [estBound]; exact Nat.le_ceil _)
    exact_mod_cast h'
  have h2 : outAcc G c ⌈2 * c * (Fintype.card V : ℝ) ^ 2⌉₊ t.2.1.events ≤ ⌈outBound V c⌉₊ := by
    have hd := outDraws_total_le hs.1 hc ⌈2 * c * (Fintype.card V : ℝ) ^ 2⌉₊
    have hlen : (t.2.1.events.length : ℝ) ≤ Fintype.card V := by
      exact_mod_cast (Nat.le_add_right _ _).trans hs.1.2.1.length
    have hcost : (0 : ℝ) ≤ residualDrawCost (searchDepth V) (searchDepth V) := by positivity
    have : (outAcc G c ⌈2 * c * (Fintype.card V : ℝ) ^ 2⌉₊ t.2.1.events : ℝ) ≤ outBound V c := by
      rw [outAcc_cast, outBound]
      nlinarith [mul_le_mul_of_nonneg_left hd hcost]
    exact_mod_cast this.trans (Nat.le_ceil _)
  unfold capQ
  omega

/-! ### The headline theorem -/

/-- **Weighted cut sparsification with a hard query cap.** For every nonnegative
real-weighted graph, the capped algorithm outputs a `1 ± ε` cut sparsifier except
with probability at most `fuelBound·callFailure + (n−1)δ`. -/
theorem sparsify_correct (G : WeightedGraph V) {ρ c ε δ δ₀ : ℝ} (hρ : 2 ≤ ρ) {R : ℕ}
    (hR : ρ * (Fintype.card V : ℝ) ^ 2 ≤ R) (hδ₀ : 0 ≤ δ₀) (hδ₀2 : δ₀ ≤ 2)
    (hexp : ((2 * Fintype.card V : ℕ) : ℝ) ^ 2 * Real.exp (-(ρ / 128)) ≤ δ₀ / 4)
    (hc : 0 < c) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ2 : δ ≤ 2)
    (hlog : 8 * (2 * Real.log (2 * Fintype.card V) + Real.log (4 / δ)) ≤ ε ^ 2 * c) :
    Probability.mass
      ((sparsify ρ c R ⌈2 * c * (Fintype.card V : ℝ) ^ 2⌉₊ (capQ V ρ c)).eval G.cut)
      (fun o => ¬∃ X, o = some X ∧ IsCutSparsifier ε G X) ≤
        fuelBound V * callFailure V ρ δ₀ + ENNReal.ofReal ((Fintype.card V - 1 : ℕ) * δ) := by
  unfold sparsify
  rw [RTree.eval_map, RTree.eval_truncate, PMF.map_comp, mass_map]
  have hcore := sparsifyCore_success G (by linarith : (0 : ℝ) < ρ) hR hδ₀ hδ₀2 hexp hc hε hε1
    hδ hδ2 hlog
  rw [RTree.eval, mass_map] at hcore
  refine le_trans (mass_mono_on_support _ (fun p hp hbad => ?_)) hcore
  intro hgood
  apply hbad
  have hcost := sparsifyCore_cost G ρ c R _ hp
  have hcap := coreGood_cost_le G hρ hc R hgood
  obtain ⟨-, -, X, hX, hsp⟩ := hgood
  refine ⟨X, ?_, hsp⟩
  simp only [Function.comp_apply, show p.2 ≤ capQ V ρ c by omega, ↓reduceIte, Option.bind_some]
  exact hX


/-! ### The sparse headline -/

/-- Edge bound of the output. -/
def edgeBound (V : Type) [Fintype V] (c : ℝ) : ℕ :=
  ⌊4 * c * (Fintype.card V - 1 : ℕ) + Fintype.card V⌋₊

def CoreGoodSparse (G : WeightedGraph V) (ε c : ℝ)
    (t : WeightedGraph V × EstState V × Option (WeightedGraph V)) : Prop :=
  IsApproxKruskalForest G t.1 ∧ EstSuccess' G t.1 t.2.1 ∧
    ∃ X, t.2.2 = some X ∧ IsSparseCutSparsifier ε (edgeBound V c) G X

theorem sparsifyCore_success_sparse (G : WeightedGraph V) {ρ c ε δ δ₀ : ℝ} (hρ : 0 < ρ) {R : ℕ}
    (hR : ρ * (Fintype.card V : ℝ) ^ 2 ≤ R) (hδ₀ : 0 ≤ δ₀) (hδ₀2 : δ₀ ≤ 2)
    (hexp : ((2 * Fintype.card V : ℕ) : ℝ) ^ 2 * Real.exp (-(ρ / 128)) ≤ δ₀ / 4)
    (hc : 0 < c) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ2 : δ ≤ 2)
    (hlog : 8 * (2 * Real.log (2 * Fintype.card V) + Real.log (4 / δ)) ≤ ε ^ 2 * c) :
    Probability.mass ((sparsifyCore ρ c R ⌈2 * c * (Fintype.card V : ℝ) ^ 2⌉₊).eval G.cut)
      (fun t => ¬CoreGoodSparse G ε c t) ≤
        fuelBound V * callFailure V ρ δ₀ + ENNReal.ofReal ((Fintype.card V - 1 : ℕ) * δ) := by
  have hH := approxKruskal_correct G
  rw [sparsifyCore_eval]
  apply mass_bind_le_add _ _ (fun s => ¬EstSuccess' G (approxKruskal.eval G.cut) s)
  · exact estRun_correct' hH hρ hR hδ₀ hδ₀2 hexp (fun _ => rfl) (runPot_init_le _ _)
  · intro s hs
    have hs' : EstSuccess' G (approxKruskal.eval G.cut) s := not_not.mp hs
    have hlen : s.events.length ≤ Fintype.card V :=
      (Nat.le_add_right _ _).trans hs'.1.2.1.length
    have hout : (outStage c ⌈2 * c * (Fintype.card V : ℝ) ^ 2⌉₊ s).eval G.cut =
        (outRun c ⌈2 * c * (Fintype.card V : ℝ) ^ 2⌉₊ s.events).eval G.cut := by
      simp only [outStage, hs'.1.2.2, hlen, and_self, ↓reduceDIte, RTree.eval_weaken]
    rw [hout, mass_map]
    refine le_trans (mass_mono _ (fun o hbad => ?_))
      (outRun_sparse hH hs'.1 hc hε hε1 hδ hδ2 hlog)
    intro hgood
    exact hbad ⟨hH, hs', hgood⟩

/-- **Sparse weighted cut sparsification with a hard query cap.** The output is a
`1 ± ε` cut sparsifier with at most `⌊4c(n−1) + n⌋` edges, except with probability at
most `fuelBound·callFailure + (n−1)δ`. -/
theorem sparsify_sparse (G : WeightedGraph V) {ρ c ε δ δ₀ : ℝ} (hρ : 2 ≤ ρ) {R : ℕ}
    (hR : ρ * (Fintype.card V : ℝ) ^ 2 ≤ R) (hδ₀ : 0 ≤ δ₀) (hδ₀2 : δ₀ ≤ 2)
    (hexp : ((2 * Fintype.card V : ℕ) : ℝ) ^ 2 * Real.exp (-(ρ / 128)) ≤ δ₀ / 4)
    (hc : 0 < c) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ2 : δ ≤ 2)
    (hlog : 8 * (2 * Real.log (2 * Fintype.card V) + Real.log (4 / δ)) ≤ ε ^ 2 * c) :
    Probability.mass
      ((sparsify ρ c R ⌈2 * c * (Fintype.card V : ℝ) ^ 2⌉₊ (capQ V ρ c)).eval G.cut)
      (fun o => ¬∃ X, o = some X ∧ IsSparseCutSparsifier ε (edgeBound V c) G X) ≤
        fuelBound V * callFailure V ρ δ₀ + ENNReal.ofReal ((Fintype.card V - 1 : ℕ) * δ) := by
  unfold sparsify
  rw [RTree.eval_map, RTree.eval_truncate, PMF.map_comp, mass_map]
  have hcore := sparsifyCore_success_sparse G (by linarith : (0 : ℝ) < ρ) hR hδ₀ hδ₀2 hexp hc
    hε hε1 hδ hδ2 hlog
  rw [RTree.eval, mass_map] at hcore
  refine le_trans (mass_mono_on_support _ (fun p hp hbad => ?_)) hcore
  intro hgood
  apply hbad
  have hcost := sparsifyCore_cost G ρ c R _ hp
  have hcap := coreGood_cost_le (ε := ε) G hρ hc R
    ⟨hgood.1, hgood.2.1, by
      obtain ⟨X, hX, hsp⟩ := hgood.2.2
      exact ⟨X, hX, hsp.1⟩⟩
  obtain ⟨-, -, X, hX, hsp⟩ := hgood
  refine ⟨X, ?_, hsp⟩
  simp only [Function.comp_apply, show p.2 ≤ capQ V ρ c by omega, ↓reduceIte, Option.bind_some]
  exact hX

end
end CutQueryComplexity.WeightedGraph
