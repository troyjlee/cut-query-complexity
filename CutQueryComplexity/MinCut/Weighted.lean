import CutQueryComplexity.MinCut.Search
import CutQueryComplexity.TwoRespecting.ProgInterface
import CutQueryComplexity.MinCut.TreePacking
import CutQueryComplexity.Model.Iterate
import CutQueryComplexity.Sparsification.WeightedParams
import CutQueryComplexity.Probability.Expectation

/-! # Randomized weighted minimum cut

The algorithm `weightedMinCut hn s k`:

1. Sparsify `G` with `ε = 1/16` (`sparsify_whp`); stop if this fails.
2. Let `S₀` be a minimum cut of `H` (free: `H` is explicit). If `cut_H(S₀) = 0`,
   output `S₀`; it is also a zero cut of `G`.
3. Otherwise fix the tree distribution of `exists_tree_pmf` for `H`, and run `k`
   rounds. Each round samples a tree, runs the deterministic 2-respecting search
   `TwoRespecting.twoRespectingProg T` compiled to a query tree, and keeps the
   best result.
4. Output the best shore.

A minimum cut `C` of `G` has `cut_H(C) ≤ (17/15)·λ_H`, so a sampled tree crosses
`C` at least three times with probability at most `34/45`. Each round keeps the
result sound, and once the best value reaches `λ_G` it stays there, so all `k`
rounds fail with probability at most `(34/45)^k` (`iterate_fail_pow`).

`weightedMinCut_correct`: the output is a minimum cut of `G` except with
probability at most `(2n+2)^{-s} + (34/45)^k`. The worst-case budget is the
sparsifier budget plus `k` times `72n(⌈log₂ n⌉ + 1)`.
-/

namespace CutQueryComplexity
namespace WeightedMinCut

noncomputable section
open scoped Classical ENNReal
open Probability CutSearch

/-! ### Repeated rounds -/

section Geom
variable {I A S : Type} {b : ℕ}

theorem mass_eq_zero_of_support {α : Type} (p : PMF α) {P : α → Prop}
    (h : ∀ x ∈ p.support, ¬P x) : mass p P = 0 := by
  rw [mass_eq_tsum]
  refine ENNReal.tsum_eq_zero.mpr fun x => ?_
  split_ifs with hx
  · by_contra hne
    exact h x ((PMF.mem_support_iff _ _).mpr hne) hx
  · rfl

/-- **Geometric failure.** If every round keeps the state sound, keeps success once
reached, and succeeds with probability at least `1 − q` from any sound state, then
`N` rounds from a failed state all fail with probability at most `q^N`. -/
theorem iterate_fail_pow (step : S → RTree I A S b) (read : I → A) (Ok Good : S → Prop)
    (q : ℝ≥0∞)
    (hok : ∀ s, Ok s → ∀ s' ∈ ((step s).eval read).support, Ok s')
    (hkeep : ∀ s, Ok s → Good s → ∀ s' ∈ ((step s).eval read).support, Good s')
    (hstep : ∀ s, Ok s → mass ((step s).eval read) (fun s' => ¬Good s') ≤ q) :
    ∀ N s, Ok s → mass ((RTree.iterate step N s).eval read) (fun s' => ¬(Ok s' ∧ Good s')) ≤
      if Good s then 0 else q ^ N := by
  intro N
  induction N with
  | zero =>
      intro s hs
      simp only [RTree.eval_iterate_zero, mass_pure]
      split_ifs <;> simp_all
  | succ N ih =>
      intro s hs
      rw [RTree.eval_iterate_succ, mass_bind]
      change expect ((step s).eval read)
        (fun s' => mass ((RTree.iterate step N s').eval read) (fun s' => ¬(Ok s' ∧ Good s'))) ≤ _
      calc _ ≤ expect ((step s).eval read) (fun s' => if Good s' then 0 else q ^ N) :=
            expect_mono_on_support _ fun s' hs' => ih s' (hok s hs s' hs')
        _ = q ^ N * mass ((step s).eval read) (fun s' => ¬Good s') := by
            rw [← expect_indicator]
            congr 1
            funext s'
            split_ifs <;> simp_all
        _ ≤ _ := by
            split_ifs with hg
            · rw [mass_eq_zero_of_support _ fun s' hs' h => h (hkeep s hs hg s' hs'), mul_zero]
            · rw [pow_succ]
              gcongr
              exact hstep s hs

end Geom

/-! ### The algorithm -/

variable {V : Type} [Fintype V]

/-- Sparsifier accuracy. -/
abbrev eps : ℝ := 1 / 16

/-- Budget of one tree round. -/
def treeBudget (V : Type) [Fintype V] : ℕ :=
  72 * Fintype.card V * (Nat.clog 2 (Fintype.card V) + 1)

/-- The deterministic search for one tree, compiled to a randomized tree. -/
def treeRun (T : RootedTree V) : RTree (Finset V) ℝ (Res V) (treeBudget V) :=
  (RTree.ofDeterministic ((TwoRespecting.twoRespectingProg T).toDTree (treeBudget V))).map
    Option.join

/-- One round: sample a tree and keep the better result. -/
def round (P : PMF (RootedTree V)) (r : Res V) : RTree (Finset V) ℝ (Res V) (treeBudget V) :=
  RTree.mix (P.map fun T => (treeRun T).map (bestR r))

/-- A minimum cut of an explicit graph, chosen for free. -/
def minShore (hn : 2 ≤ Fintype.card V) (H : WeightedGraph V) : Finset V :=
  Classical.choose (exists_isMinCut_of_two_le_card H hn)

theorem minShore_spec (hn : 2 ≤ Fintype.card V) (H : WeightedGraph V) :
    IsMinCut H (minShore hn H) :=
  Classical.choose_spec (exists_isMinCut_of_two_le_card H hn)

theorem nonempty_of_two_le (hn : 2 ≤ Fintype.card V) : Nonempty V :=
  Fintype.card_pos_iff.mp (by omega)

/-- The tree distribution for `H` when its minimum cut is positive. -/
def treePMF (hn : 2 ≤ Fintype.card V) (H : WeightedGraph V)
    (h : H.cut (minShore hn H) ≠ 0) : PMF (RootedTree V) :=
  Classical.choose (TreePacking.exists_tree_pmf H
    (lt_of_le_of_ne (H.cut_nonneg _) (Ne.symm h)) (minShore_spec hn H).2 (nonempty_of_two_le hn))

theorem treePMF_spec (hn : 2 ≤ Fintype.card V) (H : WeightedGraph V)
    (h : H.cut (minShore hn H) ≠ 0) (S : Finset V) :
    mass (treePMF hn H h) (fun T => 3 ≤ (T.crossSet S).card) ≤
      ENNReal.ofReal (2 * H.cut S / (3 * H.cut (minShore hn H))) :=
  Classical.choose_spec (TreePacking.exists_tree_pmf H
    (lt_of_le_of_ne (H.cut_nonneg _) (Ne.symm h)) (minShore_spec hn H).2
      (nonempty_of_two_le hn)) S

/-- Steps 2–4 for an explicit sparsifier `H`. -/
def stage2 (hn : 2 ≤ Fintype.card V) (k : ℕ) (H : WeightedGraph V) :
    RTree (Finset V) ℝ (Option (Finset V)) (k * treeBudget V) :=
  if h : H.cut (minShore hn H) = 0 then RTree.pure (PMF.pure (some (minShore hn H)))
  else (RTree.iterate (round (treePMF hn H h)) k none).map (Option.map Prod.snd)

/-- The sparsification step with accuracy `1/16` and failure exponent `s`. -/
def sparsifier (V : Type) [Fintype V] (s : ℝ) :
    RTree (Finset V) ℝ (Option (WeightedGraph V))
      (WeightedGraph.capQ V (WeightedGraph.paramρ V s) (WeightedGraph.paramc V s eps)) :=
  WeightedGraph.sparsify (WeightedGraph.paramρ V s) (WeightedGraph.paramc V s eps)
    (WeightedGraph.paramR V s) ⌈2 * WeightedGraph.paramc V s eps * (Fintype.card V : ℝ) ^ 2⌉₊
    (WeightedGraph.capQ V (WeightedGraph.paramρ V s) (WeightedGraph.paramc V s eps))

/-- **The randomized weighted minimum-cut algorithm.** -/
def weightedMinCut (hn : 2 ≤ Fintype.card V) (s : ℝ) (k : ℕ) :
    RTree (Finset V) ℝ (Option (Finset V))
      (WeightedGraph.capQ V (WeightedGraph.paramρ V s) (WeightedGraph.paramc V s eps) +
        k * treeBudget V) :=
  (sparsifier V s).bind fun oH => match oH with
    | none => RTree.pure (PMF.pure none)
    | some H => stage2 hn k H

/-! ### Correctness -/

theorem eval_treeRun (G : WeightedGraph V) (T : RootedTree V) :
    (treeRun T).eval G.cut = PMF.pure (Prog.eval G.cut (TwoRespecting.twoRespectingProg T)) := by
  have hc : Prog.cost G.cut (TwoRespecting.twoRespectingProg T) ≤ treeBudget V :=
    TwoRespecting.twoRespectingProg_cost T G
  rw [treeRun, RTree.eval_map]
  have hD : (RTree.ofDeterministic
      ((TwoRespecting.twoRespectingProg T).toDTree (treeBudget V))).eval G.cut =
      PMF.pure (((TwoRespecting.twoRespectingProg T).toDTree (treeBudget V)).eval G.cut) := by
    simp [RTree.eval, DTree.eval, PMF.pure_map]
  rw [hD, Prog.toDTree_eval _ _ _ hc, PMF.pure_map]
  rfl

theorem eval_round (G : WeightedGraph V) (P : PMF (RootedTree V)) (r : Res V) :
    (round P r).eval G.cut =
      P.bind fun T => PMF.pure (bestR r (Prog.eval G.cut (TwoRespecting.twoRespectingProg T))) := by
  simp only [round, RTree.eval_mix, PMF.bind_map]
  congr 1
  funext T
  simp [RTree.eval_map, eval_treeRun, PMF.pure_map]

theorem mem_support_round {G : WeightedGraph V} {P : PMF (RootedTree V)} {r r' : Res V}
    (h : r' ∈ ((round P r).eval G.cut).support) :
    ∃ T, r' = bestR r (Prog.eval G.cut (TwoRespecting.twoRespectingProg T)) := by
  rw [eval_round, PMF.mem_support_bind_iff] at h
  obtain ⟨T, _, hT⟩ := h
  exact ⟨T, (PMF.mem_support_pure_iff _ _).mp hT⟩

/-- The tree search is sound. -/
theorem sound_tree (G : WeightedGraph V) (T : RootedTree V) :
    Sound G (Prog.eval G.cut (TwoRespecting.twoRespectingProg T)) := by
  intro x hx
  obtain ⟨h1, h2, -⟩ := TwoRespecting.twoRespectingProg_correct T G x hx
  exact ⟨h1, h2⟩

/-- The tree search covers every proper cut that 2-respects the tree. -/
theorem covers_tree (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V) (T : RootedTree V)
    {S : Finset V} (hS : ProperShore S) (hcard : (T.crossSet S).card ≤ 2) :
    Covers (Prog.eval G.cut (TwoRespecting.twoRespectingProg T)) (G.cut S) := by
  have hV : ∃ v, v ≠ T.root := Fintype.exists_ne_of_one_lt_card (by omega) T.root
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (TwoRespecting.twoRespectingProg_isSome T G hV)
  exact ⟨x, hx, (TwoRespecting.twoRespectingProg_correct T G x hx).2.2 S hS hcard⟩

/-- **Correctness for an explicit sparsifier.** -/
theorem stage2_correct (G H : WeightedGraph V) (hn : 2 ≤ Fintype.card V) (k : ℕ)
    (hH : ∀ S, (1 - eps) * G.cut S ≤ H.cut S ∧ H.cut S ≤ (1 + eps) * G.cut S) :
    mass ((stage2 hn k H).eval G.cut) (fun o => ¬∃ S, o = some S ∧ IsMinCut G S) ≤
      ENNReal.ofReal ((34 / 45) ^ k) := by
  set S0 := minShore hn H
  have hS0 := minShore_spec hn H
  set C := minShore hn G
  have hC := minShore_spec hn G
  unfold stage2
  split_ifs with h0
  · -- A zero cut of `H` is a zero cut of `G`.
    have hgood : IsMinCut G (minShore hn H) := by
      refine ⟨hS0.1, fun T _ => ?_⟩
      have := (hH S0).1
      rw [h0] at this
      norm_num [eps] at this
      have hG0 : G.cut S0 ≤ 0 := by linarith [G.cut_nonneg S0]
      exact hG0.trans (G.cut_nonneg T)
    rw [RTree.eval_pure, mass_pure]
    simp [hgood]
  -- Positive minimum cut: geometric failure over the rounds.
  have hlam : 0 < H.cut S0 := lt_of_le_of_ne (H.cut_nonneg _) (Ne.symm h0)
  rw [RTree.eval_map, mass_map]
  refine (mass_mono _ (Q := fun r => ¬(Sound G r ∧ Covers r (G.cut C))) ?_).trans ?_
  · intro r hr hgood
    apply hr
    obtain ⟨hs, x, hx, hxt⟩ := hgood
    obtain ⟨hp, hv⟩ := hs x hx
    refine ⟨x.2, by rw [Option.mem_def] at hx; simp [hx], hp, fun T hT => ?_⟩
    rw [← hv]
    exact hxt.trans (hC.2 T hT)
  have hstep := iterate_fail_pow (round (treePMF hn H h0)) G.cut (Sound G)
    (fun r => Covers r (G.cut C)) (ENNReal.ofReal (34 / 45))
    (fun r hr r' hr' => by
      obtain ⟨T, rfl⟩ := mem_support_round hr'
      exact sound_bestR hr (sound_tree G T))
    (fun r _ hg r' hr' => by
      obtain ⟨T, rfl⟩ := mem_support_round hr'
      exact covers_bestR_left hg)
    (fun r _ => by
      rw [eval_round, mass_bind]
      calc ∑' T, (treePMF hn H h0) T * mass (PMF.pure (bestR r
              (Prog.eval G.cut (TwoRespecting.twoRespectingProg T)))) (fun s' => ¬Covers s' (G.cut C))
          ≤ ∑' T, (if 3 ≤ (T.crossSet C).card then (treePMF hn H h0) T else 0) := by
            refine ENNReal.tsum_le_tsum fun T => ?_
            rw [mass_pure]
            by_cases h3 : 3 ≤ (T.crossSet C).card
            · simp only [h3, ↓reduceIte]
              split_ifs <;> simp
            · have hcov : Covers (bestR r (Prog.eval G.cut (TwoRespecting.twoRespectingProg T)))
                  (G.cut C) := covers_bestR_right (covers_tree G hn T hC.1 (by omega))
              simp [hcov, h3]
        _ = mass (treePMF hn H h0) (fun T => 3 ≤ (T.crossSet C).card) := by rw [mass_eq_tsum]; congr!
        _ ≤ ENNReal.ofReal (2 * H.cut C / (3 * H.cut S0)) := treePMF_spec hn H h0 C
        _ ≤ ENNReal.ofReal (34 / 45) := by
            apply ENNReal.ofReal_le_ofReal
            have h1 := (hH C).2
            have h2 := hC.2 S0 hS0.1
            have h3 := (hH S0).1
            rw [div_le_iff₀ (by positivity)]
            simp only [eps] at h1 h3
            nlinarith [G.cut_nonneg C])
  refine (hstep k none (sound_none G)).trans ?_
  have hnc : ¬Covers (none : Res V) (G.cut C) := by
    rintro ⟨x, hx, -⟩
    simp at hx
  simp only [hnc, ↓reduceIte]
  rw [← ENNReal.ofReal_pow (by norm_num)]

/-- **Randomized weighted minimum cut.** For `n ≥ 2`, `s ≥ 0`, and `k` rounds, the
output is a minimum cut of `G` except with probability at most
`(2n+2)^{-s} + (34/45)^k`. -/
theorem weightedMinCut_correct (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V) {s : ℝ}
    (hs : 0 ≤ s) (k : ℕ) :
    mass ((weightedMinCut hn s k).eval G.cut) (fun o => ¬∃ S, o = some S ∧ IsMinCut G S) ≤
      ENNReal.ofReal (WeightedGraph.baseB V ^ (-s)) + ENNReal.ofReal ((34 / 45) ^ k) := by
  rw [weightedMinCut, RTree.eval_bind]
  refine mass_bind_le_add _ _ (fun o => ¬∃ X, o = some X ∧
    IsSparseCutSparsifier eps (WeightedGraph.edgeBound V (WeightedGraph.paramc V s eps)) G X)
    _ (WeightedGraph.sparsify_whp G (by omega) hs (by norm_num) (by norm_num)) ?_
  intro oH hoH
  push Not at hoH
  obtain ⟨H, rfl, hsp⟩ := hoH
  exact stage2_correct G H hn k hsp.1.2

/-- Rounds making `(34/45)^k ≤ (2n+2)^{-s}`. -/
def rounds (V : Type) [Fintype V] (s : ℝ) : ℕ :=
  ⌈s * Real.log (WeightedGraph.baseB V) / Real.log (45 / 34)⌉₊

theorem pow_rounds_le (V : Type) [Fintype V] (s : ℝ) :
    (34 / 45 : ℝ) ^ rounds V s ≤ WeightedGraph.baseB V ^ (-s) := by
  have hB : 0 < WeightedGraph.baseB V := by
    have : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
    simp only [WeightedGraph.baseB]; linarith
  have hl : 0 < Real.log (45 / 34) := Real.log_pos (by norm_num)
  have hk : s * Real.log (WeightedGraph.baseB V) ≤ rounds V s * Real.log (45 / 34) := by
    rw [← div_le_iff₀ hl]
    exact Nat.le_ceil _
  rw [Real.rpow_def_of_pos hB, ← Real.exp_log (by positivity : (0 : ℝ) < (34 / 45) ^ rounds V s),
    Real.log_pow, Real.exp_le_exp, show (34 / 45 : ℝ) = (45 / 34)⁻¹ by norm_num, Real.log_inv]
  nlinarith

/-- **Weighted minimum cut with high probability.** With `rounds V s` tree
rounds, the output is a minimum cut except with probability at most
`2·(2n+2)^{-s}`. -/
theorem weightedMinCut_whp (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V) {s : ℝ}
    (hs : 0 ≤ s) :
    mass ((weightedMinCut hn s (rounds V s)).eval G.cut)
        (fun o => ¬∃ S, o = some S ∧ IsMinCut G S) ≤
      ENNReal.ofReal (2 * WeightedGraph.baseB V ^ (-s)) := by
  refine (weightedMinCut_correct G hn hs _).trans ?_
  have hb : 0 ≤ WeightedGraph.baseB V ^ (-s) := by
    apply Real.rpow_nonneg
    have : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
    simp only [WeightedGraph.baseB]; linarith
  rw [two_mul, ENNReal.ofReal_add hb hb]
  gcongr
  exact pow_rounds_le V s

end
end WeightedMinCut
end CutQueryComplexity
