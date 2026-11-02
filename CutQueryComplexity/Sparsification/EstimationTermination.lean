import CutQueryComplexity.Sparsification.EstimationInvariant
import Mathlib.Algebra.Order.Floor.Semifield

/-! # Termination of a good estimation run

The potential of a running state is

```text
Ψ = 1 + (n+1)·Q(π, κ) + |pending|,
Q(π, κ) = (L − 1)·K + min(ℓ, K − 1),   ℓ = log₂⌊2κ/D⌋,   K = log₂(n²) + 2,
```

where `L` is the number of blocks and `D = topLevel H π`. Finished states have
potential zero.

* A batch boundary decreases `Q` by at least one. Separation at `κ` gives
  `D < κ`, so `ℓ ≥ 1`. The new scale is at most `κ/2`, which lowers `ℓ` by at
  least one, and at most `n²D/2`, which caps `ℓ` below `K − 1`. At most `n`
  regions are queued, so `Ψ` decreases.
* A region step never increases `Q`. A nontrivial merge removes at least one
  block, which pays for any increase of the capped `ℓ`; a trivial merge changes
  nothing. The queue shrinks by one, so `Ψ` decreases.

`estStep_failure` combines this with the per-call failure bound in the form
needed by `RTree.iterate_failure_le`.
-/

namespace CutQueryComplexity.WeightedGraph
noncomputable section
open scoped Classical
open Probability
variable {V : Type} [Fintype V]

/-- Logarithmic distance of the scale above the top level. -/
def scaleLevel (H : WeightedGraph V) (π : V → V) (κ : ℝ) : ℕ :=
  Nat.log 2 ⌊2 * κ / topLevel H π⌋₊

/-- Width of one block's share of the potential. -/
def potWidth (V : Type) [Fintype V] : ℕ := Nat.log 2 (Fintype.card V ^ 2) + 2

def batchPot (H : WeightedGraph V) (π : V → V) (κ : ℝ) : ℕ :=
  ((liveLabels π).card - 1) * potWidth V + min (scaleLevel H π κ) (potWidth V - 1)

def runPot (H : WeightedGraph V) (s : EstState V) : ℕ :=
  if s.status = .running then
    1 + (Fintype.card V + 1) * batchPot H s.π s.κ + s.pending.length
  else 0

/-! ### Arithmetic facts -/

theorem scaleLevel_pos {H : WeightedGraph V} {π : V → V} {κ : ℝ} (hD : 0 < topLevel H π)
    (hlt : topLevel H π < κ) : 1 ≤ scaleLevel H π κ := by
  apply Nat.log_pos (by norm_num)
  apply Nat.le_floor
  rw [le_div_iff₀ hD]
  push_cast
  linarith

theorem scaleLevel_half {H : WeightedGraph V} {π : V → V} {κ κ' : ℝ} (hD : 0 < topLevel H π)
    (h : κ' ≤ κ / 2) : scaleLevel H π κ' ≤ scaleLevel H π κ - 1 := by
  unfold scaleLevel
  rw [← Nat.log_div_base, ← Nat.floor_div_natCast]
  apply Nat.log_mono_right
  apply Nat.floor_le_floor
  push_cast
  rw [div_div, div_le_div_iff₀ hD (by positivity)]
  nlinarith

theorem scaleLevel_le_top {H : WeightedGraph V} {π : V → V} {κ' : ℝ} (hD : 0 < topLevel H π)
    (h : κ' ≤ (Fintype.card V : ℝ) ^ 2 / 2 * topLevel H π) :
    scaleLevel H π κ' ≤ potWidth V - 2 := by
  unfold scaleLevel potWidth
  rw [Nat.add_sub_cancel]
  apply Nat.log_mono_right
  apply Nat.floor_le_of_le
  rw [div_le_iff₀ hD]
  push_cast
  linarith

/-- The batch boundary decreases the batch potential. -/
theorem batchPot_boundary {H : WeightedGraph V} {π : V → V} {κ : ℝ}
    (hD : 0 < topLevel H π) (hlt : topLevel H π < κ) :
    batchPot H π (min (κ / 2) ((Fintype.card V : ℝ) ^ 2 / 2 * topLevel H π)) + 1 ≤
      batchPot H π κ := by
  have h1 := scaleLevel_pos hD hlt
  have h2 := scaleLevel_half hD (min_le_left (κ / 2) ((Fintype.card V : ℝ) ^ 2 / 2 * topLevel H π))
  have h3 := scaleLevel_le_top hD (min_le_right (κ / 2) _)
  have hK : 2 ≤ potWidth V := by simp [potWidth]
  unfold batchPot
  omega

/-- A merge never increases the batch potential. -/
theorem batchPot_merge {H : WeightedGraph V} {π π' : V → V} {κ : ℝ} {g : ℕ}
    (hcount : (liveLabels π').card + g ≤ (liveLabels π).card)
    (hlive' : 1 ≤ g → 1 ≤ (liveLabels π').card)
    (htriv : g = 0 → π' = π) : batchPot H π' κ ≤ batchPot H π κ := by
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · rw [htriv rfl]
  · have hlive := hlive' hg
    unfold batchPot
    set c := (liveLabels π').card - 1
    set K := potWidth V
    have hK : 2 ≤ K := by simp [K, potWidth]
    have hb : c + 1 ≤ (liveLabels π).card - 1 := by omega
    have hmul : (c + 1) * K ≤ ((liveLabels π).card - 1) * K := Nat.mul_le_mul_right K hb
    have hm := min_le_right (scaleLevel H π' κ) (K - 1)
    rw [Nat.add_mul, one_mul] at hmul
    omega

/-! ### Merges -/

/-- A call with no nontrivial group leaves the labeling unchanged. -/
theorem mergeMap_eq_self {π : V → V} {T : Finset V} {X : WeightedGraph V} {θ : ℝ}
    (h : nontrivialGroups T X θ = ∅) : mergeMap π T X θ = π := by
  funext v
  by_cases hv : π v ∈ T
  · rw [mergeMap_of_mem hv]
    have hc : ¬2 ≤ (X.strongComponent θ (π v)).card := by
      intro h2
      have : X.strongComponent θ (π v) ∈ nontrivialGroups T X θ :=
        Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hv, h2⟩
      rw [h] at this
      exact Finset.notMem_empty _ this
    rw [card_le_one_component hc]
    have := rep_mem (Finset.singleton_nonempty (π v)) (π v)
    exact Finset.mem_singleton.mp this
  · rw [mergeMap_of_not_mem hv]

theorem liveLabels_pos {π : V → V} (hπ : IsLabeling π) (v : V) : 1 ≤ (liveLabels π).card :=
  Finset.card_pos.mpr ⟨π v, (mem_liveLabels_iff hπ _).mpr ⟨v, rfl⟩⟩

theorem afterCall_pot {H : WeightedGraph V} {s : EstState V} (hπ : IsLabeling s.π)
    (hκ : 0 < s.κ) {S : Finset V} {rest : List (Finset V)} (hpend : s.pending = S :: rest)
    (hrun : s.status = .running) {X : WeightedGraph V} (hX : X.induce (S.image s.π) = X)
    (ans : Finset V → ℝ) :
    runPot H (afterCall s S rest X ans) + 1 ≤ runPot H s := by
  have hθ : 0 < 3 * s.κ / 4 := by positivity
  have hT := image_labels hπ S
  have hlab := mergeMap_isLabeling hπ hT hX hθ
  have hmerge := batchPot_merge (H := H) (κ := s.κ)
    (card_liveLabels_merge hT hX hθ)
    (fun hg => by
      obtain ⟨K, hK⟩ := Finset.card_pos.mp hg
      obtain ⟨hK, _⟩ := Finset.mem_filter.mp hK
      obtain ⟨b, _, _⟩ := Finset.mem_image.mp hK
      exact liveLabels_pos hlab b)
    (fun h => mergeMap_eq_self (Finset.card_eq_zero.mp h))
  simp only [runPot, afterCall, hrun, hpend, List.length_cons, ↓reduceIte]
  have : (Fintype.card V + 1) * batchPot H (mergeMap s.π (S.image s.π) X (3 * s.κ / 4)) s.κ ≤
      (Fintype.card V + 1) * batchPot H s.π s.κ := Nat.mul_le_mul_left _ hmerge
  omega

theorem boundary_pot {G H : WeightedGraph V} (hH : IsApproxKruskalForest G H) {s : EstState V}
    (hs : Good G H s) (hrun : s.status = .running) (hpend : s.pending = []) :
    runPot H (boundary H s) + 1 ≤ runPot H s := by
  have hsepκ : G.Separated s.π s.κ := by
    apply separated_of_related G
    intro u v hr
    rcases hs.covered u with h | ⟨S, hS, _⟩
    · exact h v hr
    · rw [hpend] at hS
      exact absurd hS List.not_mem_nil
  unfold boundary
  split_ifs with hrem
  · have hD := topLevel_pos H s.π hrem
    have hlt : topLevel H s.π < s.κ := by
      have := topLevel_lt hH (hsepκ.mono (by linarith [hs.pos] : s.κ ≤ 2 * (s.κ / 2))) hrem
      linarith
    have hb := batchPot_boundary hD hlt
    have hreg : (activeRegions H s.π (topLevel H s.π / (Fintype.card V : ℝ) ^ 2)).toList.length
        ≤ Fintype.card V := by
      rw [Finset.length_toList]
      exact (Finset.card_filter_le _ _).trans Finset.card_image_le |>.trans (by simp)
    simp only [runPot, hrun, hpend, List.length_nil, ↓reduceIte]
    have : (Fintype.card V + 1) * (batchPot H s.π (min (s.κ / 2)
        ((Fintype.card V : ℝ) ^ 2 / 2 * topLevel H s.π)) + 1) ≤
        (Fintype.card V + 1) * batchPot H s.π s.κ := Nat.mul_le_mul_left _ hb
    rw [Nat.mul_add, mul_one] at this
    omega
  · simp only [runPot, hrun, ↓reduceIte, reduceCtorEq]
    omega

/-! ### The fuel-indexed invariant -/

/-- A good state whose potential fits in the remaining fuel. -/
def RunInv (G H : WeightedGraph V) (N : ℕ) (s : EstState V) : Prop :=
  Good G H s ∧ runPot H s ≤ N

/-- **One step keeps the fuel-indexed invariant except with the call failure.** -/
theorem estStep_failure {G H : WeightedGraph V} (hH : IsApproxKruskalForest G H) {ρ : ℝ}
    (hρ : 0 < ρ) {R : ℕ} (hR : ρ * (Fintype.card V : ℝ) ^ 2 ≤ R) {δ₀ : ℝ} (hδ : 0 ≤ δ₀)
    (hδ2 : δ₀ ≤ 2)
    (hexp : ((2 * Fintype.card V : ℕ) : ℝ) ^ 2 * Real.exp (-(ρ / 128)) ≤ δ₀ / 4)
    (N : ℕ) (s : EstState V) (hs : RunInv G H (N + 1) s) :
    Probability.mass ((estStep H ρ R s).eval G.cut) (fun s' => ¬RunInv G H N s') ≤
      callFailure V ρ δ₀ := by
  obtain ⟨hg, hpot⟩ := hs
  unfold estStep
  rcases hst : s.status with _ | _ | _
  · -- Running.
    rcases hp : s.pending with _ | ⟨S, rest⟩
    · simp only
      rw [RTree.eval_pure]
      apply mass_pure_le
      intro hbad
      apply hbad
      exact ⟨boundary_good hH hg hst hp, by have := boundary_pot hH hg hst hp; omega⟩
    · simp only [hg.pos, ↓reduceDIte]
      calc
        _ ≤ Probability.mass ((regionStep ρ R s S rest hg.pos).eval G.cut)
            (fun s' => ¬Good G H s') := by
          apply mass_mono_on_support
          intro s' hs' hbad hgood
          apply hbad
          refine ⟨hgood, ?_⟩
          rw [regionStep_eval] at hs'
          obtain ⟨o, ho, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hs'
          cases o with
          | none => exact absurd rfl hgood.notFailed
          | some X =>
              have hB : Fintype.card V ≤ 2 ^ searchDepth V := Nat.le_pow_clog (by decide) _
              have hX := estimateCall_support G (searchDepth V) (searchDepth V) s.π s.cache
                hg.cache _ hB hB hg.pos hρ R ho
              have := afterCall_pot (H := H) hg.labeling hg.pos hp hst hX
                (RegionStep.answers G s S X)
              simp only [RegionStep.next]
              omega
        _ ≤ _ := regionStep_failure hg hp hg.pos hρ hR hδ hδ2 hexp
  · -- Done: the state is fixed.
    simp only
    rw [RTree.eval_pure]
    apply mass_pure_le
    intro hbad
    exact hbad ⟨hg, by simp [runPot, hst]⟩
  · exact absurd hst hg.notFailed

end
end CutQueryComplexity.WeightedGraph
