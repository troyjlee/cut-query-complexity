import CutQueryComplexity.Spanner.Random
import CutQueryComplexity.Probability.FiniteEvents
import Mathlib.Order.Interval.Finset.Fin

/-! # Public nested terminal samples and singleton-hit probabilities

One finite array of independent fair coins defines all sampling levels. The
source is retained at every level. The probability calculations use the actual
coin distribution, not an independence premise about adaptively selected cuts.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical ENNReal
open Probability

variable {V : Type} [Fintype V] [DecidableEq V]

abbrev ThresholdSeed (V : Type) (levels : ℕ) := Fin levels × V → Bool

def thresholdSeedPMF (V : Type) [Fintype V] [DecidableEq V] (levels : ℕ) :
    PMF (ThresholdSeed V levels) := Spanner.coinPMF (Fin levels × V)

def levelBits (levels i : ℕ) : Finset (Fin levels) :=
  Finset.univ.filter (fun j => j.val < i)

theorem levelBits_card {levels i : ℕ} (hi : i ≤ levels) : (levelBits levels i).card = i := by
  by_cases hlt : i < levels
  · have he : levelBits levels i = Finset.Iio (⟨i, hlt⟩ : Fin levels) := by
      ext j
      simp [levelBits, Fin.lt_def]
    rw [he, Fin.card_Iio]
  · have he : i = levels := by omega
    subst i
    have hset : levelBits levels levels = Finset.univ := by
      ext j
      simp [levelBits, j.isLt]
    simp [hset]

def Survives {levels : ℕ} (i : ℕ) (seed : ThresholdSeed V levels) (v : V) : Prop :=
  ∀ j ∈ levelBits levels i, seed (j, v) = true

def levelSample {levels : ℕ} (U : Finset V) (s : V) (i : ℕ) (seed : ThresholdSeed V levels) : Finset V :=
  U.filter (fun v => v = s ∨ Survives i seed v)

theorem levelSample_subset {levels : ℕ} (U : Finset V) (s : V) (i : ℕ)
    (seed : ThresholdSeed V levels) : levelSample U s i seed ⊆ U := Finset.filter_subset _ _

theorem source_mem_levelSample {levels : ℕ} {U : Finset V} {s : V} (hs : s ∈ U)
    (i : ℕ) (seed : ThresholdSeed V levels) : s ∈ levelSample U s i seed := by
  simp [levelSample, hs]

theorem levelSample_nested {levels i j : ℕ} (U : Finset V) (s : V)
    (seed : ThresholdSeed V levels) (hij : i ≤ j) :
    levelSample U s j seed ⊆ levelSample U s i seed := by
  intro v hv
  obtain ⟨hvU, rfl | hv⟩ := Finset.mem_filter.mp hv
  · exact source_mem_levelSample hvU i seed
  · refine Finset.mem_filter.mpr ⟨hvU, Or.inr ?_⟩
    intro k hk
    apply hv k
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hk).2.trans_le hij⟩

@[simp] theorem levelSample_zero {levels : ℕ} (U : Finset V) (s : V)
    (seed : ThresholdSeed V levels) : levelSample U s 0 seed = U := by
  ext v
  simp [levelSample, Survives, levelBits]

theorem mass_survives_set {levels i : ℕ} (hi : i ≤ levels) (A : Finset V) :
    mass (thresholdSeedPMF V levels) (fun seed => ∀ v ∈ A, Survives i seed v) =
      (2⁻¹ : ℝ≥0∞) ^ (i * A.card) := by
  have hpred : (fun seed : ThresholdSeed V levels => ∀ v ∈ A, Survives i seed v) =
      (fun seed => ∀ p ∈ (levelBits levels i).product A, seed p = true) := by
    funext seed
    apply propext
    constructor
    · intro h p hp
      obtain ⟨hj, hv⟩ := Finset.mem_product.mp hp
      exact h p.2 hv p.1 hj
    · intro h v hv j hj
      exact h (j, v) (Finset.mem_product.mpr ⟨hj, hv⟩)
  rw [hpred]
  simpa only [thresholdSeedPMF, Finset.product_eq_sprod, Finset.card_product, levelBits_card hi] using
    Spanner.mass_coins_eq ((levelBits levels i).product A) (fun _ => true)

theorem mass_survives {levels i : ℕ} (hi : i ≤ levels) (v : V) :
    mass (thresholdSeedPMF V levels) (fun seed => Survives i seed v) = (2⁻¹ : ℝ≥0∞) ^ i := by
  simpa using mass_survives_set hi ({v} : Finset V)

theorem mass_survives_pair {levels i : ℕ} (hi : i ≤ levels) {v w : V} (hvw : v ≠ w) :
    mass (thresholdSeedPMF V levels) (fun seed => Survives i seed v ∧ Survives i seed w) =
      ((2⁻¹ : ℝ≥0∞) ^ i) ^ 2 := by
  simpa [hvw, pow_mul] using mass_survives_set hi ({v, w} : Finset V)

def UniqueSurvivor {levels : ℕ} (A : Finset V) (v : V) (i : ℕ)
    (seed : ThresholdSeed V levels) : Prop :=
  Survives i seed v ∧ ∀ w ∈ A.erase v, ¬Survives i seed w

/-- A union bound on pair survivals gives a useful lower bound without
requiring a separate binomial-distribution library. -/
theorem uniqueSurvivor_mass_bound {levels i : ℕ} (hi : i ≤ levels) (A : Finset V)
    {v : V} (hv : v ∈ A) :
    (2⁻¹ : ℝ≥0∞) ^ i ≤
      mass (thresholdSeedPMF V levels) (UniqueSurvivor A v i) +
        ((A.card - 1 : ℕ) : ℝ≥0∞) * (((2⁻¹ : ℝ≥0∞) ^ i) ^ 2) := by
  have hcover : ∀ seed : ThresholdSeed V levels, Survives i seed v →
      UniqueSurvivor A v i seed ∨ ∃ w ∈ A.erase v, Survives i seed v ∧ Survives i seed w := by
    intro seed hvSeed
    by_cases hall : ∀ w ∈ A.erase v, ¬Survives i seed w
    · exact Or.inl ⟨hvSeed, hall⟩
    · push_neg at hall
      obtain ⟨w, hw, hwSeed⟩ := hall
      exact Or.inr ⟨w, hw, hvSeed, hwSeed⟩
  have h := (mass_mono (thresholdSeedPMF V levels) hcover).trans (mass_or_le _ _ _)
  have hunion := mass_exists_finset_le (thresholdSeedPMF V levels) (A.erase v)
    (fun w seed => Survives i seed v ∧ Survives i seed w)
  have hsum : (∑ w ∈ A.erase v,
      mass (thresholdSeedPMF V levels) (fun seed => Survives i seed v ∧ Survives i seed w)) =
      ((A.card - 1 : ℕ) : ℝ≥0∞) * (((2⁻¹ : ℝ≥0∞) ^ i) ^ 2) := by
    rw [Finset.sum_congr rfl (fun w hw => mass_survives_pair hi
      (Ne.symm (Finset.mem_erase.mp hw).1))]
    simp [Finset.card_erase_of_mem hv]
  rw [mass_survives hi v] at h
  exact h.trans (add_le_add le_rfl (hunion.trans_eq hsum))

theorem uniqueSurvivor_trace {levels i : ℕ} (U C : Finset V) (s : V) (seed : ThresholdSeed V levels)
    {v : V} (hv : v ∈ C ∩ U) (hs : s ∉ C) :
    UniqueSurvivor (C ∩ U) v i seed → levelSample U s i seed ∩ C = {v} := by
  intro huniq
  ext w
  simp only [Finset.mem_inter, Finset.mem_singleton]
  constructor
  · rintro ⟨hwR, hwC⟩
    obtain ⟨hwU, hws | hwAlive⟩ := Finset.mem_filter.mp hwR
    · exact (hs (hws ▸ hwC)).elim
    · by_contra hwv
      exact huniq.2 w (Finset.mem_erase.mpr ⟨hwv, Finset.mem_inter.mpr ⟨hwC, hwU⟩⟩) hwAlive
  · rintro rfl
    exact ⟨Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp hv).2, Or.inr huniq.1⟩,
      (Finset.mem_inter.mp hv).1⟩

end
end CutQueryComplexity.GHReduction
