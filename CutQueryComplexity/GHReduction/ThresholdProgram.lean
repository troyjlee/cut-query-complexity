import CutQueryComplexity.GHReduction.ThresholdCuts
import CutQueryComplexity.GHReduction.ThresholdProbability

/-! # Executable sampled threshold cuts, with queried values

All program parameters are public. Each level computes isolating shores and
queries their values. A public guard accepts only small shores excluding the
source whose queried values are at most the threshold. Soundness therefore
does not depend on the canonical solver promise. Completeness uses that promise
and a concrete singleton-survivor event.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical BigOperators
open WeightedGraph

variable {V : Type} [Fintype V] [DecidableEq V]

def thresholdAccepted (U : Finset V) (s : V) (W : ℝ) (z : ℕ)
    (cut : Finset V × ℝ) : Prop :=
  s ∉ cut.1 ∧ cut.2 ≤ W ∧ (cut.1 ∩ U).card ≤ z

def thresholdCoverage (U : Finset V) (s : V) (W : ℝ) (z : ℕ)
    {R : Finset V} (cuts : R → Finset V × ℝ) : Finset V :=
  Finset.univ.biUnion (fun v : R =>
    if thresholdAccepted U s W z (cuts v) then (cuts v).1 ∩ U else ∅)

theorem mem_thresholdCoverage {U R : Finset V} {s x : V} {W : ℝ} {z : ℕ}
    {cuts : R → Finset V × ℝ} :
    x ∈ thresholdCoverage U s W z cuts ↔
      ∃ v : R, thresholdAccepted U s W z (cuts v) ∧ x ∈ (cuts v).1 ∩ U := by
  simp only [thresholdCoverage, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨v, hv⟩
    by_cases h : thresholdAccepted U s W z (cuts v)
    · exact ⟨v, h, by simpa only [h, ite_true] using hv⟩
    · simp only [h, ite_false, Finset.notMem_empty] at hv
  · rintro ⟨v, hv, hx⟩
    exact ⟨v, by simpa only [hv, ite_true] using hx⟩

theorem thresholdCoverage_subset (U : Finset V) (s : V) (W : ℝ) (z : ℕ)
    {R : Finset V} (cuts : R → Finset V × ℝ) :
    thresholdCoverage U s W z cuts ⊆ U := by
  intro x hx
  obtain ⟨v, _, hx⟩ := mem_thresholdCoverage.mp hx
  exact (Finset.mem_inter.mp hx).2

theorem isolatingValuesProgram_value {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (R : Finset V) (v : R) :
    (Prog.eval G.cut (isolatingValuesProgram family R) v).2 =
      G.cut (Prog.eval G.cut (isolatingValuesProgram family R) v).1 := by
  simp [isolatingValuesProgram]

def thresholdLevelProgram {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (U R : Finset V) (s : V) (W : ℝ) (z : ℕ) : Prog (Finset V) ℝ (Finset V) :=
  if 2 ≤ R.card then
    (isolatingValuesProgram family R).map (thresholdCoverage U s W z)
  else Prog.pure ∅

theorem thresholdLevelProgram_subset {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (U R : Finset V) (s : V) (W : ℝ) (z : ℕ) (read : Finset V → ℝ) :
    Prog.eval read (thresholdLevelProgram family U R s W z) ⊆ U := by
  by_cases hR : 2 ≤ R.card
  · simpa [thresholdLevelProgram, hR] using
      thresholdCoverage_subset U s W z (Prog.eval read (isolatingValuesProgram family R))
  · simp [thresholdLevelProgram, hR]

/-- This conclusion uses actual queried cut values, even if the primitive
supplies an arbitrary incorrect shore. -/
theorem thresholdLevelProgram_sound {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (U R : Finset V) (s : V) (W : ℝ) (z : ℕ) {x : V}
    (hx : x ∈ Prog.eval G.cut (thresholdLevelProgram family U R s W z)) :
    x ∈ U ∧ x ≠ s ∧ stValue G x s ≤ W := by
  by_cases hR : 2 ≤ R.card
  · simp only [thresholdLevelProgram, hR, ite_true, Prog.eval_map] at hx
    obtain ⟨v, hv, hx⟩ := mem_thresholdCoverage.mp hx
    obtain ⟨hs, hvalue, _⟩ := hv
    obtain ⟨hxS, hxU⟩ := Finset.mem_inter.mp hx
    rw [isolatingValuesProgram_value family G R v] at hvalue
    exact ⟨hxU, fun he => hs (he ▸ hxS), accepted_shore_sound G hs hxS hvalue⟩
  · simp [thresholdLevelProgram, hR] at hx

theorem thresholdLevelProgram_hit {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (hG : InputPromise M G) {U R C : Finset V} {s v : V}
    {W : ℝ} {z : ℕ} (hsR : s ∈ R) (hC : IsCanonicalSTCut G v s C)
    (htrace : C ∩ R = {v}) (hvalue : stValue G v s ≤ W) (hsize : (C ∩ U).card ≤ z) :
    C ∩ U ⊆ Prog.eval G.cut (thresholdLevelProgram family U R s W z) := by
  have hvR : v ∈ R := by
    have : v ∈ C ∩ R := by rw [htrace]; simp
    exact (Finset.mem_inter.mp this).2
  have hvs : v ≠ s := fun he => hC.1.2.1 (he ▸ hC.1.1)
  have hR : 2 ≤ R.card := by
    have hsub : ({s, v} : Finset V) ⊆ R := by simp [Finset.insert_subset_iff, hsR, hvR]
    have hcard := Finset.card_le_card hsub
    simpa [Ne.symm hvs] using hcard
  let cuts := Prog.eval G.cut (isolatingValuesProgram family R)
  have hcanon := (isolatingValuesProgram_correct family G hG R hR ⟨v, hvR⟩).1
  have he : (cuts ⟨v, hvR⟩).1 = C := canonicalIso_eq_pair G hsR hvs hC htrace hcanon
  have hval : (cuts ⟨v, hvR⟩).2 = G.cut C := by
    rw [isolatingValuesProgram_value family G R ⟨v, hvR⟩, he]
  have hacc : thresholdAccepted U s W z (cuts ⟨v, hvR⟩) := by
    refine ⟨by simpa [he] using hC.1.2.1, ?_, by simpa [he] using hsize⟩
    rw [hval, stValue_eq_of_minCut G hC.1]
    exact hvalue
  intro x hx
  simp only [thresholdLevelProgram, hR, ite_true, Prog.eval_map]
  apply mem_thresholdCoverage.mpr
  change ∃ w : R, thresholdAccepted U s W z (cuts w) ∧ x ∈ (cuts w).1 ∩ U
  exact ⟨⟨v, hvR⟩, hacc, by simpa [he] using hx⟩

def thresholdRoundProgram {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (U : Finset V) (s : V) (W : ℝ) (z levels : ℕ) (seed : ThresholdSeed V levels) :
    Prog (Finset V) ℝ (Finset V) :=
  (tableProgram (levels + 1) (fun i =>
    thresholdLevelProgram family U (levelSample U s i.val seed) s W z)).map
      (fun covered => Finset.univ.biUnion covered)

theorem mem_thresholdRoundProgram {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (U : Finset V) (s : V) (W : ℝ) (z levels : ℕ) (seed : ThresholdSeed V levels)
    (read : Finset V → ℝ) (x : V) :
    x ∈ Prog.eval read (thresholdRoundProgram family U s W z levels seed) ↔
      ∃ i : Fin (levels + 1), x ∈ Prog.eval read
        (thresholdLevelProgram family U (levelSample U s i.val seed) s W z) := by
  simp [thresholdRoundProgram]

theorem thresholdRoundProgram_sound {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (U : Finset V) (s : V) (W : ℝ) (z levels : ℕ)
    (seed : ThresholdSeed V levels) {x : V}
    (hx : x ∈ Prog.eval G.cut (thresholdRoundProgram family U s W z levels seed)) :
    x ∈ U ∧ x ≠ s ∧ stValue G x s ≤ W := by
  obtain ⟨i, hi⟩ := (mem_thresholdRoundProgram family U s W z levels seed G.cut x).mp hx
  exact thresholdLevelProgram_sound family G U _ s W z hi

theorem thresholdRoundProgram_hit {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (hG : InputPromise M G) {U C : Finset V} {s v : V}
    {W : ℝ} {z levels i : ℕ} (hsU : s ∈ U) (hi : i ≤ levels)
    (hC : IsCanonicalSTCut G v s C) (hvalue : stValue G v s ≤ W)
    (hsize : (C ∩ U).card ≤ z) (seed : ThresholdSeed V levels)
    (hhit : UniqueSurvivor (C ∩ U) v i seed) (hvU : v ∈ U) :
    C ∩ U ⊆ Prog.eval G.cut (thresholdRoundProgram family U s W z levels seed) := by
  have htrace : C ∩ levelSample U s i seed = {v} := by
    rw [Finset.inter_comm]
    exact uniqueSurvivor_trace U C s seed (Finset.mem_inter.mpr ⟨hC.1.1, hvU⟩) hC.1.2.1 hhit
  have hlevel := thresholdLevelProgram_hit family G hG (source_mem_levelSample hsU i seed)
    hC htrace hvalue hsize
  intro x hx
  exact (mem_thresholdRoundProgram family U s W z levels seed G.cut x).mpr
    ⟨⟨i, by omega⟩, hlevel hx⟩

theorem thresholdLevelProgram_cost_scaled {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (U R : Finset V) (s : V) (W : ℝ) (z : ℕ) (read : Finset V → ℝ) :
    n * Prog.cost read (thresholdLevelProgram family U R s W z) ≤
      (Nat.clog 2 n + 3) * Fintype.card V * (Q n + n) := by
  by_cases hR : 2 ≤ R.card
  · have hcost := isolatingProgram_cost_scaled family R hvn hQ read
    have hcard := Finset.card_le_univ R
    have hlog := Nat.clog_mono_right 2 (hcard.trans hvn)
    have hcostValues : Prog.cost read (isolatingValuesProgram family R) =
        Prog.cost read (isolatingProgram family R) + R.card := by
      simp [isolatingValuesProgram]
    simp only [thresholdLevelProgram, hR, ite_true, Prog.cost_map, hcostValues]
    have hsum := Nat.add_le_add hcost (Nat.mul_le_mul_left n hcard)
    have hlogmul := Nat.mul_le_mul_right (Fintype.card V * Q n) hlog
    calc
      _ ≤ (Nat.clog 2 n + 2) * Fintype.card V * Q n + n * Fintype.card V := by
        nlinarith only [hsum, hlogmul]
      _ ≤ (Nat.clog 2 n + 3) * Fintype.card V * (Q n + n) := by
        have hbase : n * Fintype.card V ≤
            (Nat.clog 2 n + 3) * Fintype.card V * n := by
          have := Nat.mul_le_mul_right (Fintype.card V * n)
            (show 1 ≤ Nat.clog 2 n + 3 by omega)
          nlinarith only [this]
        nlinarith only [hbase, Nat.zero_le (Fintype.card V * Q n)]
  · simp [thresholdLevelProgram, hR]

theorem thresholdRoundProgram_cost_scaled {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (U : Finset V) (s : V) (W : ℝ) (z levels : ℕ) (seed : ThresholdSeed V levels)
    (read : Finset V → ℝ) :
    n * Prog.cost read (thresholdRoundProgram family U s W z levels seed) ≤
      (levels + 1) * ((Nat.clog 2 n + 3) * Fintype.card V * (Q n + n)) := by
  simp only [thresholdRoundProgram, Prog.cost_map, tableProgram_cost, Finset.mul_sum]
  calc
    _ ≤ ∑ _i : Fin (levels + 1), (Nat.clog 2 n + 3) * Fintype.card V * (Q n + n) :=
      Finset.sum_le_sum (fun i _ =>
        thresholdLevelProgram_cost_scaled family hvn hQ U _ s W z read)
    _ = _ := by simp

end
end CutQueryComplexity.GHReduction
