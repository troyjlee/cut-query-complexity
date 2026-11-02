import CutQueryComplexity.GlobalSTReduction.Specification
import CutQueryComplexity.GHReduction.ThresholdProbability

/-! # A sampling level isolates a vertex of a fixed global optimum (Phase 3)

Fix a global optimum `S` with the public root `r ∉ S` (`exists_minCut_avoiding`);
`S` is a proof device only. The terminal sample `levelSample univ r i seed`
keeps `r` and keeps each other vertex with probability `2^{-i}`.

* `Hit S seed`: at level `hitLevel |S|` exactly one vertex of `S` survives.
  The events "`v` is the unique survivor" are pairwise disjoint, and each has
  probability at least `1/(8|S|)` (`uniqueSurvivor_hitLevel`). Their union is
  computed exactly as a disjoint sum (`mass_exists_disjoint`), so
  `mass_hit_ge : 1/8 ≤ Pr[Hit S]` and `mass_not_hit_le : Pr[¬Hit S] ≤ 7/8`.
* `hit_trace`: on a hit, the sample `R` at that level satisfies `R ∩ S = {v}`.
* `isMinCut_of_isolating`: then any minimum isolating shore of `v` with respect
  to `R` is a global optimum; it is proper because it contains `v` and avoids `r`.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GlobalSTReduction
noncomputable section
open scoped Classical ENNReal
open Probability WeightedGraph GHReduction

section Disjoint

variable {α ι : Type*}

/-- The probability of a disjoint union of two events is the sum. -/
theorem mass_or_disjoint (p : PMF α) {P Q : α → Prop} (h : ∀ x, ¬(P x ∧ Q x)) :
    mass p (fun x => P x ∨ Q x) = mass p P + mass p Q := by
  rw [mass_eq_tsum, mass_eq_tsum, mass_eq_tsum, ← ENNReal.tsum_add]
  apply tsum_congr
  intro x
  by_cases hP : P x <;> by_cases hQ : Q x
  · exact absurd ⟨hP, hQ⟩ (h x)
  all_goals simp [hP, hQ]

/-- The probability of a finite pairwise disjoint union is the sum. -/
theorem mass_exists_disjoint (p : PMF α) (s : Finset ι) (E : ι → α → Prop)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ x, ¬(E i x ∧ E j x)) :
    mass p (fun x => ∃ i ∈ s, E i x) = ∑ i ∈ s, mass p (E i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have he : (fun x => ∃ j ∈ insert i s, E j x) = (fun x => E i x ∨ ∃ j ∈ s, E j x) := by
        funext x
        simp
      rw [he, Finset.sum_insert hi, mass_or_disjoint p, ih]
      · intro a ha b hb hab
        exact hdisj a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb) hab
      · rintro x ⟨hx, j, hj, hjx⟩
        have hij : i ≠ j := fun h => hi (h ▸ hj)
        exact hdisj i (Finset.mem_insert_self i s) j (Finset.mem_insert_of_mem hj) hij x ⟨hx, hjx⟩

end Disjoint

variable {V : Type} [Fintype V] [DecidableEq V]

/-- At the hit level of `A`, exactly one vertex of `A` survives. -/
def Hit {levels : ℕ} (A : Finset V) (seed : ThresholdSeed V levels) : Prop :=
  ∃ v ∈ A, UniqueSurvivor A v (hitLevel A.card) seed

omit [Fintype V] in
theorem uniqueSurvivor_disjoint {levels i : ℕ} {A : Finset V} {v w : V}
    (hw : w ∈ A) (hvw : v ≠ w) (seed : ThresholdSeed V levels) :
    ¬(UniqueSurvivor A v i seed ∧ UniqueSurvivor A w i seed) := by
  rintro ⟨hv, hw'⟩
  exact hv.2 w (Finset.mem_erase.mpr ⟨Ne.symm hvw, hw⟩) hw'.1

/-- Some vertex of `A` is the unique survivor with probability at least `1/8`. -/
theorem mass_hit_ge {levels : ℕ} (A : Finset V) (hA : A.Nonempty)
    (hi : hitLevel A.card ≤ levels) :
    ENNReal.ofReal (1 / 8 : ℝ) ≤ mass (thresholdSeedPMF V levels) (Hit A) := by
  have hsum : mass (thresholdSeedPMF V levels) (Hit A) =
      ∑ v ∈ A, mass (thresholdSeedPMF V levels) (UniqueSurvivor A v (hitLevel A.card)) :=
    mass_exists_disjoint _ A _ (fun v _ w hw hvw seed => uniqueSurvivor_disjoint hw hvw seed)
  have hcard : (A.card : ℝ≥0∞) ≠ 0 := by
    simpa using (Finset.card_pos.mpr hA).ne'
  have hlow : (A.card : ℝ≥0∞) * ENNReal.ofReal (1 / 8 : ℝ) ≤
      (A.card : ℝ≥0∞) * mass (thresholdSeedPMF V levels) (Hit A) := by
    rw [hsum, Finset.mul_sum]
    calc
      (A.card : ℝ≥0∞) * ENNReal.ofReal (1 / 8 : ℝ) = ∑ _v ∈ A, ENNReal.ofReal (1 / 8 : ℝ) := by
        simp
      _ ≤ _ := Finset.sum_le_sum (fun v hv => uniqueSurvivor_hitLevel A hv hi)
  exact (ENNReal.mul_le_mul_iff_right hcard (ENNReal.natCast_ne_top _)).mp hlow

theorem seven_eighths_eq_ofReal : (7 / 8 : ℝ≥0∞) = ENNReal.ofReal (7 / 8) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  simp

/-- No vertex of `A` is the unique survivor with probability at most `7/8`. -/
theorem mass_not_hit_le {levels : ℕ} (A : Finset V) (hA : A.Nonempty)
    (hi : hitLevel A.card ≤ levels) :
    mass (thresholdSeedPMF V levels) (fun seed => ¬Hit A seed) ≤ 7 / 8 := by
  have hreal := real_add_compl (thresholdSeedPMF V levels) (Hit A)
  have hge := ENNReal.toReal_mono (mass_ne_top _ _) (mass_hit_ge A hA hi)
  rw [ENNReal.toReal_ofReal (by norm_num)] at hge
  rw [seven_eighths_eq_ofReal, ← ENNReal.ofReal_toReal (mass_ne_top _ (fun seed => ¬Hit A seed))]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- On a hit, the sample at the hit level meets `S` in exactly one vertex. -/
theorem hit_trace {levels : ℕ} {S : Finset V} {r : V} (hr : r ∉ S)
    {seed : ThresholdSeed V levels} (h : Hit S seed) :
    ∃ v ∈ S, levelSample Finset.univ r (hitLevel S.card) seed ∩ S = {v} := by
  obtain ⟨v, hv, huniq⟩ := h
  refine ⟨v, hv, uniqueSurvivor_trace Finset.univ S r seed (by simpa using hv) hr ?_⟩
  simpa using huniq

/-- A global optimum avoiding a given vertex. -/
theorem exists_minCut_avoiding (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V) (r : V) :
    ∃ S, IsMinCut G S ∧ r ∉ S := by
  obtain ⟨S, hS⟩ := exists_isMinCut_of_two_le_card G hn
  by_cases hr : r ∈ S
  · refine ⟨Sᶜ, ⟨⟨?_, ?_⟩, fun T hT => ?_⟩, by simpa using hr⟩
    · obtain ⟨x, hx⟩ : ∃ x, x ∉ S := by
        by_contra h
        push Not at h
        exact hS.1.2 (Finset.eq_univ_iff_forall.mpr h)
      exact ⟨x, by simpa using hx⟩
    · intro h
      obtain ⟨x, hx⟩ := hS.1.1
      have : x ∈ Sᶜ := h ▸ Finset.mem_univ x
      exact (Finset.mem_compl.mp this) hx
    · rw [cut_compl]
      exact hS.2 T hT
  · exact ⟨S, hS, hr⟩

/-- A minimum isolating shore of the unique sampled vertex of an optimum is an optimum. -/
theorem isMinCut_of_isolating (G : WeightedGraph V) {R S X : Finset V} {v r : V}
    (hS : IsMinCut G S) (hRS : R ∩ S = {v}) (hrR : r ∈ R) (hrS : r ∉ S)
    (hX : IsMinTraceCut G R {v} X) : IsMinCut G X := by
  have hSR : S ∩ R = {v} := by rw [Finset.inter_comm]; exact hRS
  have hle : G.cut X ≤ G.cut S := hX.2 S hSR
  have hvX : v ∈ X := by
    have : v ∈ X ∩ R := by rw [hX.1]; simp
    exact (Finset.mem_inter.mp this).1
  have hrX : r ∉ X := by
    intro hrX
    have hrv : r ∈ X ∩ R := Finset.mem_inter.mpr ⟨hrX, hrR⟩
    rw [hX.1, Finset.mem_singleton] at hrv
    have hvS : v ∈ S := by
      have : v ∈ R ∩ S := by rw [hRS]; simp
      exact (Finset.mem_inter.mp this).2
    exact hrS (hrv ▸ hvS)
  refine ⟨⟨⟨v, hvX⟩, fun h => hrX (h ▸ Finset.mem_univ r)⟩, fun T hT => hle.trans (hS.2 T hT)⟩

end
end CutQueryComplexity.GlobalSTReduction
