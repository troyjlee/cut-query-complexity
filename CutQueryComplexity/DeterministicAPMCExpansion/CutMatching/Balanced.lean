import CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.Leakage
import CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.Gap

/-!
# Quantitative progress for a public balanced sparse cut

Low leakage leaves many starting rows with at least three quarters of their
mass on the chosen shore. Every matching sending that shore outside itself
pairs a fixed positive amount of that mass with entries at most half as large.
The proved entropy gap then pays a constant times the number of vertices.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.CutMatching

open Finset
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

theorem Matching.mate_mass_le_compl (M : Matching V) (S : Finset V) (p : V → ℝ)
    (hp : ∀ v, 0 ≤ p v) (hcross : ∀ v ∈ S, M.mate v ∉ S) :
    (∑ v ∈ S, p (M.mate v)) ≤ ∑ v ∈ Sᶜ, p v := by
  have hsub : S.image M.mate ⊆ Sᶜ := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hv
    exact mem_compl.mpr (hcross u hu)
  calc
    _ = ∑ v ∈ S.image M.mate, p v := by
      rw [sum_image (fun _ _ _ _ h => M.mate.injective h)]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun v _ _ => hp v)

def favored (M : Matching V) (p : V → ℝ) (S : Finset V) : Finset V :=
  S.filter fun v => 2 * p (M.mate v) ≤ p v

theorem favored_mass_ge_quarter (M : Matching V) (S : Finset V) (p : V → ℝ)
    (hp : ∀ v, 0 ≤ p v) (hsum : ∑ v, p v = 1)
    (hout : (∑ v ∈ Sᶜ, p v) ≤ 1 / 4)
    (hcross : ∀ v ∈ S, M.mate v ∉ S) :
    (1 / 4 : ℝ) ≤ ∑ v ∈ favored M p S, p v := by
  have hpoint (v : V) : p v ≤
      (if 2 * p (M.mate v) ≤ p v then p v else 0) + 2 * p (M.mate v) := by
    split_ifs with h
    · linarith [hp (M.mate v)]
    · linarith
  have h := sum_le_sum (s := S) (fun v _ => hpoint v)
  simp only [sum_add_distrib, ← mul_sum] at h
  have hfav : (∑ v ∈ S, if 2 * p (M.mate v) ≤ p v then p v else 0) =
      ∑ v ∈ favored M p S, p v := by rw [favored, sum_filter]
  rw [hfav] at h
  have hm := M.mate_mass_le_compl S p hp hcross
  have htotal := sum_add_sum_compl S p
  rw [hsum] at htotal
  linarith

theorem sum_pairGain (M : Matching V) (p : V → ℝ) :
    (∑ v, pairGain (p v) (p (M.mate v))) =
      2 * (entropy (average M p) - entropy p) := by
  have hperm : (∑ v, Real.negMulLog (p (M.mate v))) =
      ∑ v, Real.negMulLog (p v) := Equiv.sum_comp M.mate (fun v => Real.negMulLog (p v))
  simp only [pairGain, entropy, average, sum_sub_distrib, ← mul_sum, hperm]
  ring

theorem favored_gain (M : Matching V) (S : Finset V) (p : V → ℝ)
    (hp : ∀ v, 0 ≤ p v) :
    gapConstant * (∑ v ∈ favored M p S, p v) ≤
      ∑ v, pairGain (p v) (p (M.mate v)) := by
  calc
    _ = ∑ v ∈ favored M p S, gapConstant * p v := mul_sum _ _ _
    _ ≤ ∑ v ∈ favored M p S, pairGain (p v) (p (M.mate v)) := by
      apply sum_le_sum
      intro v hv
      exact pairGain_ge (hp v) (hp (M.mate v)) (mem_filter.mp hv).2
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _)
      (fun v _ _ => pairGain_nonneg (hp v) (hp (M.mate v)))

theorem entropy_increment_of_low_escape (M : Matching V) (S : Finset V) (p : V → ℝ)
    (hp : ∀ v, 0 ≤ p v) (hsum : ∑ v, p v = 1)
    (hout : (∑ v ∈ Sᶜ, p v) ≤ 1 / 4)
    (hcross : ∀ v ∈ S, M.mate v ∉ S) :
    gapConstant / 8 ≤ entropy (average M p) - entropy p := by
  have hmass := favored_mass_ge_quarter M S p hp hsum hout hcross
  have hscaled := mul_le_mul_of_nonneg_left hmass gapConstant_pos.le
  have hgain := favored_gain M S p hp
  rw [sum_pairGain] at hgain
  linarith

def goodStarts (history : List (Matching V)) (S : Finset V) : Finset V :=
  S.filter fun u => (∑ v ∈ Sᶜ, walk history u v) ≤ 1 / 4

theorem goodStarts_card (history : List (Matching V)) (S : Finset V)
    (hsparse : 4 * (historyGraph history).cut S ≤ (S.card : ℝ)) :
    (S.card : ℝ) ≤ 2 * (goodStarts history S).card := by
  have hpoint (u : V) : (1 : ℝ) ≤
      (if (∑ v ∈ Sᶜ, walk history u v) ≤ 1 / 4 then 1 else 0) +
        4 * (∑ v ∈ Sᶜ, walk history u v) := by
    have hn : (0 : ℝ) ≤ ∑ v ∈ Sᶜ, walk history u v :=
      sum_nonneg (fun v _ => walk_nonneg history u v)
    split_ifs with h
    · linarith
    · linarith
  have h := sum_le_sum (s := S) (fun u _ => hpoint u)
  have hc : (∑ u ∈ S, if (∑ v ∈ Sᶜ, walk history u v) ≤ 1 / 4 then (1 : ℝ) else 0) =
      (goodStarts history S).card := by
    calc
      _ = ∑ _u ∈ goodStarts history S, (1 : ℝ) := by rw [goodStarts, sum_filter]
      _ = _ := by simp
  simp only [sum_const, nsmul_eq_mul, mul_one, sum_add_distrib, ← mul_sum] at h
  rw [hc, ← leakage_eq_start_sum] at h
  have hl := twice_leakage_le_cut history S
  linarith

/-- Every legal matching against a completion of a quarter-balanced sparse
shore raises the potential by at least `gapConstant*N/64`. -/
theorem balanced_progress (history : List (Matching V)) (S : Finset V) (M : Matching V)
    (hbalanced : Fintype.card V ≤ 4 * S.card)
    (hsparse : 4 * (historyGraph history).cut S ≤ (S.card : ℝ))
    (hcross : ∀ v ∈ S, M.mate v ∉ S) :
    gapConstant * Fintype.card V / 64 ≤ potential (M :: history) - potential history := by
  let good := goodStarts history S
  let gain := fun u => entropy (average M (walk history u)) - entropy (walk history u)
  have hnonneg (u : V) : 0 ≤ gain u := by
    exact sub_nonneg.mpr (entropy_average_mono M _ (walk_nonneg history u))
  have hgood : ∀ u ∈ good, gapConstant / 8 ≤ gain u := by
    intro u hu
    exact entropy_increment_of_low_escape M S _ (walk_nonneg history u)
      (walk_row_sum history u) (mem_filter.mp hu).2 hcross
  have hsum : (good.card : ℝ) * (gapConstant / 8) ≤ ∑ u, gain u := by
    calc
      _ = ∑ _u ∈ good, gapConstant / 8 := by simp [nsmul_eq_mul]
      _ ≤ ∑ u ∈ good, gain u := sum_le_sum hgood
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ good) (fun u _ _ => hnonneg u)
  have hcount : (Fintype.card V : ℝ) ≤ 8 * good.card := by
    have hb : (Fintype.card V : ℝ) ≤ 4 * (S.card : ℝ) := by exact_mod_cast hbalanced
    have hg := goodStarts_card history S hsparse
    change (S.card : ℝ) ≤ 2 * (good.card : ℝ) at hg
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hcount gapConstant_pos.le
  have heq : potential (M :: history) - potential history = ∑ u, gain u := by
    simp only [potential, walk, gain, sum_sub_distrib]
  rw [heq]
  nlinarith

end
end CutQueryComplexity.DeterministicAPMCExpansion.CutMatching

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.entropy_increment_of_low_escape
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.goodStarts_card
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.balanced_progress
