import CutQueryComplexity.GHReduction.SourceValues
import CutQueryComplexity.GHReduction.ThresholdAmplification

/-! # Public binary search for a maximum source-connectivity terminal

Each comparison executes the sampled threshold classifier on the current
candidate terminals together with the source. All arithmetic and set choices
are public. The hidden integral connectivity function appears only in proofs.
Fresh conditional classifier failure is charged once per binary-search level.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical ENNReal
open Probability

variable {V : Type} [Fintype V] [DecidableEq V]

def sourceThresholdBudget (Q : ℕ → ℕ) (n levels scale exponent : ℕ) : ℕ :=
  thresholdRounds levels scale exponent * thresholdRoundBudget Q n levels

def sourceMaxAtTree {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n : ℕ) (s : V) (levels scale exponent : ℕ) : (fuel : ℕ) →
      Finset V → ℕ → ℕ → RTree (Finset V) ℝ (Option V)
        (fuel * sourceThresholdBudget Q n levels scale exponent)
  | 0, R, _, _ => RTree.pure (PMF.pure (selectVertex R))
  | fuel + 1, R, lo, hi =>
    if hi ≤ lo then RTree.pure (PMF.pure (selectVertex R)) else
      let mid := lo + (hi - lo) / 2
      ((thresholdClassifyTree family n (insert s R) s (mid : ℝ) levels scale exponent).bind
        (fun covered => if (R \ covered).Nonempty then
          sourceMaxAtTree family n s levels scale exponent fuel (R \ covered) (mid + 1) hi
        else sourceMaxAtTree family n s levels scale exponent fuel R lo mid)).cast (by
          simp only [sourceThresholdBudget]
          ring)

theorem sourceMaxAtTree_failure_le {M n scale : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (hnscale : n ≤ scale) (G : WeightedGraph V) (hG : InputPromise M G) (s : V)
    (value : V → ℕ) (levels exponent : ℕ) (hlevels : thresholdLevels n ≤ levels)
    (fuel : ℕ) : ∀ (R : Finset V) (lo hi : ℕ), R.Nonempty → s ∉ R →
      (∀ v ∈ R, stValue G v s = (value v : ℝ)) →
      (∀ v ∈ R, lo ≤ value v ∧ value v ≤ hi) → hi < lo + 2 ^ fuel →
      mass ((sourceMaxAtTree family n s levels scale exponent fuel R lo hi).eval G.cut)
        (fun out => ¬IsMaximizer value R out) ≤
          (fuel : ℝ≥0∞) * ((((scale + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ exponent) := by
  induction fuel with
  | zero =>
    intro R lo hi hR hs hvalue hrange hspan
    have hhilo : hi ≤ lo := by simpa only [pow_zero] using Nat.le_of_lt_succ hspan
    have hgood := selectVertex_max_of_range value R hR hrange hhilo
    simp [sourceMaxAtTree, hgood]
  | succ fuel ih =>
    intro R lo hi hR hs hvalue hrange hspan
    by_cases hhilo : hi ≤ lo
    · have hgood := selectVertex_max_of_range value R hR hrange hhilo
      simp [sourceMaxAtTree, hhilo, hgood]
    · let mid := lo + (hi - lo) / 2
      let delta : ℝ≥0∞ := (((scale + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ exponent
      have hlohi : lo ≤ hi := by
        obtain ⟨v, hv⟩ := hR
        exact (hrange v hv).1.trans (hrange v hv).2
      have hspanLo : mid < lo + 2 ^ fuel := by
        dsimp [mid]
        rw [pow_succ] at hspan
        omega
      have hspanHi : hi < (mid + 1) + 2 ^ fuel := by
        dsimp [mid]
        rw [pow_succ] at hspan
        omega
      have hp : mass ((thresholdClassifyTree family n (insert s R) s (mid : ℝ)
          levels scale exponent).eval G.cut)
          (fun covered => covered ≠ lowTargets G (insert s R) s (mid : ℝ)) ≤ delta :=
        thresholdClassifyTree_failure_le family hvn hQ hnscale G hG (insert s R) s
          (mid : ℝ) levels exponent hlevels (Finset.mem_insert_self _ _)
      have hnext (covered : Finset V)
          (hgood : ¬covered ≠ lowTargets G (insert s R) s (mid : ℝ)) :
          mass ((if (R \ covered).Nonempty then
            sourceMaxAtTree family n s levels scale exponent fuel (R \ covered) (mid + 1) hi
            else sourceMaxAtTree family n s levels scale exponent fuel R lo mid).eval G.cut)
            (fun out => ¬IsMaximizer value R out) ≤ (fuel : ℝ≥0∞) * delta := by
        have he := not_not.mp hgood
        have hclass : ∀ v ∈ R, v ∈ covered ↔ value v ≤ mid := by
          intro v hv
          have hvs : v ≠ s := fun hvEq => hs (hvEq ▸ hv)
          rw [he, mem_lowTargets, hvalue v hv]
          simp only [Finset.mem_insert_of_mem hv, true_and, Nat.cast_le]
          exact ⟨fun h => h.2, fun h => ⟨hvs, h⟩⟩
        by_cases hhigh : (R \ covered).Nonempty
        · simp only [hhigh, ite_true]
          have hsHigh : s ∉ R \ covered := fun h => hs (Finset.mem_sdiff.mp h).1
          have hvalHigh : ∀ v ∈ R \ covered, stValue G v s = (value v : ℝ) :=
            fun v hv => hvalue v (Finset.mem_sdiff.mp hv).1
          have hrangeHigh : ∀ v ∈ R \ covered, mid + 1 ≤ value v ∧ value v ≤ hi := by
            intro v hv
            obtain ⟨hvR, hvC⟩ := Finset.mem_sdiff.mp hv
            have hgt : ¬value v ≤ mid := fun h => hvC ((hclass v hvR).mpr h)
            exact ⟨by omega, (hrange v hvR).2⟩
          have hchild := ih (R \ covered) (mid + 1) hi hhigh hsHigh hvalHigh hrangeHigh hspanHi
          exact (mass_mono _ (fun out hbad hmax =>
            hbad (maximizer_high_lift value R covered mid hclass hmax))).trans hchild
        · simp only [hhigh, ite_false]
          have hrangeLo : ∀ v ∈ R, lo ≤ value v ∧ value v ≤ mid := by
            intro v hv
            have hvC : v ∈ covered := by
              by_contra hvC
              exact hhigh ⟨v, Finset.mem_sdiff.mpr ⟨hv, hvC⟩⟩
            exact ⟨(hrange v hv).1, (hclass v hv).mp hvC⟩
          exact ih R lo mid hR hs hvalue hrangeLo hspanLo
      simp only [sourceMaxAtTree, hhilo, ite_false, RTree.eval_cast, RTree.eval_bind]
      calc
        _ ≤ delta + (fuel : ℝ≥0∞) * delta := mass_bind_le_add _ _ _ _ hp hnext
        _ = ((fuel + 1 : ℕ) : ℝ≥0∞) * delta := by push_cast; ring

def sourceMaxTree {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n : ℕ) (R : Finset V) (s : V) (levels scale exponent : ℕ) :
    RTree (Finset V) ℝ (Option V)
      (Nat.clog 2 (M + 1) * sourceThresholdBudget Q n levels scale exponent) :=
  sourceMaxAtTree family n s levels scale exponent (Nat.clog 2 (M + 1)) R 0 M

def IsSourceMaximum (G : WeightedGraph V) (s : V) (R : Finset V) (out : Option V) : Prop :=
  ∃ v, out = some v ∧ v ∈ R ∧ ∀ w ∈ R, stValue G w s ≤ stValue G v s

theorem sourceMaxTree_failure_le {M n scale : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (hnscale : n ≤ scale) (G : WeightedGraph V) (hG : InputPromise M G)
    (R : Finset V) (s : V) (levels exponent : ℕ)
    (hlevels : thresholdLevels n ≤ levels) (hR : R.Nonempty) (hs : s ∉ R) :
    mass ((sourceMaxTree family n R s levels scale exponent).eval G.cut)
      (fun out => ¬IsSourceMaximum G s R out) ≤
        (Nat.clog 2 (M + 1) : ℝ≥0∞) * ((((scale + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ exponent) := by
  let value := sourceValueNat G hG.1 s
  have hvalues (v : V) (hv : v ∈ R) : stValue G v s = (value v : ℝ) :=
    sourceValueNat_eq G hG.1 (fun he => hs (he ▸ hv))
  have hrange (v : V) (_hv : v ∈ R) : 0 ≤ value v ∧ value v ≤ M :=
    ⟨Nat.zero_le _, sourceValueNat_le G hG s v⟩
  have hspan : M < 0 + 2 ^ Nat.clog 2 (M + 1) := by
    have h := Nat.le_pow_clog (by decide : 1 < 2) (M + 1)
    omega
  have hfail := sourceMaxAtTree_failure_le family hvn hQ hnscale G hG s value levels exponent
    hlevels (Nat.clog 2 (M + 1)) R 0 M hR hs hvalues hrange hspan
  apply le_trans (mass_mono _ (fun out hbad hmax => ?_)) hfail
  apply hbad
  obtain ⟨v, ho, hv, htop⟩ := hmax
  refine ⟨v, ho, hv, fun w hw => ?_⟩
  rw [hvalues w hw, hvalues v hv]
  exact_mod_cast htop w hw

end
end CutQueryComplexity.GHReduction
