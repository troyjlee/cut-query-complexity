import CutQueryComplexity.GHReduction.TerminalGuides
import CutQueryComplexity.Probability.FiniteEvents

/-! # Independent public guide samples

The sampler takes only the explicit approximator, terminal set, and public
sample count. A family of hidden shores occurs only in its coverage theorem.
Fresh independent draws are expressed by `PMF.bind`; dependence of those
shores on any earlier history does not change the pointwise theorem.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction

noncomputable section
open scoped Classical ENNReal
open WeightedGraph Probability

variable {α : Type}

/-- An explicit list of independent draws, of exactly the public length. -/
def independentSamples (P : PMF α) : ℕ → PMF (List α)
  | 0 => PMF.pure []
  | h + 1 => P.bind (fun a => (independentSamples P h).map (List.cons a))

theorem independentSamples_length (P : PMF α) (h : ℕ) {L : List α}
    (hL : L ∈ (independentSamples P h).support) : L.length = h := by
  induction h generalizing L with
  | zero =>
      have he := (PMF.mem_support_pure_iff _ _).mp hL
      subst L
      rfl
  | succ h ih =>
      obtain ⟨a, _, hMapped⟩ := (PMF.mem_support_bind_iff _ _ _).mp hL
      obtain ⟨tail, hTail, hEq⟩ := (PMF.mem_support_map_iff _ _ _).mp hMapped
      rw [← hEq, List.length_cons]
      exact congrArg Nat.succ (ih hTail)

/-- Exact independent repetition, before any union bound over target shores. -/
theorem mass_all_independentSamples (P : PMF α) (Bad : α → Prop) (h : ℕ) :
    mass (independentSamples P h) (fun L => ∀ a ∈ L, Bad a) = (mass P Bad) ^ h := by
  induction h with
  | zero => simp [independentSamples]
  | succ h ih =>
      rw [independentSamples, mass_bind]
      have hstep (a : α) :
          mass ((independentSamples P h).map (List.cons a)) (fun L => ∀ b ∈ L, Bad b) =
            if Bad a then mass (independentSamples P h) (fun L => ∀ b ∈ L, Bad b) else 0 := by
        rw [mass_map]
        by_cases ha : Bad a <;> simp [ha]
      simp_rw [hstep]
      calc
        _ = (∑' a, if Bad a then P a else 0) *
            mass (independentSamples P h) (fun L => ∀ a ∈ L, Bad a) := by
          rw [← ENNReal.tsum_mul_right]
          apply tsum_congr
          intro a
          by_cases ha : Bad a <;> simp [ha]
        _ = (mass P Bad) ^ (h + 1) := by
          rw [← mass_eq_tsum, ih, pow_succ]
          exact mul_comm _ _

theorem mass_all_independentSamples_le (P : PMF α) (Bad : α → Prop)
    {δ : ℝ≥0∞} (hP : mass P Bad ≤ δ) (h : ℕ) :
    mass (independentSamples P h) (fun L => ∀ a ∈ L, Bad a) ≤ δ ^ h := by
  rw [mass_all_independentSamples]
  exact pow_le_pow_left₀ (show (0 : ℝ≥0∞) ≤ mass P Bad from bot_le) hP h

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Zero original queries: all selection and randomness use explicit public data. -/
def guideSampleProgram (K : WeightedGraph V) (U : Finset V) (hU : 2 ≤ U.card)
    (hpos : 0 < terminalMin K U) (h : ℕ) :
    RTree (Finset V) ℝ (List (RootedTree U)) 0 :=
  RTree.pure (independentSamples (terminalGuidePMF K U hU hpos) h)

@[simp] theorem guideSampleProgram_eval (K : WeightedGraph V) (U : Finset V)
    (hU : 2 ≤ U.card) (hpos : 0 < terminalMin K U) (h : ℕ) (read : Finset V → ℝ) :
    (guideSampleProgram K U hU hpos h).eval read =
      independentSamples (terminalGuidePMF K U hU hpos) h := by
  simp [guideSampleProgram]

theorem guideSampleProgram_cost (K : WeightedGraph V) (U : Finset V)
    (hU : 2 ≤ U.card) (hpos : 0 < terminalMin K U) (h : ℕ) (read : Finset V → ℝ)
    {out : List (RootedTree U) × ℕ}
    (hout : out ∈ (RTree.run read (guideSampleProgram K U hU hpos h)).support) :
    out.2 = 0 :=
  Nat.eq_zero_of_le_zero (RTree.cost_le _ read hout)

theorem guideSampleProgram_length (K : WeightedGraph V) (U : Finset V)
    (hU : 2 ≤ U.card) (hpos : 0 < terminalMin K U) (h : ℕ) (read : Finset V → ℝ)
    {L : List (RootedTree U)}
    (hL : L ∈ ((guideSampleProgram K U hU hpos h).eval read).support) :
    L.length = h := by
  rw [guideSampleProgram_eval] at hL
  exact independentSamples_length _ h hL

/-- A single fixed true shore is missed in all rounds with geometric probability. -/
theorem guideSampleProgram_miss_le (F K : WeightedGraph V) (U : Finset V)
    (hU : 2 ≤ U.card) (hposK : 0 < terminalMin K U)
    (happrox : ∀ S, (99 / 100 : ℝ) * F.cut S ≤ K.cut S ∧
      K.cut S ≤ (101 / 100 : ℝ) * F.cut S)
    (S : Finset V) (hsmall : F.cut S ≤ (11 / 10 : ℝ) * terminalMin F U)
    (h : ℕ) (read : Finset V → ℝ) :
    mass ((guideSampleProgram K U hU hposK h).eval read)
      (fun L => ∀ T ∈ L, 3 ≤ (T.crossSet (projectShore U S)).card) ≤
        (ENNReal.ofReal (3 / 4 : ℝ)) ^ h := by
  rw [guideSampleProgram_eval]
  exact mass_all_independentSamples_le _ _
    (terminalGuidePMF_failure_le F K U hU hposK happrox S hsmall) h

/-- Simultaneous 2-respecting coverage of any finite family of true small shores.
The shore family is absent from `guideSampleProgram`'s arguments. -/
theorem guideSampleProgram_coverage {ι : Type} [DecidableEq ι]
    (F K : WeightedGraph V) (U : Finset V) (hU : 2 ≤ U.card)
    (hposK : 0 < terminalMin K U)
    (happrox : ∀ S, (99 / 100 : ℝ) * F.cut S ≤ K.cut S ∧
      K.cut S ≤ (101 / 100 : ℝ) * F.cut S)
    (targets : Finset ι) (shore : ι → Finset V)
    (hsmall : ∀ v ∈ targets, F.cut (shore v) ≤ (11 / 10 : ℝ) * terminalMin F U)
    (h : ℕ) (read : Finset V → ℝ) :
    mass ((guideSampleProgram K U hU hposK h).eval read)
      (fun L => ¬∀ v ∈ targets, ∃ T ∈ L,
        (T.crossSet (projectShore U (shore v))).card ≤ 2) ≤
      (targets.card : ℝ≥0∞) * (ENNReal.ofReal (3 / 4 : ℝ)) ^ h := by
  let P := (guideSampleProgram K U hU hposK h).eval read
  calc
    _ ≤ mass P (fun L => ∃ v ∈ targets, ∀ T ∈ L,
          3 ≤ (T.crossSet (projectShore U (shore v))).card) := by
      apply mass_mono
      intro L hfail
      by_contra hnone
      apply hfail
      intro v hv
      by_contra hmiss
      apply hnone
      refine ⟨v, hv, fun T hT => ?_⟩
      have hn : ¬(T.crossSet (projectShore U (shore v))).card ≤ 2 :=
        fun hc => hmiss ⟨T, hT, hc⟩
      omega
    _ ≤ ∑ v ∈ targets, mass P (fun L => ∀ T ∈ L,
          3 ≤ (T.crossSet (projectShore U (shore v))).card) :=
      mass_exists_finset_le P targets _
    _ ≤ ∑ _v ∈ targets, (ENNReal.ofReal (3 / 4 : ℝ)) ^ h := by
      exact Finset.sum_le_sum (fun v hv =>
        guideSampleProgram_miss_le F K U hU hposK happrox (shore v) (hsmall v hv) h read)
    _ = _ := by simp [nsmul_eq_mul]

end
end CutQueryComplexity.GHReduction
