import CutQueryComplexity.GHReduction.RandomPrograms
import CutQueryComplexity.GHReduction.GuideSampling

/-! # Repetition of an actual randomized query tree

The evaluation law is the product distribution of fresh runs. The operational
law adds realized costs, so amplification can be used inside a history-dependent
recursive call without replacing its query ledger by an expectation bound.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical ENNReal
open Probability

variable {I A O : Type} {q : ℕ}

def randomRepeat (T : RTree I A O q) : (h : ℕ) → RTree I A (List O) (h * q)
  | 0 => RTree.pure (PMF.pure [])
  | h + 1 => (T.bind (fun output => (randomRepeat T h).map (List.cons output))).cast
      (by rw [Nat.succ_mul, Nat.add_comm])

theorem randomRepeat_eval (T : RTree I A O q) (h : ℕ) (read : I → A) :
    (randomRepeat T h).eval read = independentSamples (T.eval read) h := by
  induction h with
  | zero => simp [randomRepeat, independentSamples]
  | succ h ih =>
    simp only [randomRepeat, RTree.eval_cast, RTree.eval_bind, RTree.eval_map,
      ih, independentSamples]

theorem independentSamples_member {α : Type} (P : PMF α) (h : ℕ) {L : List α}
    (hL : L ∈ (independentSamples P h).support) {a : α} (ha : a ∈ L) : a ∈ P.support := by
  induction h generalizing L with
  | zero =>
    have heq := (PMF.mem_support_pure_iff _ _).mp hL
    subst L
    simp at ha
  | succ h ih =>
    obtain ⟨first, hfirst, hMapped⟩ := (PMF.mem_support_bind_iff _ _ _).mp hL
    obtain ⟨tail, htail, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hMapped
    rw [← heq] at ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hfirst
    · exact ih htail ha

theorem randomRepeat_member (T : RTree I A O q) (h : ℕ) (read : I → A)
    {L : List O} (hL : L ∈ ((randomRepeat T h).eval read).support)
    {output : O} (hout : output ∈ L) : output ∈ (T.eval read).support := by
  rw [randomRepeat_eval] at hL
  exact independentSamples_member (T.eval read) h hL hout

theorem randomRepeat_failure_le (T : RTree I A O q) (h : ℕ) (read : I → A)
    (Bad : O → Prop) {δ : ℝ≥0∞} (hbad : mass (T.eval read) Bad ≤ δ) :
    mass ((randomRepeat T h).eval read) (fun L => ∀ output ∈ L, Bad output) ≤ δ ^ h := by
  rw [randomRepeat_eval]
  exact mass_all_independentSamples_le (T.eval read) Bad hbad h

theorem randomRepeat_cost (T : RTree I A O q) (h : ℕ) (read : I → A)
    (scale budget : ℕ)
    (hcost : ∀ p ∈ (RTree.run read T).support, scale * p.2 ≤ budget)
    {p : List O × ℕ} (hp : p ∈ (RTree.run read (randomRepeat T h)).support) :
    scale * p.2 ≤ h * budget := by
  induction h generalizing p with
  | zero =>
    simp only [randomRepeat, RTree.run_pure, PMF.pure_map] at hp
    have heq := (PMF.mem_support_pure_iff _ _).mp hp
    subst p
    simp
  | succ h ih =>
    simp only [randomRepeat, RTree.run_cast, RTree.run_bind] at hp
    obtain ⟨first, hfirst, hMapped⟩ := (PMF.mem_support_bind_iff _ _ _).mp hp
    obtain ⟨second, hsecond, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hMapped
    rw [random_run_map] at hsecond
    obtain ⟨tail, htail, htailEq⟩ := (PMF.mem_support_map_iff _ _ _).mp hsecond
    have hfirstCost := hcost first hfirst
    have htailCost := ih htail
    rw [← heq, ← htailEq]
    simp only [Nat.mul_add, Nat.succ_mul]
    omega

end
end CutQueryComplexity.GHReduction
