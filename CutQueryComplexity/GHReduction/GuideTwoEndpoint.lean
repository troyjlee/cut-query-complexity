import CutQueryComplexity.GHReduction.GuideTwoBudget
import CutQueryComplexity.Probability.Truncation

/-! # A hard-capped two-respecting value routine

The public program has the sharp query cap on every answer history. On promised
graphs every supported uncapped run already obeys that cap, so exact truncation
coupling adds no failure probability and no inverse-confidence query factor.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical ENNReal
open Probability

variable {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]

def guideTwoCappedTree {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n trials levels scale exponent : ℕ) (T : GuideTree V N) (hvn : Fintype.card V ≤ n) :
    RTree (Finset V) ℝ (Option (V → Option ℝ))
      (guideTwoSharpBudget M Q n trials levels scale exponent (Nat.clog 2 (n + 1))) :=
  (guideTwoTree family n trials levels scale exponent (Nat.clog 2 (n + 1)) T hvn).truncate
    (guideTwoSharpBudget M Q n trials levels scale exponent (Nat.clog 2 (n + 1)))

theorem guideTwoCappedTree_failure_le {M n scale : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q) (hnscale : n ≤ scale)
    (trials levels exponent : ℕ) (hlevels : thresholdLevels n ≤ levels)
    (G : WeightedGraph V) (hG : InputPromise M G) (T : GuideTree V N) (hvn : Fintype.card V ≤ n) :
    mass ((guideTwoCappedTree family n trials levels scale exponent T hvn).eval G.cut)
      (fun output => ¬output.elim False (GuideTwoSuccess G T)) ≤
      guideTwoError M trials scale exponent (Nat.clog 2 (n + 1)) T.real.card := by
  have hfailure := guideTwoTree_clog_failure_le family hQ hnscale trials levels exponent hlevels G hG T hvn
  rw [RTree.eval, mass_map] at hfailure
  rw [guideTwoCappedTree, RTree.eval_truncate, mass_map]
  apply le_trans (mass_mono_on_support _ ?_) hfailure
  intro p hp hbad
  have hcost := guideTwoTree_cost_le_sharp family hQ trials levels scale exponent _ G hG T hvn hp
  simpa only [hcost, ite_true, Option.elim_some] using hbad

def guideTwoValueTree {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n trials levels scale exponent : ℕ) (T : GuideTree V N) (hvn : Fintype.card V ≤ n) :
    RTree (Finset V) ℝ (V → Option ℝ)
      (guideTwoSharpBudget M Q n trials levels scale exponent (Nat.clog 2 (n + 1))) :=
  (guideTwoCappedTree family n trials levels scale exponent T hvn).map
    (fun output => output.getD (fun _ => none))

theorem guideTwoValueTree_failure_le {M n scale : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q) (hnscale : n ≤ scale)
    (trials levels exponent : ℕ) (hlevels : thresholdLevels n ≤ levels)
    (G : WeightedGraph V) (hG : InputPromise M G) (T : GuideTree V N) (hvn : Fintype.card V ≤ n) :
    mass ((guideTwoValueTree family n trials levels scale exponent T hvn).eval G.cut)
      (fun output => ¬GuideTwoSuccess G T output) ≤
      guideTwoError M trials scale exponent (Nat.clog 2 (n + 1)) T.real.card := by
  rw [guideTwoValueTree, RTree.eval_map, mass_map]
  apply le_trans (mass_mono _ ?_)
    (guideTwoCappedTree_failure_le family hQ hnscale trials levels exponent hlevels G hG T hvn)
  intro output hbad hgood
  cases output with
  | none => exact hgood
  | some out => exact hbad hgood

end
end CutQueryComplexity.GHReduction
