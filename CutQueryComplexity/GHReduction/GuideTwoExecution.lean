import CutQueryComplexity.GHReduction.GuideTwoSuccess
import CutQueryComplexity.GHReduction.RandomTableFailure

/-! # Evaluation of the implemented guide recursion

The child table below is a definitional expansion of the actual program. Its
success transfer uses a represented original minimum, including the proxy
case, and its failure bound charges only the corresponding recursive call.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical ENNReal BigOperators
open Probability

variable {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]

def guideTwoChildTree {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n trials levels scale exponent fuel : ℕ) (T : GuideTree V N) (hvn : Fintype.card V ≤ n)
    (shores : T.parts → Finset V) (P : T.parts) :
    RTree (Finset V) ℝ (V → Option ℝ) (guideTwoBudget M Q n trials levels scale exponent fuel) :=
  let S := shores P
  if htrace : S ∩ T.realVertices = T.graphGroup P.val then
    (contractProgram (shoreMap S)
      (guideTwoTree family n trials levels scale exponent fuel
        (childGuide T P S htrace) ((childGuide_graph_size_le T P S htrace).trans hvn))).map
          (fun output t => pullEstimate (shoreMap S) T.source t output)
  else RTree.pure (PMF.pure (fun _ => none))

theorem guideTwoChildTree_eval {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (trials levels scale exponent fuel : ℕ)
    (G : WeightedGraph V) (hG : InputPromise M G) (T : GuideTree V N)
    (hvn : Fintype.card V ≤ n) (hlarge : 2 < T.real.card) (P : T.parts)
    (htrace : (Prog.eval G.cut (centroidShoreProgram family T) P) ∩ T.realVertices = T.graphGroup P.val) :
    (guideTwoChildTree family n trials levels scale exponent fuel T hvn
      (Prog.eval G.cut (centroidShoreProgram family T)) P).eval G.cut =
      ((guideTwoTree family n trials levels scale exponent fuel (childGuide T P _ htrace)
        ((childGuide_graph_size_le T P _ htrace).trans hvn)).eval
          (G.contract (shoreMap (Prog.eval G.cut (centroidShoreProgram family T) P))).cut).map
            (fun output t => pullEstimate (shoreMap (Prog.eval G.cut (centroidShoreProgram family T) P))
              T.source t output) := by
  simp only [guideTwoChildTree, htrace, dite_true, RTree.eval_map, contractProgram_eval]

theorem guideTwoTree_step {M n : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (trials levels scale exponent fuel : ℕ) (G : WeightedGraph V) (T : GuideTree V N)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) (hlarge : ¬T.real.card ≤ 10) :
    (guideTwoTree family n trials levels scale exponent (fuel + 1) T hvn).eval G.cut =
      ((randomTable (fun _ => none) (guideTwoChildTree family n trials levels scale exponent fuel
        T hvn (Prog.eval G.cut (centroidShoreProgram family T)))).eval G.cut).bind (fun children =>
          ((guidePruneTrialsTree family n trials T).eval G.cut).bind (fun pruned =>
            ((guideSourceBranchTree family n T levels scale exponent).eval G.cut).map
              (guideTwoCombine T (Prog.eval G.cut (centroidPairProgram family T)) children pruned))) := by
  have hnode : Prog.eval G.cut (guideNodeProgram family T) =
      (Prog.eval G.cut (centroidPairProgram family T),
        Prog.eval G.cut (centroidShoreProgram family T)) := by
    rw [guideNodeProgram, Prog.eval_bind, Prog.eval_map]
  rw [guideTwoTree, ite_eq_right hlarge, RTree.eval_weaken, RTree.eval_bind,
    guideNodeTree_eval family T hvn hQ, hnode, PMF.pure_bind]
  simp only [RTree.eval_bind,
    RTree.eval_map, RTree.eval_weaken]
  unfold guideTwoChildTree
  rfl

theorem guideTwoChildTree_failure_le {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (trials levels scale exponent fuel : ℕ)
    (G : WeightedGraph V) (hG : InputPromise M G) (T : GuideTree V N)
    (hvn : Fintype.card V ≤ n) (hlarge : 2 < T.real.card) (P : T.parts)
    {δ : ℝ≥0∞}
    (hrec : ∀ (htrace : (Prog.eval G.cut (centroidShoreProgram family T) P) ∩ T.realVertices =
        T.graphGroup P.val),
      mass ((guideTwoTree family n trials levels scale exponent fuel (childGuide T P _ htrace)
        ((childGuide_graph_size_le T P _ htrace).trans hvn)).eval
          (G.contract (shoreMap (Prog.eval G.cut (centroidShoreProgram family T) P))).cut)
        (fun output => ¬GuideTwoSuccess
          (G.contract (shoreMap (Prog.eval G.cut (centroidShoreProgram family T) P)))
          (childGuide T P _ htrace) output) ≤ δ) :
    mass ((guideTwoChildTree family n trials levels scale exponent fuel T hvn
      (Prog.eval G.cut (centroidShoreProgram family T)) P).eval G.cut)
      (fun output => ¬GuideChildSuccess family G T P output) ≤ δ := by
  have htrace := (centroidShoreProgram_correct family G hG T hlarge P).1.1
  rw [guideTwoChildTree_eval family trials levels scale exponent fuel G hG T hvn hlarge P htrace,
    mass_map]
  apply le_trans (mass_mono _ ?_) (hrec htrace)
  intro output hbad hgood
  exact hbad (guideChildSuccess_of_child family G T P htrace output hgood)

theorem guideTwoTree_step_failure_le {M n scale : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (trials levels exponent fuel : ℕ)
    (G : WeightedGraph V) (hG : InputPromise M G) (T : GuideTree V N)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) (hnscale : n ≤ scale)
    (hlevels : thresholdLevels n ≤ levels) (hlarge : ¬T.real.card ≤ 10)
    (δ : T.parts → ℝ≥0∞)
    (hchildren : ∀ P, mass ((guideTwoChildTree family n trials levels scale exponent fuel T hvn
      (Prog.eval G.cut (centroidShoreProgram family T)) P).eval G.cut)
      (fun output => ¬GuideChildSuccess family G T P output) ≤ δ P) :
    mass ((guideTwoTree family n trials levels scale exponent (fuel + 1) T hvn).eval G.cut)
      (fun output => ¬GuideTwoSuccess G T output) ≤
      (∑ P, δ P) + ((T.real.card : ℝ≥0∞) * ENNReal.ofReal (3 / 4 : ℝ) ^ trials +
        (Nat.clog 2 (M + 1) : ℝ≥0∞) * ((((scale + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ exponent)) := by
  have hlarge' : 2 < T.real.card := by omega
  have htable := randomTable_failure_le (fun _ => none)
    (guideTwoChildTree family n trials levels scale exponent fuel T hvn
      (Prog.eval G.cut (centroidShoreProgram family T))) G.cut
    (GuideChildSuccess family G T) δ hchildren
  rw [guideTwoTree_step family trials levels scale exponent fuel G T hvn hQ hlarge]
  apply mass_bind_le_add _ _ (fun children => ¬∀ P, GuideChildSuccess family G T P (children P)) _ htable
  intro children hchildrenGood
  have hc : ∀ P, GuideChildSuccess family G T P (children P) := not_not.mp hchildrenGood
  apply mass_bind_le_add _ _ (fun output => ¬PruningSuccess G T output) _
    (guidePruneTrialsTree_simultaneous family G hG T hvn hQ trials)
  intro pruned hprunedGood
  have hp : PruningSuccess G T pruned := not_not.mp hprunedGood
  rw [mass_map]
  apply le_trans (mass_mono _ ?_)
    (guideSourceBranchTree_failure_le family hvn hQ hnscale G hG T levels exponent hlevels)
  intro switched hfail hs
  exact hfail (guideTwoCombine_success family G hG T hlarge' children pruned switched hc hp hs)

end
end CutQueryComplexity.GHReduction
