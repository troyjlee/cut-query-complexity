import CutQueryComplexity.GHReduction.GuideAuxiliaryCosts

/-! # The complete randomized source-switch branch

This program runs the threshold-based maximum search and then the actual
one-respecting branch. A single conditional maximum-search failure charge
controls both one-sidedness and simultaneous completeness for all retained
targets. Every oracle history has a public finite query cap.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical ENNReal
open Probability

variable {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]

def guideSwitchContinuation {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n : ℕ) (T : GuideTree V N) (C : Finset N) (choice : Option N) :
    RTree (Finset V) ℝ (V → Option ℝ) (sourceSwitchBudget Q n) :=
  match choice with
  | none => RTree.pure (PMF.pure (fun _ => none))
  | some a => if ha : a ∈ outsideGuideNodes T C then
      RTree.ofDeterministic (sourceSwitchGlobalTree family n T C a ha)
    else RTree.pure (PMF.pure (fun _ => none))

def guideSwitchTree {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n : ℕ) (T : GuideTree V N) (C : Finset N) (levels scale exponent : ℕ) :
    RTree (Finset V) ℝ (V → Option ℝ)
      (Nat.clog 2 (M + 1) * sourceThresholdBudget Q n levels scale exponent + sourceSwitchBudget Q n) :=
  (guideMaximumTree family n T C levels scale exponent).bind
    (guideSwitchContinuation family n T C)

def SourceSwitchSuccess (G : WeightedGraph V) (T : GuideTree V N) (C : Finset N)
    (output : V → Option ℝ) : Prop :=
  (∀ t value, output t = some value → stValue G t T.source ≤ value) ∧
    ∀ t ∈ T.real, t ∉ C → ∀ S : Finset V, IsSTMinCut G (T.label t) T.source S →
      ∀ A : Finset N, (∀ v ∈ T.real, v ∈ A ↔ T.label v ∈ S) →
        (T.tree.crossSet A).card ≤ 2 → ∀ e ∈ T.tree.crossSet A,
          (e ∈ C ∨ T.tree.parent e ∈ C) → output (T.label t) = some (stValue G (T.label t) T.source)

theorem guideSwitchContinuation_good {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (C : Finset N) (hs : T.sourceNode ∈ C)
    (hbranch : IsCentroidBranch T.tree T.centroid C)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (choice : Option N) (hmax : IsGuideMaximum G T C choice) :
    ∃ output, (guideSwitchContinuation family n T C choice).eval G.cut = PMF.pure output ∧
      SourceSwitchSuccess G T C output := by
  obtain ⟨a, rfl, ha, htop⟩ := hmax
  have has : T.source ≠ T.label a := by
    intro he
    have hnode : T.sourceNode = a := T.label_injective T.source_real
      (Finset.mem_inter.mp ha).1 he
    exact (Finset.mem_compl.mp (Finset.mem_inter.mp ha).2) (hnode ▸ hs)
  let output := Prog.eval G.cut (sourceSwitchProgram family T C a ha)
  refine ⟨output, ?_, ?_, ?_⟩
  · simp only [guideSwitchContinuation, ha, dite_true, RTree.eval,
      RTree.run_ofDeterministic, PMF.pure_map]
    apply congrArg PMF.pure
    change (sourceSwitchGlobalTree family n T C a ha).eval G.cut = output
    exact sourceSwitchGlobalTree_eval family G hG T C a ha hvn hQ
  · intro t value hvalue
    exact sourceSwitchProgram_upper family G hG T C a ha has htop hvalue
  · intro t ht htC S hS A hA hcross e he heC
    have ht' : T.label t ∈ (switchedGuide T C a ha).realVertices :=
      Finset.mem_image.mpr ⟨t, Finset.mem_inter.mpr ⟨ht, Finset.mem_compl.mpr htC⟩, rfl⟩
    exact sourceSwitchProgram_complete family G hG T C a ha has hbranch htop ht'
      hS A hA hcross e he heC

/-- The bad event includes every retained target at once. Only the actual
maximum search is randomized here; the subsequent exact branch is pointwise. -/
theorem guideSwitchTree_failure_le {M n scale : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (hnscale : n ≤ scale) (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (C : Finset N) (levels exponent : ℕ)
    (hlevels : thresholdLevels n ≤ levels) (hs : T.sourceNode ∈ C)
    (hbranch : IsCentroidBranch T.tree T.centroid C)
    (houtside : (outsideGuideNodes T C).Nonempty) :
    mass ((guideSwitchTree family n T C levels scale exponent).eval G.cut)
      (fun output => ¬SourceSwitchSuccess G T C output) ≤
        (Nat.clog 2 (M + 1) : ℝ≥0∞) * ((((scale + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ exponent) := by
  have hp := guideMaximumTree_failure_le family hvn hQ hnscale G hG T C levels exponent
    hlevels hs houtside
  have hnext (choice : Option N) (hgood : ¬¬IsGuideMaximum G T C choice) :
      mass ((guideSwitchContinuation family n T C choice).eval G.cut)
        (fun output => ¬SourceSwitchSuccess G T C output) ≤ 0 := by
    obtain ⟨output, heq, hsuccess⟩ := guideSwitchContinuation_good family G hG T C hs hbranch
      hvn hQ choice (not_not.mp hgood)
    simp [heq, hsuccess]
  rw [guideSwitchTree, RTree.eval_bind]
  have h := mass_bind_le_add _ _ (fun choice => ¬IsGuideMaximum G T C choice)
    (fun output => ¬SourceSwitchSuccess G T C output) hp hnext
  simpa only [add_zero] using h

end
end CutQueryComplexity.GHReduction
