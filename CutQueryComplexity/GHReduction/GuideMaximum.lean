import CutQueryComplexity.GHReduction.GuideTwoCases
import CutQueryComplexity.GHReduction.ThresholdCosts

/-! # Choosing the source-switch node by actual threshold queries

Maximum-source search returns a graph vertex. A finite public lookup converts
it into a retained real guide node. Its output guard is valid on every history;
the maximum-connectivity property holds with the proved conditional error.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical ENNReal
open Probability

variable {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]

def GuideTree.nodeOfLabel (T : GuideTree V N) (R : Finset N) (v : V) : Option N :=
  if h : ∃ a ∈ R, T.label a = v then some h.choose else none

theorem GuideTree.nodeOfLabel_spec (T : GuideTree V N) (R : Finset N) {v : V} {a : N}
    (ha : T.nodeOfLabel R v = some a) : a ∈ R ∧ T.label a = v := by
  unfold nodeOfLabel at ha
  split at ha
  next h =>
    have heq := Option.some.inj ha
    exact heq ▸ h.choose_spec
  next h => simp at ha

theorem GuideTree.nodeOfLabel_exists (T : GuideTree V N) (R : Finset N) {v : V}
    (hv : v ∈ T.graphGroup R) : ∃ a ∈ R, T.nodeOfLabel R v = some a ∧ T.label a = v := by
  obtain ⟨a, ha, hav⟩ := Finset.mem_image.mp hv
  have h : ∃ a ∈ R, T.label a = v := ⟨a, ha, hav⟩
  exact ⟨h.choose, h.choose_spec.1, by simp [nodeOfLabel, h], h.choose_spec.2⟩

def outsideGuideNodes (T : GuideTree V N) (C : Finset N) : Finset N := T.real ∩ Cᶜ

theorem source_not_mem_outsideGuideVertices (T : GuideTree V N) (C : Finset N)
    (hs : T.sourceNode ∈ C) : T.source ∉ T.graphGroup (outsideGuideNodes T C) := by
  intro h
  obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp h
  obtain ⟨har, haC⟩ := Finset.mem_inter.mp ha
  have he : a = T.sourceNode := T.label_injective har T.source_real heq
  exact (Finset.mem_compl.mp haC) (he.symm ▸ hs)

def guideMaximumTree {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n : ℕ) (T : GuideTree V N) (C : Finset N) (levels scale exponent : ℕ) :
    RTree (Finset V) ℝ (Option N)
      (Nat.clog 2 (M + 1) * sourceThresholdBudget Q n levels scale exponent) :=
  (sourceMaxTree family n (T.graphGroup (outsideGuideNodes T C)) T.source
    levels scale exponent).map (fun out => out.bind (T.nodeOfLabel (outsideGuideNodes T C)))

def IsGuideMaximum (G : WeightedGraph V) (T : GuideTree V N) (C : Finset N)
    (out : Option N) : Prop :=
  ∃ a, out = some a ∧ a ∈ outsideGuideNodes T C ∧
    ∀ v ∈ T.graphGroup (outsideGuideNodes T C), stValue G v T.source ≤ stValue G (T.label a) T.source

theorem guideMaximumTree_guard {M n : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (T : GuideTree V N) (C : Finset N) (levels scale exponent : ℕ) (read : Finset V → ℝ)
    {a : N} (ha : some a ∈ ((guideMaximumTree family n T C levels scale exponent).eval read).support) :
    a ∈ outsideGuideNodes T C := by
  rw [guideMaximumTree, RTree.eval_map] at ha
  obtain ⟨out, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp ha
  cases out with
  | none => simp at heq
  | some v => exact (T.nodeOfLabel_spec (outsideGuideNodes T C) heq).1

theorem guideMaximumTree_failure_le {M n scale : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (hnscale : n ≤ scale) (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (C : Finset N) (levels exponent : ℕ)
    (hlevels : thresholdLevels n ≤ levels) (hs : T.sourceNode ∈ C)
    (houtside : (outsideGuideNodes T C).Nonempty) :
    mass ((guideMaximumTree family n T C levels scale exponent).eval G.cut)
      (fun out => ¬IsGuideMaximum G T C out) ≤
        (Nat.clog 2 (M + 1) : ℝ≥0∞) * ((((scale + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ exponent) := by
  have hR : (T.graphGroup (outsideGuideNodes T C)).Nonempty := houtside.image _
  have hp := sourceMaxTree_failure_le family hvn hQ hnscale G hG
    (T.graphGroup (outsideGuideNodes T C)) T.source levels exponent hlevels hR
    (source_not_mem_outsideGuideVertices T C hs)
  rw [guideMaximumTree, RTree.eval_map, mass_map]
  apply le_trans (mass_mono _ (fun out hbad hmax => ?_)) hp
  obtain ⟨v, heq, hv, htop⟩ := hmax
  obtain ⟨a, ha, hlookup, hav⟩ := T.nodeOfLabel_exists (outsideGuideNodes T C) hv
  apply hbad
  refine ⟨a, ?_, ha, ?_⟩
  · rw [heq]
    exact hlookup
  · intro w hw
    rw [hav]
    exact htop w hw

theorem guideMaximumTree_cost_scaled {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (T : GuideTree V N) (C : Finset N) (levels scale exponent : ℕ) (read : Finset V → ℝ)
    {p : Option N × ℕ}
    (hp : p ∈ (RTree.run read (guideMaximumTree family n T C levels scale exponent)).support) :
    n * p.2 ≤ Fintype.card V *
      (Nat.clog 2 (M + 1) * sourceThresholdBudget Q n levels scale exponent) := by
  rw [guideMaximumTree, random_run_map] at hp
  obtain ⟨r, hr, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
  rw [← heq]
  exact sourceMaxTree_cost_scaled family hvn hQ (T.graphGroup (outsideGuideNodes T C))
    T.source levels scale exponent read hr

end
end CutQueryComplexity.GHReduction
