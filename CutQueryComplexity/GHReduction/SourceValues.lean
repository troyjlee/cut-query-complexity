import CutQueryComplexity.GHReduction.Specification

/-! # Integral source connectivities for the public threshold search

These definitions occur only in semantic proofs. The query algorithm searches
the public integer interval `[0, M]`; it never computes these values directly
from the hidden graph.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical
open WeightedGraph

variable {V : Type} [Fintype V] [DecidableEq V]

theorem cut_nat_of_integral (G : WeightedGraph V) (hG : G.IsIntegral) (S : Finset V) :
    ∃ k : ℕ, G.cut S = k := by
  choose w hw using hG
  refine ⟨∑ u ∈ S, ∑ v ∈ Sᶜ, w u v, ?_⟩
  simp [WeightedGraph.cut, hw]

theorem stValue_nat_of_integral (G : WeightedGraph V) (hG : G.IsIntegral) {s t : V}
    (hst : s ≠ t) : ∃ k : ℕ, stValue G s t = k := by
  obtain ⟨S, _, hval⟩ := exists_stMinCut G hst
  rw [← hval]
  exact cut_nat_of_integral G hG S

def sourceValueNat (G : WeightedGraph V) (hG : G.IsIntegral) (s v : V) : ℕ :=
  if hvs : v = s then 0 else Classical.choose (stValue_nat_of_integral G hG hvs)

theorem sourceValueNat_eq (G : WeightedGraph V) (hG : G.IsIntegral) {s v : V} (hvs : v ≠ s) :
    stValue G v s = (sourceValueNat G hG s v : ℝ) := by
  simpa only [sourceValueNat, hvs, dite_false] using
    Classical.choose_spec (stValue_nat_of_integral G hG hvs)

theorem sourceValueNat_le {M : ℕ} (G : WeightedGraph V) (hG : InputPromise M G) (s v : V) :
    sourceValueNat G hG.1 s v ≤ M := by
  by_cases hvs : v = s
  · simp [sourceValueNat, hvs]
  · obtain ⟨S, _, hval⟩ := exists_stMinCut G hvs
    have hcut := (cut_le_edgeMass G S).trans hG.2
    rw [hval, sourceValueNat_eq G hG.1 hvs] at hcut
    exact_mod_cast hcut

def selectVertex (R : Finset V) : Option V :=
  if hR : R.Nonempty then some hR.choose else none

theorem selectVertex_mem (R : Finset V) (hR : R.Nonempty) :
    ∃ v ∈ R, selectVertex R = some v := by
  refine ⟨hR.choose, hR.choose_spec, ?_⟩
  simp [selectVertex, hR]

def IsMaximizer (value : V → ℕ) (R : Finset V) (out : Option V) : Prop :=
  ∃ v, out = some v ∧ v ∈ R ∧ ∀ w ∈ R, value w ≤ value v

theorem selectVertex_max_of_range (value : V → ℕ) (R : Finset V) (hR : R.Nonempty)
    {lo hi : ℕ} (hrange : ∀ v ∈ R, lo ≤ value v ∧ value v ≤ hi) (hhilo : hi ≤ lo) :
    IsMaximizer value R (selectVertex R) := by
  obtain ⟨v, hv, he⟩ := selectVertex_mem R hR
  exact ⟨v, he, hv, fun w hw => ((hrange w hw).2.trans hhilo).trans (hrange v hv).1⟩

theorem maximizer_high_lift (value : V → ℕ) (R covered : Finset V) (mid : ℕ)
    (hclass : ∀ v ∈ R, v ∈ covered ↔ value v ≤ mid) {out : Option V}
    (hmax : IsMaximizer value (R \ covered) out) : IsMaximizer value R out := by
  obtain ⟨v, ho, hv, htop⟩ := hmax
  obtain ⟨hvR, hvC⟩ := Finset.mem_sdiff.mp hv
  have hlarge : mid < value v := by
    have : ¬value v ≤ mid := fun he => hvC ((hclass v hvR).mpr he)
    omega
  refine ⟨v, ho, hvR, fun w hw => ?_⟩
  by_cases hwC : w ∈ covered
  · exact ((hclass w hw).mp hwC).trans (Nat.le_of_lt hlarge)
  · exact htop w (Finset.mem_sdiff.mpr ⟨hw, hwC⟩)

end
end CutQueryComplexity.GHReduction
