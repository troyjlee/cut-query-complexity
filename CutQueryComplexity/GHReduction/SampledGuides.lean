import CutQueryComplexity.GHReduction.GuideTwoEndpoint
import CutQueryComplexity.GHReduction.GeometricBuckets

/-! # Sampling and solving actual terminal guides

The explicit approximator determines the guide distribution. Each sampled tree
is passed to the implemented two-respecting solver on the current graph. A
public length guard keeps the tree finite on malformed outputs; real sampled
lists satisfy it exactly. Guide edges need not be edges of the input graph.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical ENNReal BigOperators
open Probability WeightedGraph

variable {V : Type} [Fintype V] [DecidableEq V]

def terminalGuide (U : Finset V) (s : U) (T : RootedTree U) : GuideTree V U where
  tree := T
  real := Finset.univ
  label := Subtype.val
  label_injective := fun _ _ _ _ h => Subtype.ext h
  sourceNode := s
  source_real := Finset.mem_univ s

@[simp] theorem terminalGuide_source (U : Finset V) (s : U) (T : RootedTree U) :
    (terminalGuide U s T).source = s.val := rfl

@[simp] theorem terminalGuide_real_card (U : Finset V) (s : U) (T : RootedTree U) :
    (terminalGuide U s T).real.card = U.card := by simp [terminalGuide]

@[simp] theorem terminalGuide_realVertices (U : Finset V) (s : U) (T : RootedTree U) :
    (terminalGuide U s T).realVertices = U := by
  ext v
  simp [GuideTree.realVertices, terminalGuide]

theorem terminalGuide_respects (U : Finset V) (s : U) (T : RootedTree U) (S : Finset V)
    {k : ℕ} (hk : (T.crossSet (projectShore U S)).card ≤ k) :
    (terminalGuide U s T).RespectsCut S k :=
  ⟨projectShore U S, fun v _ => mem_projectShore U S v, hk⟩

def guideListEntry {U : Finset V} (L : List (RootedTree U)) {samples : ℕ}
    (hlen : L.length = samples) (i : Fin samples) : RootedTree U :=
  L.get ⟨i.val, by rw [hlen]; exact i.isLt⟩

theorem guideListEntry_mem {U : Finset V} (L : List (RootedTree U)) {samples : ℕ}
    (hlen : L.length = samples) (i : Fin samples) : guideListEntry L hlen i ∈ L :=
  List.get_mem _ _

theorem exists_guideListEntry {U : Finset V} (L : List (RootedTree U)) {samples : ℕ}
    (hlen : L.length = samples) {T : RootedTree U} (hT : T ∈ L) :
    ∃ i : Fin samples, guideListEntry L hlen i = T := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hT
  refine ⟨⟨i.val, by rw [← hlen]; exact i.isLt⟩, ?_⟩
  exact hi

def mergeGuideValues {samples : ℕ} (output : Fin samples → V → Option ℝ) (t : V) : Option ℝ :=
  bestEstimates (Finset.univ.toList.map (fun i : Fin samples => output i t))

def sampledGuideContinuation {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n samples trials levels scale exponent : ℕ) (U : Finset V) (s : U)
    (hvn : Fintype.card V ≤ n) (L : List (RootedTree U)) :
    RTree (Finset V) ℝ (V → Option ℝ)
      (samples * guideTwoBudget M Q n trials levels scale exponent (Nat.clog 2 (n + 1))) :=
  if hlen : L.length = samples then
    ((randomTable (fun _ => none) (fun i : Fin samples =>
      guideTwoTree family n trials levels scale exponent (Nat.clog 2 (n + 1))
        (terminalGuide U s (guideListEntry L hlen i)) hvn)).map mergeGuideValues).cast (by simp)
  else RTree.pure (PMF.pure (fun _ => none))

def sampledGuideTree {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n samples trials levels scale exponent : ℕ) (K : WeightedGraph V)
    (U : Finset V) (s : U) (hU : 2 ≤ U.card) (hpos : 0 < terminalMin K U)
    (hvn : Fintype.card V ≤ n) :
    RTree (Finset V) ℝ (V → Option ℝ)
      (samples * guideTwoBudget M Q n trials levels scale exponent (Nat.clog 2 (n + 1))) :=
  ((guideSampleProgram K U hU hpos samples).bind
    (sampledGuideContinuation family n samples trials levels scale exponent U s hvn)).cast (by omega)

def SourceValuesSuccess (G : WeightedGraph V) (U : Finset V) (s : V) (output : V → Option ℝ) : Prop :=
  (∀ t, EstimateAbove (stValue G t s) (output t)) ∧
    ∀ t ∈ U, t ≠ s → output t = some (stValue G t s)

def GuideListCoverage (G : WeightedGraph V) (U : Finset V) (s : V)
    (L : List (RootedTree U)) : Prop :=
  ∀ t ∈ U, t ≠ s → ∃ T ∈ L, ∃ S : Finset V,
    IsSTMinCut G t s S ∧ (T.crossSet (projectShore U S)).card ≤ 2

theorem mergeGuideValues_success (G : WeightedGraph V) (U : Finset V) (s : U)
    {samples : ℕ} (L : List (RootedTree U)) (hlen : L.length = samples)
    (hcoverage : GuideListCoverage G U s.val L) (output : Fin samples → V → Option ℝ)
    (hgood : ∀ i, GuideTwoSuccess G (terminalGuide U s (guideListEntry L hlen i)) (output i)) :
    SourceValuesSuccess G U s.val (mergeGuideValues output) := by
  have habove (t : V) : ∀ a ∈ Finset.univ.toList.map (fun i : Fin samples => output i t),
      EstimateAbove (stValue G t s.val) a := by
    intro a ha
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
    exact (hgood i).1 t
  refine ⟨fun t => bestEstimates_above _ (habove t), ?_⟩
  intro t ht hts
  obtain ⟨T, hT, S, hS, hk⟩ := hcoverage t ht hts
  obtain ⟨i, hi⟩ := exists_guideListEntry L hlen hT
  have hrespect := terminalGuide_respects U s T S hk
  have hexact := (hgood i).2 t (by simpa only [terminalGuide_realVertices] using ht)
    ⟨S, hS, by simpa only [hi] using hrespect⟩
  apply bestEstimates_exact _ (habove t)
  exact List.mem_map.mpr ⟨i, by simp, hexact⟩

end
end CutQueryComplexity.GHReduction
