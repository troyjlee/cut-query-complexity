import CutQueryComplexity.GHReduction.Specification
import Mathlib.Tactic.FinCases

/-! # Actual canonical cuts between public terminal groups

Two nonempty disjoint groups are contracted to distinct terminals; all other
vertices retain individual labels. This is an exact contraction, with one
original query per virtual query and the actual compact vertex count.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical
open WeightedGraph

variable {V : Type} [Fintype V] [DecidableEq V]

abbrev SetCutVertex (A B : Finset V) := Fin 2 ⊕ {v : V // v ∉ A ∧ v ∉ B}

def setCutMap (A B : Finset V) (v : V) : SetCutVertex A B :=
  if ha : v ∈ A then Sum.inl 0 else if hb : v ∈ B then Sum.inl 1 else Sum.inr ⟨v, ha, hb⟩

theorem setCutMap_surjective {A B : Finset V} (hAB : Disjoint A B)
    (hA : A.Nonempty) (hB : B.Nonempty) : Function.Surjective (setCutMap A B) := by
  rintro (i | ⟨v, hv⟩)
  · fin_cases i
    · obtain ⟨a, ha⟩ := hA
      exact ⟨a, by simp [setCutMap, ha]⟩
    · obtain ⟨b, hb⟩ := hB
      have ha : b ∉ A := fun ha => Finset.disjoint_left.mp hAB ha hb
      exact ⟨b, by simp [setCutMap, ha, hb]⟩
  · exact ⟨v, by simp [setCutMap, hv.1, hv.2]⟩

theorem setCutVertex_card_le {A B : Finset V} (hAB : Disjoint A B)
    (hA : A.Nonempty) (hB : B.Nonempty) :
    Fintype.card (SetCutVertex A B) ≤ Fintype.card V :=
  Fintype.card_le_of_surjective _ (setCutMap_surjective hAB hA hB)

/-- A feasible original shore represented on the two-group quotient. -/
def setCutShore (A B S : Finset V) : Finset (SetCutVertex A B) :=
  Finset.univ.filter (fun v => match v with
    | Sum.inl i => i = 0
    | Sum.inr v => v.val ∈ S)

theorem setCutShore_source (A B S : Finset V) :
    Sum.inl (0 : Fin 2) ∈ setCutShore A B S := by simp [setCutShore]

theorem setCutShore_sink (A B S : Finset V) :
    Sum.inl (1 : Fin 2) ∉ setCutShore A B S := by simp [setCutShore]

theorem pull_setCutShore {A B S : Finset V} (hAS : A ⊆ S) (hSB : Disjoint S B) :
    pull (setCutMap A B) (setCutShore A B S) = S := by
  ext v
  by_cases ha : v ∈ A
  · simp [setCutMap, setCutShore, ha, hAS ha]
  · by_cases hb : v ∈ B
    · have hs : v ∉ S := fun hs => Finset.disjoint_left.mp hSB hs hb
      simp [setCutMap, setCutShore, ha, hb, hs]
    · simp [setCutMap, setCutShore, ha, hb]

theorem trace_feasible {A B S : Finset V} (hAB : Disjoint A B)
    (hS : S ∩ (A ∪ B) = A) : A ⊆ S ∧ Disjoint S B := by
  constructor
  · intro v hv
    have h : v ∈ S ∩ (A ∪ B) := by rw [hS]; exact hv
    exact (Finset.mem_inter.mp h).1
  · apply Finset.disjoint_left.mpr
    intro v hvS hvB
    have h : v ∈ A := by
      rw [← hS]
      exact Finset.mem_inter.mpr ⟨hvS, Finset.mem_union_right _ hvB⟩
    exact Finset.disjoint_left.mp hAB h hvB

theorem setCutPull_trace {A B : Finset V} (hAB : Disjoint A B)
    {S : Finset (SetCutVertex A B)}
    (hs : Sum.inl (0 : Fin 2) ∈ S) (ht : Sum.inl (1 : Fin 2) ∉ S) :
    pull (setCutMap A B) S ∩ (A ∪ B) = A := by
  ext v
  by_cases ha : v ∈ A
  · simp [setCutMap, ha, hs]
  · by_cases hb : v ∈ B
    · simp [setCutMap, ha, hb, ht]
    · simp [ha, hb]

theorem minTrace_to_setCut (G : WeightedGraph V) {A B S : Finset V}
    (hAB : Disjoint A B) (hS : IsMinTraceCut G (A ∪ B) A S) :
    IsSTMinCut (G.contract (setCutMap A B)) (Sum.inl 0) (Sum.inl 1) (setCutShore A B S) := by
  obtain ⟨hAS, hSB⟩ := trace_feasible hAB hS.1
  refine ⟨setCutShore_source A B S, setCutShore_sink A B S, fun T hs ht => ?_⟩
  simpa only [cut_contract, pull_setCutShore hAS hSB] using
    hS.2 (pull (setCutMap A B) T) (setCutPull_trace hAB hs ht)

theorem canonical_setCut_pull (G : WeightedGraph V) {A B : Finset V}
    (hAB : Disjoint A B) {S : Finset (SetCutVertex A B)}
    (hS : IsCanonicalSTCut (G.contract (setCutMap A B)) (Sum.inl 0) (Sum.inl 1) S) :
    IsCanonicalTraceCut G (A ∪ B) A (pull (setCutMap A B) S) := by
  have htrace := setCutPull_trace hAB hS.1.1 hS.1.2.1
  have hmin : IsMinTraceCut G (A ∪ B) A (pull (setCutMap A B) S) := by
    refine ⟨htrace, fun T hT => ?_⟩
    obtain ⟨hAT, hTB⟩ := trace_feasible hAB hT
    have h := hS.1.2.2 (setCutShore A B T) (setCutShore_source _ _ _)
      (setCutShore_sink _ _ _)
    simpa only [cut_contract, pull_setCutShore hAT hTB] using h
  refine ⟨hmin, fun T hT => ?_⟩
  obtain ⟨hAT, hTB⟩ := trace_feasible hAB hT.1
  have hsub := hS.2 (setCutShore A B T) (minTrace_to_setCut G hAB hT)
  have hpull : pull (setCutMap A B) S ⊆ pull (setCutMap A B) (setCutShore A B T) := by
    intro v hv
    exact (mem_pull _ _ _).mpr (hsub ((mem_pull _ _ _).mp hv))
  rwa [pull_setCutShore hAT hTB] at hpull

/-- A concrete group-cut program with the actual contracted vertex count. -/
def setCutProgram {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (A B : Finset V) : DTree (Finset V) ℝ (Finset V) (Q (Fintype.card (SetCutVertex A B))) :=
  (contractDetProgram (setCutMap A B)
    (canonicalSTProgram family (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2)))).map
      (pull (setCutMap A B))

theorem setCutProgram_correct {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (hG : InputPromise M G) {A B : Finset V}
    (hAB : Disjoint A B) :
    IsCanonicalTraceCut G (A ∪ B) A ((setCutProgram family A B).eval G.cut) := by
  rw [setCutProgram, DTree.eval_map, contractDetProgram_eval]
  apply canonical_setCut_pull G hAB
  apply canonicalSTProgram_correct family _
    (show InputPromise M (G.contract (setCutMap A B)) from
      ⟨integral_contract G hG.1 _, (edgeMass_contract_le G _).trans hG.2⟩)
  simp

end
end CutQueryComplexity.GHReduction
