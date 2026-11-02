import CutQueryComplexity.GHReduction.CutUncrossing

/-! # Numeric guide estimates and their contraction interface

Two-respecting guide calls return values, not necessarily individual shore
witnesses. `none` is an absent bound. Minimum selection preserves upper bounds
and any exact entry. Pulling a child value requires distinct quotient terminals;
equality additionally follows from an actual representable parent minimum.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical
open WeightedGraph

def minEstimate (a b : Option ℝ) : Option ℝ :=
  match a, b with
  | none, b => b
  | a, none => a
  | some a, some b => some (min a b)

def bestEstimates : List (Option ℝ) → Option ℝ
  | [] => none
  | a :: L => minEstimate a (bestEstimates L)

def EstimateAbove (lower : ℝ) (estimate : Option ℝ) : Prop :=
  ∀ value, estimate = some value → lower ≤ value

theorem minEstimate_above {lower : ℝ} {a b : Option ℝ}
    (ha : EstimateAbove lower a) (hb : EstimateAbove lower b) :
    EstimateAbove lower (minEstimate a b) := by
  cases a with
  | none => exact hb
  | some a =>
    cases b with
    | none => exact ha
    | some b =>
      intro value hvalue
      have heq : min a b = value := Option.some.inj hvalue
      rw [← heq]
      exact le_min (ha a rfl) (hb b rfl)

theorem bestEstimates_above {lower : ℝ} (L : List (Option ℝ))
    (h : ∀ a ∈ L, EstimateAbove lower a) : EstimateAbove lower (bestEstimates L) := by
  induction L with
  | nil => intro value hvalue; cases hvalue
  | cons a L ih =>
    exact minEstimate_above (h a List.mem_cons_self)
      (ih (fun b hb => h b (List.mem_cons_of_mem _ hb)))

theorem minEstimate_exact_left {lower : ℝ} {b : Option ℝ}
    (hb : EstimateAbove lower b) : minEstimate (some lower) b = some lower := by
  cases b with
  | none => rfl
  | some b => simp only [minEstimate, min_eq_left (hb b rfl)]

theorem minEstimate_exact_right {lower : ℝ} {a : Option ℝ}
    (ha : EstimateAbove lower a) : minEstimate a (some lower) = some lower := by
  cases a with
  | none => rfl
  | some a => simp only [minEstimate, min_eq_right (ha a rfl)]

theorem bestEstimates_exact {lower : ℝ} (L : List (Option ℝ))
    (h : ∀ a ∈ L, EstimateAbove lower a) (hexact : some lower ∈ L) :
    bestEstimates L = some lower := by
  induction L with
  | nil => simp at hexact
  | cons a L ih =>
    have htail : ∀ b ∈ L, EstimateAbove lower b :=
      fun b hb => h b (List.mem_cons_of_mem _ hb)
    rcases List.mem_cons.mp hexact with heq | hexact
    · rw [← heq, bestEstimates]
      exact minEstimate_exact_left (bestEstimates_above L htail)
    · rw [bestEstimates, ih htail hexact]
      exact minEstimate_exact_right (h a List.mem_cons_self)

variable {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

def candidateEstimate (candidate : Option (CutCandidate V)) : Option ℝ :=
  candidate.map CutCandidate.value

theorem candidateEstimate_above (G : WeightedGraph V) {s t : V}
    {candidate : Option (CutCandidate V)}
    (h : ∀ C, candidate = some C → CandidateValid G s t C) :
    EstimateAbove (stValue G t s) (candidateEstimate candidate) := by
  cases candidate with
  | none => intro value hvalue; cases hvalue
  | some C =>
    intro value hvalue
    have heq : C.value = value := Option.some.inj hvalue
    rw [← heq]
    exact (h C rfl).upper G

theorem candidateEstimate_exact (G : WeightedGraph V) {s t : V} {C : CutCandidate V}
    (h : CandidateExact G s t C) :
    candidateEstimate (some C) = some (stValue G t s) := by
  exact congrArg some (h.value_eq G)

theorem stValue_le_contract (G : WeightedGraph V) (π : V → W) {s t : V}
    (hst : π t ≠ π s) : stValue G t s ≤ stValue (G.contract π) (π t) (π s) := by
  obtain ⟨S, hS, hvalue⟩ := exists_stMinCut (G.contract π) hst
  rw [← hvalue, cut_contract]
  exact stValue_le G ((mem_pull π S t).mpr hS.1)
    (fun hs => hS.2.1 ((mem_pull π S s).mp hs))

theorem stValue_contract_eq_of_representable (G : WeightedGraph V) (π : V → W)
    {s t : V} {X : Finset W} (hX : IsSTMinCut G t s (pull π X)) :
    stValue (G.contract π) (π t) (π s) = stValue G t s := by
  have hchild := minCut_contract_of_pull G π hX rfl
  rw [← stValue_eq_of_minCut _ hchild, cut_contract]
  exact stValue_eq_of_minCut G hX

def pullEstimate (π : V → W) (s t : V) (output : W → Option ℝ) : Option ℝ :=
  if π t = π s then none else output (π t)

theorem pullEstimate_above (G : WeightedGraph V) (π : V → W) (s t : V)
    (output : W → Option ℝ)
    (h : EstimateAbove (stValue (G.contract π) (π t) (π s)) (output (π t))) :
    EstimateAbove (stValue G t s) (pullEstimate π s t output) := by
  by_cases hst : π t = π s
  · intro value hvalue
    simp [pullEstimate, hst] at hvalue
  · intro value hvalue
    exact (stValue_le_contract G π hst).trans
      (h value (by simpa only [pullEstimate, hst, ite_false] using hvalue))

theorem pullEstimate_exact (G : WeightedGraph V) (π : V → W) {s t : V}
    {X : Finset W} (hX : IsSTMinCut G t s (pull π X))
    (output : W → Option ℝ)
    (h : output (π t) = some (stValue (G.contract π) (π t) (π s))) :
    pullEstimate π s t output = some (stValue G t s) := by
  have hst : π t ≠ π s := by
    intro heq
    exact hX.2.1 ((mem_pull π X s).mpr (heq ▸ (mem_pull π X t).mp hX.1))
  rw [pullEstimate, if_neg hst, h, stValue_contract_eq_of_representable G π hX]

end
end CutQueryComplexity.GHReduction
