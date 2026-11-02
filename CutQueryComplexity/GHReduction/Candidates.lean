import CutQueryComplexity.GHReduction.Specification
import CutQueryComplexity.GHReduction.Programs

/-! # Queried cut candidates and free minimum selection

Each accepted candidate carries a feasible shore and its actual queried value.
Absence means that no finite upper bound has been found yet. Public feasibility
checks make these interfaces useful even on malformed primitive outputs.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical

variable {V : Type} [Fintype V] [DecidableEq V]

structure CutCandidate (V : Type) where
  shore : Finset V
  value : ℝ

def CandidateValid (G : WeightedGraph V) (s t : V) (C : CutCandidate V) : Prop :=
  t ∈ C.shore ∧ s ∉ C.shore ∧ C.value = G.cut C.shore

def CandidateExact (G : WeightedGraph V) (s t : V) (C : CutCandidate V) : Prop :=
  IsSTMinCut G t s C.shore ∧ C.value = G.cut C.shore

theorem CandidateExact.valid (G : WeightedGraph V) {s t : V} {C : CutCandidate V}
    (h : CandidateExact G s t C) : CandidateValid G s t C := ⟨h.1.1, h.1.2.1, h.2⟩

theorem CandidateValid.upper (G : WeightedGraph V) {s t : V} {C : CutCandidate V}
    (h : CandidateValid G s t C) : stValue G t s ≤ C.value := by
  rw [h.2.2]
  exact stValue_le G h.1 h.2.1

theorem CandidateExact.value_eq (G : WeightedGraph V) {s t : V} {C : CutCandidate V}
    (h : CandidateExact G s t C) : C.value = stValue G t s :=
  h.2.trans (stValue_eq_of_minCut G h.1)

def chooseCandidate (a b : Option (CutCandidate V)) : Option (CutCandidate V) :=
  match a, b with
  | none, b => b
  | a, none => a
  | some a, some b => if a.value ≤ b.value then some a else some b

theorem chooseCandidate_mem (a b : Option (CutCandidate V)) {C : CutCandidate V}
    (h : chooseCandidate a b = some C) : a = some C ∨ b = some C := by
  cases a with
  | none => exact Or.inr h
  | some a =>
    cases b with
    | none => exact Or.inl h
    | some b =>
      change (if a.value ≤ b.value then some a else some b) = some C at h
      split at h
      · exact Or.inl h
      · exact Or.inr h

theorem chooseCandidate_valid (G : WeightedGraph V) (s t : V)
    {a b : Option (CutCandidate V)}
    (ha : ∀ C, a = some C → CandidateValid G s t C)
    (hb : ∀ C, b = some C → CandidateValid G s t C)
    {C : CutCandidate V} (h : chooseCandidate a b = some C) : CandidateValid G s t C := by
  rcases chooseCandidate_mem a b h with h | h
  · exact ha C h
  · exact hb C h

theorem valid_le_exact_is_exact (G : WeightedGraph V) {s t : V} {A B : CutCandidate V}
    (hA : CandidateValid G s t A) (hB : CandidateExact G s t B)
    (hle : A.value ≤ B.value) : CandidateExact G s t A := by
  refine ⟨⟨hA.1, hA.2.1, fun X htX hsX => ?_⟩, hA.2.2⟩
  rw [hA.2.2, hB.2] at hle
  exact hle.trans (hB.1.2.2 X htX hsX)

theorem chooseCandidate_exact_left (G : WeightedGraph V) (s t : V)
    {A : CutCandidate V} (hA : CandidateExact G s t A)
    {b : Option (CutCandidate V)} (hb : ∀ B, b = some B → CandidateValid G s t B) :
    ∃ C, chooseCandidate (some A) b = some C ∧ CandidateExact G s t C := by
  cases b with
  | none => exact ⟨A, rfl, hA⟩
  | some B =>
    by_cases hle : A.value ≤ B.value
    · exact ⟨A, by simp [chooseCandidate, hle], hA⟩
    · exact ⟨B, by simp [chooseCandidate, hle],
        valid_le_exact_is_exact G (hb B rfl) hA (le_of_not_ge hle)⟩

theorem chooseCandidate_exact_right (G : WeightedGraph V) (s t : V)
    {a : Option (CutCandidate V)} (ha : ∀ A, a = some A → CandidateValid G s t A)
    {B : CutCandidate V} (hB : CandidateExact G s t B) :
    ∃ C, chooseCandidate a (some B) = some C ∧ CandidateExact G s t C := by
  cases a with
  | none => exact ⟨B, rfl, hB⟩
  | some A =>
    by_cases hle : A.value ≤ B.value
    · exact ⟨A, by simp [chooseCandidate, hle], valid_le_exact_is_exact G (ha A rfl) hB hle⟩
    · exact ⟨B, by simp [chooseCandidate, hle], hB⟩

/-- Ask for the candidate's value only after the public feasibility check. -/
def evaluateCandidate (s t : V) (S : Finset V) : Prog (Finset V) ℝ (Option (CutCandidate V)) :=
  if t ∈ S ∧ s ∉ S then (Prog.ask S).map (fun v => some ⟨S, v⟩) else Prog.pure none

theorem evaluateCandidate_valid (G : WeightedGraph V) (s t : V) (S : Finset V)
    {C : CutCandidate V} (h : Prog.eval G.cut (evaluateCandidate s t S) = some C) :
    CandidateValid G s t C := by
  by_cases hs : t ∈ S ∧ s ∉ S
  · rw [evaluateCandidate, if_pos hs] at h
    simp only [Prog.eval_map, Prog.eval_ask, Option.some.injEq] at h
    subst C
    exact ⟨hs.1, hs.2, rfl⟩
  · simp [evaluateCandidate, hs] at h

theorem evaluateCandidate_cost (s t : V) (S : Finset V) (read : Finset V → ℝ) :
    Prog.cost read (evaluateCandidate s t S) ≤ 1 := by
  unfold evaluateCandidate
  split <;> simp

def pairCandidateProgram {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (s t : V) : Prog (Finset V) ℝ (Option (CutCandidate V)) :=
  if s = t then Prog.pure none else
    (liftDTree (canonicalSTProgram family t s)).bind (evaluateCandidate s t)

theorem pairCandidateProgram_valid {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (s t : V) {C : CutCandidate V}
    (h : Prog.eval G.cut (pairCandidateProgram family s t) = some C) :
    CandidateValid G s t C := by
  by_cases hst : s = t
  · simp [pairCandidateProgram, hst] at h
  · simp only [pairCandidateProgram, hst, ite_false, Prog.eval_bind] at h
    exact evaluateCandidate_valid G s t _ h

theorem pairCandidateProgram_exact {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (hG : InputPromise M G) {s t : V} (hst : s ≠ t) :
    ∃ C, Prog.eval G.cut (pairCandidateProgram family s t) = some C ∧ CandidateExact G s t C := by
  let S := (canonicalSTProgram family t s).eval G.cut
  have hS := canonicalSTProgram_correct family G hG (Ne.symm hst)
  refine ⟨⟨S, G.cut S⟩, ?_, hS.1, rfl⟩
  simp [pairCandidateProgram, hst, evaluateCandidate, hS.1.1, hS.1.2.1, S]

theorem pairCandidateProgram_cost {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (s t : V) (read : Finset V → ℝ) :
    Prog.cost read (pairCandidateProgram family s t) ≤ Q (Fintype.card V) + 1 := by
  by_cases hst : s = t
  · simp [pairCandidateProgram, hst]
  · simp only [pairCandidateProgram, hst, ite_false, Prog.cost_bind]
    exact Nat.add_le_add (liftDTree_cost_le _ read) (evaluateCandidate_cost _ _ _ read)

end
end CutQueryComplexity.GHReduction
