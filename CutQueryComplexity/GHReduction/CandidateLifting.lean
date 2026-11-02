import CutQueryComplexity.GHReduction.Candidates

/-! # Lifting recursive candidates and retaining the best witness

A complement proxy represents every vertex outside its child shore. Looking up
the child result at the image of each original target implements the required
broadcast when the original source belongs to that child.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical
open WeightedGraph

variable {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

def filterCandidate (s t : V) : Option (CutCandidate V) → Option (CutCandidate V)
  | none => none
  | some C => if t ∈ C.shore ∧ s ∉ C.shore then some C else none

theorem filterCandidate_valid (G : WeightedGraph V) (s t : V)
    {a : Option (CutCandidate V)} (ha : ∀ A, a = some A → A.value = G.cut A.shore)
    {C : CutCandidate V} (h : filterCandidate s t a = some C) : CandidateValid G s t C := by
  cases a with
  | none => simp [filterCandidate] at h
  | some A =>
    by_cases hf : t ∈ A.shore ∧ s ∉ A.shore
    · rw [filterCandidate, if_pos hf] at h
      simp only [Option.some.injEq] at h
      subst C
      exact ⟨hf.1, hf.2, ha A rfl⟩
    · simp [filterCandidate, hf] at h

theorem filterCandidate_of_valid (G : WeightedGraph V) {s t : V} {C : CutCandidate V}
    (hC : CandidateValid G s t C) : filterCandidate s t (some C) = some C := by
  simp [filterCandidate, hC.1, hC.2.1]

def pullCandidate (π : V → W) (s t : V) (a : Option (CutCandidate W)) : Option (CutCandidate V) :=
  filterCandidate s t (a.map (fun C => ⟨pull π C.shore, C.value⟩))

theorem pullCandidate_valid (G : WeightedGraph V) (π : V → W) (s t : V)
    {a : Option (CutCandidate W)}
    (ha : ∀ A, a = some A → A.value = (G.contract π).cut A.shore)
    {C : CutCandidate V} (h : pullCandidate π s t a = some C) : CandidateValid G s t C := by
  unfold pullCandidate at h
  refine filterCandidate_valid G s t ?_ h
  intro B hB
  obtain ⟨A, hA, he⟩ := Option.map_eq_some_iff.mp hB
  subst B
  simpa only [cut_contract] using ha A hA

theorem pullCandidate_of_valid (G : WeightedGraph V) (π : V → W) (s t : V)
    {C : CutCandidate W} (hC : CandidateValid (G.contract π) (π s) (π t) C) :
    pullCandidate π s t (some C) = some ⟨pull π C.shore, C.value⟩ := by
  simp only [pullCandidate, Option.map_some]
  apply filterCandidate_of_valid G
  exact ⟨(mem_pull _ _ _).mpr hC.1, fun hs => hC.2.1 ((mem_pull _ _ _).mp hs),
    by simpa only [cut_contract] using hC.2.2⟩

def bestCandidates : List (Option (CutCandidate V)) → Option (CutCandidate V)
  | [] => none
  | a :: rest => chooseCandidate a (bestCandidates rest)

theorem bestCandidates_valid (G : WeightedGraph V) (s t : V)
    (xs : List (Option (CutCandidate V)))
    (hx : ∀ a ∈ xs, ∀ C, a = some C → CandidateValid G s t C)
    {C : CutCandidate V} (h : bestCandidates xs = some C) : CandidateValid G s t C := by
  induction xs generalizing C with
  | nil => simp [bestCandidates] at h
  | cons a xs ih =>
    apply chooseCandidate_valid G s t (hx a (by simp)) ?_ h
    intro B hB
    exact ih (fun b hb => hx b (by simp [hb])) hB

theorem bestCandidates_exact (G : WeightedGraph V) (s t : V)
    (xs : List (Option (CutCandidate V)))
    (hx : ∀ a ∈ xs, ∀ C, a = some C → CandidateValid G s t C)
    {A : CutCandidate V} (hA : CandidateExact G s t A) (hmem : some A ∈ xs) :
    ∃ C, bestCandidates xs = some C ∧ CandidateExact G s t C := by
  induction xs with
  | nil => simp at hmem
  | cons a xs ih =>
    rcases List.mem_cons.mp hmem with he | hmem
    · subst a
      exact chooseCandidate_exact_left G s t hA
        (fun C hC => bestCandidates_valid G s t xs (fun b hb => hx b (by simp [hb])) hC)
    · obtain ⟨B, hB, hBexact⟩ := ih (fun b hb => hx b (by simp [hb])) hmem
      simpa only [bestCandidates, hB] using chooseCandidate_exact_right G s t
        (hx a (by simp)) hBexact

theorem chooseCandidate_le_left (A : CutCandidate V) (b : Option (CutCandidate V)) :
    ∃ C, chooseCandidate (some A) b = some C ∧ C.value ≤ A.value := by
  cases b with
  | none => exact ⟨A, rfl, le_rfl⟩
  | some B =>
    by_cases hle : A.value ≤ B.value
    · exact ⟨A, by simp [chooseCandidate, hle], le_rfl⟩
    · exact ⟨B, by simp [chooseCandidate, hle], le_of_not_ge hle⟩

theorem chooseCandidate_le_right (a : Option (CutCandidate V)) (B : CutCandidate V) :
    ∃ C, chooseCandidate a (some B) = some C ∧ C.value ≤ B.value := by
  cases a with
  | none => exact ⟨B, rfl, le_rfl⟩
  | some A =>
    by_cases hle : A.value ≤ B.value
    · exact ⟨A, by simp [chooseCandidate, hle], hle⟩
    · exact ⟨B, by simp [chooseCandidate, hle], le_rfl⟩

theorem bestCandidates_le (xs : List (Option (CutCandidate V))) {A : CutCandidate V}
    (hA : some A ∈ xs) : ∃ C, bestCandidates xs = some C ∧ C.value ≤ A.value := by
  induction xs with
  | nil => simp at hA
  | cons a xs ih =>
    rcases List.mem_cons.mp hA with he | hA
    · subst a
      exact chooseCandidate_le_left A (bestCandidates xs)
    · obtain ⟨B, hB, hle⟩ := ih hA
      obtain ⟨C, hC, hCB⟩ := chooseCandidate_le_right a B
      exact ⟨C, by simpa only [bestCandidates, hB] using hC, hCB.trans hle⟩

end
end CutQueryComplexity.GHReduction
