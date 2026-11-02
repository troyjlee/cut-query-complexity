import CutQueryComplexity.GHReduction.GuideOneComplete
import CutQueryComplexity.GHReduction.SourceMaximum

/-! # The source-switching branch, including equal source values

After selecting a maximum-connectivity terminal outside the source branch,
one exact pair call supplies the maximum value. That value is a valid upper
bound for every retained target. Taking its minimum with the one-respecting
answer from the new source handles ties without requiring a cut shore from
the numeric guide solver. The maximum-selection algorithm is separate and
its Monte Carlo failure must be charged by the caller.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical
open WeightedGraph

variable {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]

theorem stValue_symm (G : WeightedGraph V) (s t : V) : stValue G s t = stValue G t s := by
  by_cases hst : s = t
  · simp only [hst]
  · obtain ⟨S, hS, hval⟩ := exists_stMinCut G hst
    have hcomp := stValue_eq_of_minCut G (stMinCut_compl G hS)
    rw [cut_compl, hval] at hcomp
    exact hcomp

theorem sourceSwitch_lower (G : WeightedGraph V) {s a t : V} (hat : a ≠ t)
    (hmax : stValue G t s ≤ stValue G a s) : stValue G t s ≤ stValue G t a := by
  have h := stValue_triangle G s a t hat
  rw [stValue_symm G s a, stValue_symm G s t, min_eq_right hmax,
    stValue_symm G a t] at h
  exact h

/-- Strictly smaller targets keep the same minimum shore after the source is
switched. This is the shore whose crossing witness survives branch deletion. -/
theorem sourceSwitch_minCut (G : WeightedGraph V) {s a t : V} {C : Finset V}
    (hC : IsSTMinCut G t s C) (hlt : stValue G t s < stValue G a s) :
    IsSTMinCut G t a C := by
  have hval := stValue_eq_of_minCut G hC
  have ha : a ∉ C := by
    intro ha
    have hu := stValue_le G ha hC.2.1
    rw [hval] at hu
    exact (not_lt_of_ge hu) hlt
  have hts : s ≠ t := fun he => hC.2.1 (he.symm ▸ hC.1)
  have hat : a ≠ t := fun he => ha (he.symm ▸ hC.1)
  have hvalue : stValue G t a = stValue G t s := by
    have h := stValue_source_switch G hts hat
      (by simpa only [stValue_symm G s t, stValue_symm G s a] using hlt)
    simpa only [stValue_symm G a t, stValue_symm G s t] using h
  refine ⟨hC.1, ha, fun X htX haX => ?_⟩
  rw [hval, ← hvalue]
  exact stValue_le G htX haX

def sourceSwitchEstimate (a t : V) (maximum : ℝ) (candidate : Option (CutCandidate V)) : ℝ :=
  if t = a then maximum else match candidate with
    | none => maximum
    | some C => min maximum C.value

theorem sourceSwitchEstimate_upper (G : WeightedGraph V) {s a t : V} {maximum : ℝ}
    (hmaximum : maximum = stValue G a s) (hmax : stValue G t s ≤ stValue G a s)
    (out : Option (CutCandidate V))
    (hvalid : ∀ C, out = some C → CandidateValid G a t C) :
    stValue G t s ≤ sourceSwitchEstimate a t maximum out := by
  subst maximum
  by_cases hta : t = a
  · simp only [sourceSwitchEstimate, hta, ite_true, le_refl]
  · simp only [sourceSwitchEstimate, hta, ite_false]
    cases out with
    | none => exact hmax
    | some C =>
        exact le_min hmax
          ((sourceSwitch_lower G (Ne.symm hta) hmax).trans ((hvalid C rfl).upper G))

theorem sourceSwitchEstimate_exact_at_max (G : WeightedGraph V) {s a t : V} {maximum : ℝ}
    (hmaximum : maximum = stValue G a s) (heq : stValue G t s = stValue G a s)
    (out : Option (CutCandidate V))
    (hvalid : ∀ C, out = some C → CandidateValid G a t C) :
    sourceSwitchEstimate a t maximum out = stValue G t s := by
  have hlow := sourceSwitchEstimate_upper G hmaximum heq.le out hvalid
  have hup : sourceSwitchEstimate a t maximum out ≤ maximum := by
    unfold sourceSwitchEstimate
    split
    · exact le_rfl
    · cases out with
      | none => exact le_rfl
      | some C => exact min_le_left _ _
  exact le_antisymm (hup.trans_eq (hmaximum.trans heq.symm)) hlow

def switchedGuide (T : GuideTree V N) (C : Finset N) (a : N)
    (ha : a ∈ T.real ∩ Cᶜ) : GuideTree V N := T.retain Cᶜ a ha

def sourceSwitchProgram {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (T : GuideTree V N) (C : Finset N) (a : N) (ha : a ∈ T.real ∩ Cᶜ) :
    Prog (Finset V) ℝ (V → Option ℝ) :=
  let T' := switchedGuide T C a ha
  (pairCandidateProgram family T.source (T.label a)).bind (fun maximum => match maximum with
    | none => Prog.pure (fun _ => none)
    | some maximum =>
      (guideOneProgram family (Nat.clog 2 (T'.real.card + 1)) T').map (fun output t =>
        if t ∈ T'.realVertices then
          some (sourceSwitchEstimate (T.label a) t maximum.value (output t)) else none))

theorem sourceSwitchProgram_upper {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (C : Finset N) (a : N) (ha : a ∈ T.real ∩ Cᶜ)
    (has : T.source ≠ T.label a)
    (hmax : ∀ t ∈ (switchedGuide T C a ha).realVertices,
      stValue G t T.source ≤ stValue G (T.label a) T.source)
    {t : V} {value : ℝ}
    (hvalue : Prog.eval G.cut (sourceSwitchProgram family T C a ha) t = some value) :
    stValue G t T.source ≤ value := by
  let T' := switchedGuide T C a ha
  let output := Prog.eval G.cut (guideOneProgram family (Nat.clog 2 (T'.real.card + 1)) T')
  obtain ⟨maximum, hmaximum, hexact⟩ := pairCandidateProgram_exact family G hG has
  simp only [sourceSwitchProgram, Prog.eval_bind, hmaximum, Prog.eval_map] at hvalue
  split at hvalue
  next ht =>
    have he := Option.some.inj hvalue
    rw [← he]
    apply sourceSwitchEstimate_upper G (hexact.value_eq G) (hmax t ht) (output t)
    intro D hD
    exact guideOneProgram_valid family _ G T' t D hD
  next ht => simp at hvalue

/-- The actual branch recovers every two-respected target whenever a deleted
centroid branch carries a crossing edge. Equal maxima use the exact baseline;
strictly smaller targets use the retained one-respecting recursive call. -/
theorem sourceSwitchProgram_complete {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (C : Finset N) (a : N) (ha : a ∈ T.real ∩ Cᶜ)
    (has : T.source ≠ T.label a)
    (hbranch : IsCentroidBranch T.tree T.centroid C)
    (hmax : ∀ t ∈ (switchedGuide T C a ha).realVertices,
      stValue G t T.source ≤ stValue G (T.label a) T.source)
    {t : V} (ht : t ∈ (switchedGuide T C a ha).realVertices)
    {S : Finset V} (hS : IsSTMinCut G t T.source S)
    (A : Finset N) (hA : ∀ v ∈ T.real, v ∈ A ↔ T.label v ∈ S)
    (hcross : (T.tree.crossSet A).card ≤ 2)
    (e : N) (he : e ∈ T.tree.crossSet A) (heC : e ∈ C ∨ T.tree.parent e ∈ C) :
    Prog.eval G.cut (sourceSwitchProgram family T C a ha) t = some (stValue G t T.source) := by
  let T' := switchedGuide T C a ha
  let output := Prog.eval G.cut (guideOneProgram family (Nat.clog 2 (T'.real.card + 1)) T')
  obtain ⟨maximum, hmaximum, hexact⟩ := pairCandidateProgram_exact family G hG has
  have hvalid : ∀ D, output t = some D → CandidateValid G (T.label a) t D :=
    fun D hD => guideOneProgram_valid family _ G T' t D hD
  simp only [sourceSwitchProgram, Prog.eval_bind, hmaximum, Prog.eval_map,
    ht, ite_true, Option.some.injEq]
  change sourceSwitchEstimate (T.label a) t maximum.value (output t) = stValue G t T.source
  rcases lt_or_eq_of_le (hmax t ht) with hlt | heq
  · have hnew := sourceSwitch_minCut G hS hlt
    have hrespect : T'.RespectsCut S 1 := by
      exact T.retain_branch_respects C hbranch a ha hA hcross he heC
    obtain ⟨D, hD, hDexact⟩ := guideOneProgram_clog_complete family T' G hG ht
      ⟨S, hnew, hrespect⟩
    have hta : t ≠ T.label a := fun h => hnew.2.1 (h ▸ hnew.1)
    have hval : D.value = stValue G t T.source :=
      (hDexact.value_eq G).trans
        ((stValue_eq_of_minCut G hnew).symm.trans (stValue_eq_of_minCut G hS))
    rw [show output t = some D from hD]
    simp only [sourceSwitchEstimate, hta, ite_false, hval, hexact.value_eq G,
      min_eq_right hlt.le]
  · exact sourceSwitchEstimate_exact_at_max G (hexact.value_eq G) heq (output t) hvalid

/-- The extra exact source-pair call and its value query are charged explicitly. -/
theorem sourceSwitchProgram_cost {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (T : GuideTree V N) (C : Finset N) (a : N) (ha : a ∈ T.real ∩ Cᶜ)
    (read : Finset V → ℝ) :
    Prog.cost read (sourceSwitchProgram family T C a ha) ≤ Q (Fintype.card V) + 1 +
      Prog.cost read (guideOneProgram family
        (Nat.clog 2 ((switchedGuide T C a ha).real.card + 1)) (switchedGuide T C a ha)) := by
  simp only [sourceSwitchProgram, Prog.cost_bind]
  apply Nat.add_le_add (pairCandidateProgram_cost family _ _ read)
  cases Prog.eval read (pairCandidateProgram family T.source (T.label a)) <;> simp

end
end CutQueryComplexity.GHReduction
