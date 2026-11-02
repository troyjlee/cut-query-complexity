import CutQueryComplexity.GlobalSTReduction.Replies
import CutQueryComplexity.GHReduction.Randomized.Primitives

/-! # Single calls on public contractions, with arbitrary minimum replies

The call programs are the existing twins `setCutCall`, `shoreCutCall`,
`groupSeparatorCall` and `isolatingLocalCall` (`GHReduction.Randomized.Primitives`):
each contracts along a public map, makes one call on the compact relabeling, and
pulls the reply back. Every virtual cut query is one original query.

The existing correctness lemmas assume the canonical reply. Their weaker
companions here accept any minimum reply:

* `min_setCut_pull`: a minimum cut between the two contracted terminal groups
  pulls back to a minimum shore with the prescribed trace (`IsMinTraceCut`);
* `min_shorePull`: a minimum source–proxy cut of a cell that contains some
  minimum isolating shore pulls back to a minimum isolating shore.

The cost and call-count bounds hold for all answers and replies, so they cover
malformed histories.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GlobalSTReduction
noncomputable section
open scoped Classical BigOperators
open WeightedGraph GHReduction GHReduction.Randomized

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Pullback lemmas -/

/-- An arbitrary minimum cut between the contracted groups is a minimum shore of
the original graph with trace `A` on `A ∪ B`. -/
theorem min_setCut_pull (G : WeightedGraph V) {A B : Finset V} (hAB : Disjoint A B)
    {S : Finset (SetCutVertex A B)}
    (hS : IsSTMinCut (G.contract (setCutMap A B)) (Sum.inl 0) (Sum.inl 1) S) :
    IsMinTraceCut G (A ∪ B) A (pull (setCutMap A B) S) := by
  refine ⟨setCutPull_trace hAB hS.1 hS.2.1, fun T hT => ?_⟩
  obtain ⟨hAT, hTB⟩ := trace_feasible hAB hT
  have h := hS.2.2 (setCutShore A B T) (setCutShore_source _ _ _) (setCutShore_sink _ _ _)
  simpa only [cut_contract, pull_setCutShore hAT hTB] using h

/-- An arbitrary minimum source–proxy cut of the cell `P` is a minimum isolating
shore of `v`, provided `P` meets `R` only in `v` and contains some minimum
isolating shore `C` of `v`. -/
theorem min_shorePull (G : WeightedGraph V) {R P C : Finset V} {v : V} (hv : v ∈ P)
    (hPR : P ∩ R = {v}) (hC : IsMinTraceCut G R {v} C) (hCP : C ⊆ P)
    {X : Finset (ShoreVertex P)}
    (hX : IsSTMinCut (G.contract (shoreMap P)) (some ⟨v, hv⟩) none X) :
    IsMinTraceCut G R {v} (pull (shoreMap P) X) := by
  have hXP := pull_shore_subset hX.2.1
  have hvX : v ∈ pull (shoreMap P) X := by simpa [shoreMap, hv] using hX.1
  have hvC : v ∈ C := by
    have : v ∈ C ∩ R := by rw [hC.1]; simp
    exact (Finset.mem_inter.mp this).1
  have hvR : v ∈ R := by
    have : v ∈ P ∩ R := by rw [hPR]; simp
    exact (Finset.mem_inter.mp this).2
  have htrace : pull (shoreMap P) X ∩ R = {v} := by
    apply Finset.Subset.antisymm
    · exact (Finset.inter_subset_inter hXP (le_refl R)).trans (le_of_eq hPR)
    · exact Finset.singleton_subset_iff.mpr (Finset.mem_inter.mpr ⟨hvX, hvR⟩)
  have hle : G.cut (pull (shoreMap P) X) ≤ G.cut C := by
    have h := hX.2.2 (shorePush P C) (by simpa using hvC) (none_not_mem_shorePush _ _)
    simpa only [cut_contract, pull_shorePush hCP] using h
  exact ⟨htrace, fun Y hY => hle.trans (hC.2 Y hY)⟩

/-! ### Correctness under minimum replies -/

theorem holds_setCutCall (G : WeightedGraph V) {A B : Finset V} (hAB : Disjoint A B) :
    Holds G.cut (optReply G) (IsMinTraceCut G (A ∪ B) A) (CallProg.setCutCall A B) := by
  rw [CallProg.setCutCall, holds_map]
  apply holds_contract_opt
  exact (holds_canonicalCall _ _).mono (fun S hS => min_setCut_pull G hAB hS)

theorem holds_shoreCutCall (G : WeightedGraph V) {R P C : Finset V} {v : V} (hv : v ∈ P)
    (hPR : P ∩ R = {v}) (hC : IsMinTraceCut G R {v} C) (hCP : C ⊆ P) :
    Holds G.cut (optReply G) (IsMinTraceCut G R {v}) (CallProg.shoreCutCall P ⟨v, hv⟩) := by
  rw [CallProg.shoreCutCall, holds_map]
  apply holds_contract_opt
  exact (holds_canonicalCall _ _).mono (fun X hX => min_shorePull G hv hPR hC hCP hX)

theorem holds_groupSeparatorCall (G : WeightedGraph V) {A B : Finset V} (hAB : Disjoint A B) :
    Holds G.cut (optReply G) (IsMinTraceCut G (A ∪ B) A) (CallProg.groupSeparatorCall A B) := by
  unfold CallProg.groupSeparatorCall
  split_ifs with hA hB
  · subst hA
    exact ⟨by simp, fun T _ => by simpa using G.cut_nonneg T⟩
  · subst hB
    exact ⟨by simp, fun T _ => by simpa using G.cut_nonneg T⟩
  · exact holds_setCutCall G hAB

/-- The local call of a guarded cell returns a minimum isolating shore. -/
theorem holds_isolatingLocalCall (G : WeightedGraph V) {R P C : Finset V} {v : V}
    (hv : v ∈ P) (hp : P ≠ Finset.univ) (hPR : P ∩ R = {v}) (hC : IsMinTraceCut G R {v} C)
    (hCP : C ⊆ P) :
    Holds G.cut (optReply G) (IsMinTraceCut G R {v}) (CallProg.isolatingLocalCall P v) := by
  rw [CallProg.isolatingLocalCall, dite_eq_left hv, ite_eq_left hp]
  exact holds_shoreCutCall G hv hPR hC hCP

/-! ### Charges for all answers and replies -/

section Charges

variable {wq : ℕ} {wc : ℕ → ℕ}

theorem within_setCutCall (A B : Finset V) :
    Within wq wc (CallProg.setCutCall A B) (wc (Fintype.card (SetCutVertex A B))) :=
  within_map _ (within_contract _ (within_canonicalCall _))

theorem within_shoreCutCall (P : Finset V) (v : {v : V // v ∈ P}) :
    Within wq wc (CallProg.shoreCutCall P v) (wc (Fintype.card (ShoreVertex P))) :=
  within_map _ (within_contract _ (within_canonicalCall _))

/-- One group separator costs at most `Q |V|`, by size regularity at `|V|`. -/
theorem cost_groupSeparatorCall {Q : ℕ → ℕ} {A B : Finset V} (hAB : Disjoint A B)
    (hQ : SizeRegular (Fintype.card V) Q) :
    CostWithin Q (CallProg.groupSeparatorCall A B) (Q (Fintype.card V)) := by
  unfold CallProg.groupSeparatorCall
  split_ifs with hA hB
  · trivial
  · trivial
  · have hAn : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr hA
    have hBn : B.Nonempty := Finset.nonempty_iff_ne_empty.mpr hB
    have hn : 0 < Fintype.card V := hAn.card_pos.trans_le (Finset.card_le_univ A)
    have hs : 1 ≤ Fintype.card (SetCutVertex A B) := by
      have : Nonempty (SetCutVertex A B) := ⟨Sum.inl 0⟩
      exact Fintype.card_pos
    exact (within_setCutCall A B).mono
      (regular_cost_mono hn hs (setCutVertex_card_le hAB hAn hBn) hQ)

theorem calls_groupSeparatorCall (A B : Finset V) :
    CallsWithin (CallProg.groupSeparatorCall A B) 1 := by
  unfold CallProg.groupSeparatorCall
  split_ifs
  · trivial
  · trivial
  · exact within_setCutCall A B

theorem cost_isolatingLocalCall (Q : ℕ → ℕ) (P : Finset V) (v : V) :
    CostWithin Q (CallProg.isolatingLocalCall P v) (localCharge Q P v) := by
  unfold CallProg.isolatingLocalCall localCharge
  by_cases hv : v ∈ P
  · by_cases hp : P ≠ Finset.univ
    · rw [dite_eq_left hv, ite_eq_left hp, ite_eq_left ⟨hv, hp⟩]
      simpa only [shoreVertex_card] using within_shoreCutCall P ⟨v, hv⟩
    · rw [dite_eq_left hv, ite_eq_right hp]
      trivial
  · rw [dite_eq_right hv]
    trivial

theorem calls_isolatingLocalCall (P : Finset V) (v : V) :
    CallsWithin (CallProg.isolatingLocalCall P v) 1 := by
  unfold CallProg.isolatingLocalCall
  split_ifs
  · exact within_shoreCutCall _ _
  · trivial
  · trivial

end Charges

end
end CutQueryComplexity.GlobalSTReduction
