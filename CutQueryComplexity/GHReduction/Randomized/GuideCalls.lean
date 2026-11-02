import CutQueryComplexity.GHReduction.Randomized.Primitives
import CutQueryComplexity.GHReduction.GuideTwoProgram

/-! # Phase 3c, deterministic part: the guide programs as call programs

Twins of the deterministic guide pieces: the centroid shores and centroid pair
(`GuideSplit`, `GuideOne`), the one-respecting recursion `guideOneProgram`, the
source switch (`GuideSourceSwitch`) and the guide node (`GuideTwoProgram`), with
their bridges and ideal charged costs.

The cost of the recursion uses facts about the centroid shores that hold only
on a promised graph (`GuideOneBudget`). They are transferred to the twin's ideal
shores through the reference family (`centroidShoreCall_facts`).
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction.Randomized
noncomputable section
open scoped Classical ENNReal BigOperators
open WeightedGraph Probability

namespace CallProg

variable {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]

/-- Twin of `centroidShoreProgram`. -/
def centroidShoreCall (T : GuideTree V N) : CallProg V (T.parts → Finset V) :=
  (groupIsolatingCall T.isolationGroups).map
    (fun output P => output ⟨P.val, T.part_mem_isolationParts P.property⟩)

theorem centroidShore_idealEval {M : ℕ} {QE : ℕ → ℕ} (E : CanonicalSTFamily M QE)
    (G : WeightedGraph V) (hG : InputPromise M G) (T : GuideTree V N) :
    Prog.eval G.cut (centroidShoreProgram E T) = idealEval G (centroidShoreCall T) := by
  simp only [centroidShoreProgram, centroidShoreCall, Prog.eval_map, idealEval_map,
    groupIsolating_idealEval E G hG]

theorem centroidShoreCall_idealCost_scaled {n : ℕ} {Q : ℕ → ℕ} (T : GuideTree V N)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) (G : WeightedGraph V) :
    n * idealCost G Q (centroidShoreCall T) ≤ ((Nat.clog 2 n + 2) * Fintype.card V) * Q n := by
  rw [centroidShoreCall, idealCost_map]
  have h := groupIsolatingCall_idealCost_scaled T.isolationGroups
    T.isolationGroups_disjoint T.isolationGroups_nonempty hvn hQ G
  apply h.trans
  apply Nat.mul_le_mul_right (Q n)
  apply Nat.mul_le_mul_right (Fintype.card V)
  exact Nat.add_le_add_right
    (Nat.clog_mono_right 2 (T.isolationParts_card_le.trans (T.real_card_le.trans hvn))) 2

/-- Twin of `centroidPairProgram`. -/
def centroidPairCall (T : GuideTree V N) : CallProg V (Option (CutCandidate V)) :=
  if T.centroid ∈ T.real then pairCandidateCall T.source (T.label T.centroid) else pure none

theorem centroidPair_idealEval {M : ℕ} {QE : ℕ → ℕ} (E : CanonicalSTFamily M QE)
    (G : WeightedGraph V) (hG : InputPromise M G) (T : GuideTree V N) :
    Prog.eval G.cut (centroidPairProgram E T) = idealEval G (centroidPairCall T) := by
  unfold centroidPairProgram centroidPairCall
  split_ifs <;> simp [pairCandidate_idealEval E G hG]

theorem centroidPairCall_idealCost (T : GuideTree V N) (G : WeightedGraph V) (Q : ℕ → ℕ) :
    idealCost G Q (centroidPairCall T) ≤ Q (Fintype.card V) + 1 := by
  unfold centroidPairCall
  split
  · exact pairCandidateCall_idealCost G Q _ _
  · simp

theorem centroidPairCall_idealCost_scaled {n : ℕ} {Q : ℕ → ℕ} (T : GuideTree V N)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) (G : WeightedGraph V) :
    n * idealCost G Q (centroidPairCall T) ≤ Fintype.card V * (Q n + n) := by
  have : Nonempty V := ⟨T.source⟩
  have hs : 1 ≤ Fintype.card V := Fintype.card_pos
  have hreg := hQ _ hs hvn
  have hsmall := Nat.mul_le_mul_left n (centroidPairCall_idealCost T G Q)
  have hn := Nat.mul_le_mul_right n hs
  nlinarith

theorem guideBaseCall_idealCost_scaled {n : ℕ} {Q : ℕ → ℕ} (T : GuideTree V N)
    (hsmall : T.real.card ≤ 10) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (G : WeightedGraph V) :
    n * idealCost G Q (guideBaseCall T) ≤ (10 * Fintype.card V) * (Q n + n) := by
  have h := sourceBaseCall_idealCost_scaled G T.source T.realVertices hvn hQ
  rw [T.realVertices_card] at h
  have h1 := Nat.mul_le_mul_right (Fintype.card V * Q n) hsmall
  have h2 := Nat.mul_le_mul_right n T.real_card_le
  change n * idealCost G Q (sourceBaseCall T.source T.realVertices) ≤ _
  nlinarith

/-- Twin of `guideOneProgram`: the one-respecting guide recursion. -/
def guideOneCall (fuel : ℕ) {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]
    (T : GuideTree V N) : CallProg V (V → Option (CutCandidate V)) :=
  match fuel with
  | 0 => if T.real.card ≤ 10 then guideBaseCall T else pure (fun _ => none)
  | fuel + 1 => if T.real.card ≤ 10 then guideBaseCall T else
      (centroidPairCall T).bind (fun initial =>
        (centroidShoreCall T).bind (fun shores =>
          (finiteTable (fun P : T.parts =>
            let S := shores P
            if htrace : S ∩ T.realVertices = T.graphGroup P.val then
              let child := childGuide T P S htrace
              (contract (shoreMap S) (guideOneCall fuel child)).map
                (fun output t => pullCandidate (shoreMap S) T.source t (output (shoreMap S t)))
            else pure (fun _ => none))).map (fun children t =>
              bestCandidates (filterCandidate T.source t initial ::
                (Finset.univ.toList.map (fun P : T.parts => children P t))))))
termination_by fuel

theorem guideOne_idealEval {M : ℕ} {QE : ℕ → ℕ} (E : CanonicalSTFamily M QE) (fuel : ℕ) :
    ∀ {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]
      (G : WeightedGraph V), InputPromise M G → ∀ T : GuideTree V N,
      Prog.eval G.cut (guideOneProgram E fuel T) = idealEval G (guideOneCall fuel T) := by
  induction fuel with
  | zero =>
      intro V N _ _ _ _ G hG T
      by_cases hsmall : T.real.card ≤ 10
      · simp [guideOneProgram, guideOneCall, hsmall, guideBase_idealEval E G hG]
      · simp [guideOneProgram, guideOneCall, hsmall]
  | succ fuel ih =>
      intro V N _ _ _ _ G hG T
      by_cases hsmall : T.real.card ≤ 10
      · simp [guideOneProgram, guideOneCall, hsmall, guideBase_idealEval E G hG]
      · have hread : ∀ S : Finset V, G.cut ∘ pull (shoreMap S) = (G.contract (shoreMap S)).cut := by
          intro S
          funext X
          exact (cut_contract G _ X).symm
        have hchild : ∀ (S : T.parts → Finset V) (P : T.parts),
            Prog.eval G.cut (if htrace : S P ∩ T.realVertices = T.graphGroup P.val then
              (queryMap (pull (shoreMap (S P))) (guideOneProgram E fuel (childGuide T P (S P) htrace))).map
                (fun output t => pullCandidate (shoreMap (S P)) T.source t (output (shoreMap (S P) t)))
              else Prog.pure (fun _ => none)) =
            idealEval G (if htrace : S P ∩ T.realVertices = T.graphGroup P.val then
              (contract (shoreMap (S P)) (guideOneCall fuel (childGuide T P (S P) htrace))).map
                (fun output t => pullCandidate (shoreMap (S P)) T.source t (output (shoreMap (S P) t)))
              else pure (fun _ => none)) := by
          intro S P
          split
          · simp only [Prog.eval_map, queryMap_eval, hread, idealEval_map, idealEval_contract,
              ih _ (inputPromise_contract G hG _)]
          · rfl
        simp only [guideOneProgram, guideOneCall, hsmall, ite_false, Prog.eval_bind, idealEval_bind]
        rw [centroidPair_idealEval E G hG, centroidShore_idealEval E G hG]
        simp only [Prog.eval_map, idealEval_map, finiteTable_eval, idealEval_finiteTable]
        simp only [hchild]

/-- The old centroid facts, transferred to the twin's ideal shores through the
reference family. -/
theorem centroidShoreCall_facts {M : ℕ} (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (hlarge : 2 < T.real.card) :
    (∀ P : T.parts, IsCanonicalTraceCut G T.realVertices (T.graphGroup P.val)
      (idealEval G (centroidShoreCall T) P)) ∧
    (∑ P : T.parts, ((idealEval G (centroidShoreCall T) P).card + 1)) ≤
      Fintype.card V + T.real.card ∧
    (∑ P : T.parts, guideWork ((idealEval G (centroidShoreCall T) P).card + 1)
      ((T.graphGroup P.val).card + 1)) ≤ guideWork (Fintype.card V) T.real.card := by
  rw [← centroidShore_idealEval (refFamily M) G hG T]
  exact ⟨centroidShoreProgram_correct (refFamily M) G hG T hlarge,
    centroid_children_total_size (refFamily M) G hG T hlarge,
    centroid_children_guideWork (refFamily M) G hG T hlarge⟩

theorem guideOneCall_idealCost_scaled {M n : ℕ} {Q : ℕ → ℕ} (hQ : SizeRegular n Q) (fuel : ℕ) :
    ∀ {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]
      (G : WeightedGraph V), InputPromise M G → ∀ T : GuideTree V N,
      Fintype.card V ≤ n →
      n * idealCost G Q (guideOneCall fuel T) ≤
        (10 * Fintype.card V + fuel * (Nat.clog 2 n + 23) *
          guideWork (Fintype.card V) T.real.card) * (Q n + n) := by
  induction fuel with
  | zero =>
    intro V N _ _ _ _ G hG T hvn
    by_cases hsmall : T.real.card ≤ 10
    · simpa only [guideOneCall, hsmall, ite_true, zero_mul, Nat.zero_mul, add_zero,
        Nat.add_zero] using guideBaseCall_idealCost_scaled T hsmall hvn hQ G
    · simp [guideOneCall, hsmall]
  | succ fuel ih =>
    intro V N _ _ _ _ G hG T hvn
    by_cases hsmall : T.real.card ≤ 10
    · simp only [guideOneCall, hsmall, ite_true]
      exact (guideBaseCall_idealCost_scaled T hsmall hvn hQ G).trans
        (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
    · have hlarge : 2 < T.real.card := by omega
      obtain ⟨hcorrect, htotal, hguide⟩ := centroidShoreCall_facts G hG T hlarge
      let S : T.parts → Finset V := idealEval G (centroidShoreCall T)
      have htrace : ∀ P : T.parts, S P ∩ T.realVertices = T.graphGroup P.val :=
        fun P => (hcorrect P).1.1
      let child (P : T.parts) := childGuide T P (S P) (htrace P)
      let size (P : T.parts) := Fintype.card (ShoreVertex (S P))
      let work (P : T.parts) := guideWork (size P) (child P).real.card
      let cost (P : T.parts) := idealCost (G.contract (shoreMap (S P))) Q
        (guideOneCall fuel (child P))
      let overhead := idealCost G Q (centroidPairCall T) + idealCost G Q (centroidShoreCall T)
      have hchild : ∀ P, n * cost P ≤
          (10 * size P + fuel * (Nat.clog 2 n + 23) * work P) * (Q n + n) := by
        intro P
        exact ih _ (inputPromise_contract G hG (shoreMap (S P))) (child P)
          ((childGuide_graph_size_le T P (S P) (htrace P)).trans hvn)
      have hsize : (∑ P, size P) ≤ 2 * Fintype.card V := by
        have hr := T.real_card_le
        simp only [size, shoreVertex_card]
        exact htotal.trans (by omega)
      have hwork : (∑ P, work P) ≤ guideWork (Fintype.card V) T.real.card := by
        have hcards : ∀ P : T.parts, (T.graphGroup P.val).card = P.val.card :=
          fun P => T.graphGroup_card (T.part_subset P.property)
        simpa only [work, size, child, shoreVertex_card, childGuide_real_card, hcards] using hguide
      have hsw : Fintype.card V ≤ guideWork (Fintype.card V) T.real.card :=
        size_le_guideWork T.real_card_le (by omega)
      have hoverhead : n * overhead ≤ ((Nat.clog 2 n + 3) * Fintype.card V) * (Q n + n) := by
        have hp := centroidPairCall_idealCost_scaled T hvn hQ G
        have hi := centroidShoreCall_idealCost_scaled T hvn hQ G
        have hi' : n * idealCost G Q (centroidShoreCall T) ≤
            ((Nat.clog 2 n + 2) * Fintype.card V) * (Q n + n) :=
          hi.trans (Nat.mul_le_mul_left _ (Nat.le_add_right _ _))
        change n * (idealCost G Q (centroidPairCall T) + idealCost G Q (centroidShoreCall T)) ≤ _
        nlinarith
      have hstep : idealCost G Q (guideOneCall (fuel + 1) T) = overhead + ∑ P, cost P := by
        simp only [guideOneCall, hsmall, ite_false, idealCost_bind, idealCost_map,
          idealCost_finiteTable]
        rw [show idealEval G (centroidShoreCall T) = S from rfl]
        simp only [htrace, dite_true, idealCost_map, idealCost_contract]
        exact (Nat.add_assoc _ _ _).symm
      rw [hstep]
      exact guide_cost_recurrence cost size work hsize hwork hsw hoverhead hchild

theorem guideOneCall_global_cost {M n : ℕ} {Q : ℕ → ℕ} (G : WeightedGraph V)
    (hG : InputPromise M G) (T : GuideTree V N) (hvn : Fintype.card V ≤ n)
    (hQ : SizeRegular n Q) :
    idealCost G Q (guideOneCall (Nat.clog 2 (n + 1)) T) ≤ guideOneGlobalBudget Q n := by
  have : Nonempty V := ⟨T.source⟩
  have hn : 0 < n := Fintype.card_pos.trans_le hvn
  have h := guideOneCall_idealCost_scaled hQ (Nat.clog 2 (n + 1)) G hG T hvn
  have hw : guideWork (Fintype.card V) T.real.card ≤ 2 * n :=
    (guideWork_le_twice_size T.real_card_le).trans (Nat.mul_le_mul_left 2 hvn)
  have hmul : n * idealCost G Q (guideOneCall (Nat.clog 2 (n + 1)) T) ≤
      n * guideOneGlobalBudget Q n := by
    calc
      _ ≤ (10 * Fintype.card V + Nat.clog 2 (n + 1) * (Nat.clog 2 n + 23) *
          guideWork (Fintype.card V) T.real.card) * (Q n + n) := h
      _ ≤ (10 * n + Nat.clog 2 (n + 1) * (Nat.clog 2 n + 23) * (2 * n)) * (Q n + n) :=
        Nat.mul_le_mul_right _ (Nat.add_le_add (Nat.mul_le_mul_left 10 hvn)
          (Nat.mul_le_mul_left _ hw))
      _ = _ := by unfold guideOneGlobalBudget; ring
  exact Nat.le_of_mul_le_mul_left hmul hn

theorem guideOneCall_cost_linear {M n : ℕ} {Q : ℕ → ℕ} (G : WeightedGraph V)
    (hG : InputPromise M G) (T : GuideTree V N) (hvn : Fintype.card V ≤ n)
    (hQ : SizeRegular n Q) (fuel : ℕ) :
    n * idealCost G Q (guideOneCall fuel T) ≤
      Fintype.card V * ((10 + 2 * fuel * (Nat.clog 2 n + 23)) * (Q n + n)) := by
  have h := guideOneCall_idealCost_scaled hQ fuel G hG T hvn
  have hw := guideWork_le_twice_size T.real_card_le
  calc
    _ ≤ (10 * Fintype.card V + fuel * (Nat.clog 2 n + 23) *
        guideWork (Fintype.card V) T.real.card) * (Q n + n) := h
    _ ≤ (10 * Fintype.card V + fuel * (Nat.clog 2 n + 23) *
        (2 * Fintype.card V)) * (Q n + n) :=
      Nat.mul_le_mul_right _ (Nat.add_le_add_left (Nat.mul_le_mul_left _ hw) _)
    _ = _ := by ring

theorem guideOneCall_localFuel_cost_scaled {M n : ℕ} {Q : ℕ → ℕ} (G : WeightedGraph V)
    (hG : InputPromise M G) (T : GuideTree V N) (hvn : Fintype.card V ≤ n)
    (hQ : SizeRegular n Q) :
    n * idealCost G Q (guideOneCall (Nat.clog 2 (T.real.card + 1)) T) ≤
      Fintype.card V * guideOneGlobalBudget Q n := by
  have hfuel := Nat.clog_mono_right 2 (Nat.add_le_add_right (T.real_card_le.trans hvn) 1)
  have h := guideOneCall_cost_linear G hG T hvn hQ (Nat.clog 2 (T.real.card + 1))
  apply h.trans
  apply Nat.mul_le_mul_left
  apply Nat.mul_le_mul_right
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hfuel)) 10

/-- Twin of `sourceSwitchProgram`. -/
def sourceSwitchCall (T : GuideTree V N) (C : Finset N) (a : N) (ha : a ∈ T.real ∩ Cᶜ) :
    CallProg V (V → Option ℝ) :=
  let T' := switchedGuide T C a ha
  (pairCandidateCall T.source (T.label a)).bind (fun maximum => match maximum with
    | none => pure (fun _ => none)
    | some maximum =>
      (guideOneCall (Nat.clog 2 (T'.real.card + 1)) T').map (fun output t =>
        if t ∈ T'.realVertices then
          some (sourceSwitchEstimate (T.label a) t maximum.value (output t)) else none))

theorem sourceSwitch_idealEval {M : ℕ} {QE : ℕ → ℕ} (E : CanonicalSTFamily M QE)
    (G : WeightedGraph V) (hG : InputPromise M G) (T : GuideTree V N) (C : Finset N) (a : N)
    (ha : a ∈ T.real ∩ Cᶜ) :
    Prog.eval G.cut (sourceSwitchProgram E T C a ha) = idealEval G (sourceSwitchCall T C a ha) := by
  simp only [sourceSwitchProgram, sourceSwitchCall, Prog.eval_bind, idealEval_bind,
    pairCandidate_idealEval E G hG]
  cases idealEval G (pairCandidateCall T.source (T.label a)) with
  | none => rfl
  | some maximum =>
      simp only [Prog.eval_map, idealEval_map, guideOne_idealEval E _ G hG]

theorem sourceSwitchCall_idealCost (G : WeightedGraph V) (Q : ℕ → ℕ) (T : GuideTree V N)
    (C : Finset N) (a : N) (ha : a ∈ T.real ∩ Cᶜ) :
    idealCost G Q (sourceSwitchCall T C a ha) ≤ Q (Fintype.card V) + 1 +
      idealCost G Q (guideOneCall
        (Nat.clog 2 ((switchedGuide T C a ha).real.card + 1)) (switchedGuide T C a ha)) := by
  simp only [sourceSwitchCall, idealCost_bind]
  apply Nat.add_le_add (pairCandidateCall_idealCost G Q _ _)
  cases idealEval G (pairCandidateCall T.source (T.label a)) <;> simp

theorem sourceSwitchCall_idealCost_scaled {M n : ℕ} {Q : ℕ → ℕ} (G : WeightedGraph V)
    (hG : InputPromise M G) (T : GuideTree V N) (C : Finset N) (a : N) (ha : a ∈ T.real ∩ Cᶜ)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) :
    n * idealCost G Q (sourceSwitchCall T C a ha) ≤ Fintype.card V * sourceSwitchBudget Q n := by
  have : Nonempty V := ⟨T.source⟩
  have hm : 1 ≤ Fintype.card V := Fintype.card_pos
  have hreg := hQ _ hm hvn
  have hunit := Nat.mul_le_mul_right n hm
  have hcost := Nat.mul_le_mul_left n (sourceSwitchCall_idealCost G Q T C a ha)
  have hrec := guideOneCall_localFuel_cost_scaled G hG (switchedGuide T C a ha) hvn hQ
  unfold sourceSwitchBudget
  nlinarith

/-- Twin of `guideNodeProgram`. -/
def guideNodeCall (T : GuideTree V N) : CallProg V (GuideNodeOutput T) :=
  (centroidPairCall T).bind (fun initial =>
    (centroidShoreCall T).map (fun shores => (initial, shores)))

theorem guideNode_idealEval {M : ℕ} {QE : ℕ → ℕ} (E : CanonicalSTFamily M QE)
    (G : WeightedGraph V) (hG : InputPromise M G) (T : GuideTree V N) :
    Prog.eval G.cut (guideNodeProgram E T) = idealEval G (guideNodeCall T) := by
  simp only [guideNodeProgram, guideNodeCall, Prog.eval_bind, Prog.eval_map, idealEval_bind,
    idealEval_map, centroidPair_idealEval E G hG, centroidShore_idealEval E G hG]

theorem guideNodeCall_idealCost_scaled {n : ℕ} {Q : ℕ → ℕ} (T : GuideTree V N)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) (G : WeightedGraph V) :
    n * idealCost G Q (guideNodeCall T) ≤ Fintype.card V * guideNodeBudget Q n := by
  have hpair := centroidPairCall_idealCost_scaled T hvn hQ G
  have hshores := centroidShoreCall_idealCost_scaled T hvn hQ G
  simp only [guideNodeCall, idealCost_bind, idealCost_map, Nat.mul_add]
  unfold guideNodeBudget
  calc
    _ ≤ Fintype.card V * (Q n + n) + (Nat.clog 2 n + 2) * Fintype.card V * Q n :=
      add_le_add hpair hshores
    _ ≤ Fintype.card V * (Q n + n) + (Nat.clog 2 n + 2) * Fintype.card V * (Q n + n) :=
      add_le_add le_rfl (Nat.mul_le_mul_left _ (by omega))
    _ = _ := by ring

end CallProg
end
end CutQueryComplexity.GHReduction.Randomized
