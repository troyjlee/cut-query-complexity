import CutQueryComplexity.GHReduction.Randomized.Reference
import CutQueryComplexity.GHReduction.GroupContraction
import CutQueryComplexity.GHReduction.GuideBase

/-! # Phase 3a: the local primitives as call programs

Each definition `fooCall` is the call-language twin of the old `foo`: it makes the
same cut queries in the same order, and each inlined s-t program
`contractDetProgram f (canonicalSTProgram family s t)` becomes one call node
`contract f (canonicalCall s t _)` on the same contracted instance. Family-free
pieces (`evaluateCandidate`) are embedded unchanged with `ofProg`.

For each twin:

* the bridge `foo_idealEval`: for every exact family `E` and every promised graph,
  the old program run with `E` evaluates on `G.cut` to the twin's ideal output.
  The old correctness theorems therefore describe the ideal output;
* the ideal charged cost (`idealCost`: cut queries plus `Q k` per call), bounded
  by the old cost argument for every charge `Q`. The bounds hold on every graph,
  as the old ones hold for every oracle.

The old modules are `Specification`, `Candidates`, `ShoreContraction`,
`TerminalContraction`, `GroupSeparator`, `GuideBase`, `Isolating` and
`GroupContraction`.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction.Randomized
noncomputable section
open scoped Classical BigOperators
open WeightedGraph
open Certificate (bitClass)

namespace CallProg

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### One call on a contracted instance -/

/-- Twin of `setCutProgram`: the canonical cut between two terminal groups. -/
def setCutCall (X Y : Finset V) : CallProg V (Finset V) :=
  (contract (setCutMap X Y)
    (canonicalCall (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2)) (by simp))).map (pull (setCutMap X Y))

theorem setCut_idealEval {M : ℕ} {QE : ℕ → ℕ} (E : CanonicalSTFamily M QE)
    (G : WeightedGraph V) (hG : InputPromise M G) (X Y : Finset V) :
    (setCutProgram E X Y).eval G.cut = idealEval G (setCutCall X Y) := by
  rw [setCutProgram, DTree.eval_map, contractDetProgram_eval,
    canonicalSTProgram_eval_eq E _ (inputPromise_contract G hG _) (by simp)]
  simp [setCutCall]

@[simp] theorem setCutCall_idealCost (G : WeightedGraph V) (Q : ℕ → ℕ) (X Y : Finset V) :
    idealCost G Q (setCutCall X Y) = Q (Fintype.card (SetCutVertex X Y)) := by
  simp [setCutCall]

/-- Twin of `shoreCutProgram`: the source–proxy call of an isolating cell. -/
def shoreCutCall (P : Finset V) (v : {v : V // v ∈ P}) : CallProg V (Finset V) :=
  (contract (shoreMap P) (canonicalCall (some v) none (by simp))).map (pull (shoreMap P))

theorem shoreCut_idealEval {M : ℕ} {QE : ℕ → ℕ} (E : CanonicalSTFamily M QE)
    (G : WeightedGraph V) (hG : InputPromise M G) (P : Finset V) (v : {v : V // v ∈ P}) :
    (shoreCutProgram E P v).eval G.cut = idealEval G (shoreCutCall P v) := by
  rw [shoreCutProgram, DTree.eval_map, contractDetProgram_eval,
    canonicalSTProgram_eval_eq E _ (inputPromise_contract G hG _) (by simp)]
  simp [shoreCutCall]

@[simp] theorem shoreCutCall_idealCost (G : WeightedGraph V) (Q : ℕ → ℕ) (P : Finset V)
    (v : {v : V // v ∈ P}) :
    idealCost G Q (shoreCutCall P v) = Q (Fintype.card (ShoreVertex P)) := by
  simp [shoreCutCall]

/-! ### Candidates and group separators -/

/-- Twin of `pairCandidateProgram`. -/
def pairCandidateCall (s t : V) : CallProg V (Option (CutCandidate V)) :=
  if h : s = t then pure none else
    (canonicalCall t s (Ne.symm h)).bind (fun S => ofProg (evaluateCandidate s t S))

theorem pairCandidate_idealEval {M : ℕ} {QE : ℕ → ℕ} (E : CanonicalSTFamily M QE)
    (G : WeightedGraph V) (hG : InputPromise M G) (s t : V) :
    Prog.eval G.cut (pairCandidateProgram E s t) = idealEval G (pairCandidateCall s t) := by
  by_cases h : s = t
  · simp [pairCandidateProgram, pairCandidateCall, h]
  · simp only [pairCandidateProgram, pairCandidateCall, h, ite_false, dite_false,
      Prog.eval_bind, liftDTree_eval, idealEval_bind, idealEval_ofProg]
    rw [canonicalSTProgram_eval_eq E G hG (Ne.symm h)]

theorem pairCandidateCall_idealCost (G : WeightedGraph V) (Q : ℕ → ℕ) (s t : V) :
    idealCost G Q (pairCandidateCall s t) ≤ Q (Fintype.card V) + 1 := by
  by_cases h : s = t
  · simp [pairCandidateCall, h]
  · simp only [pairCandidateCall, h, dite_false, idealCost_bind, idealCost_canonicalCall,
      idealCost_ofProg]
    exact Nat.add_le_add_left (evaluateCandidate_cost _ _ _ _) _

/-- Twin of `groupSeparator`. -/
def groupSeparatorCall (X Y : Finset V) : CallProg V (Finset V) :=
  if X = ∅ then pure ∅ else if Y = ∅ then pure Finset.univ else setCutCall X Y

theorem groupSeparator_idealEval {M : ℕ} {QE : ℕ → ℕ} (E : CanonicalSTFamily M QE)
    (G : WeightedGraph V) (hG : InputPromise M G) (X Y : Finset V) :
    Prog.eval G.cut (groupSeparator E X Y) = idealEval G (groupSeparatorCall X Y) := by
  unfold groupSeparator groupSeparatorCall
  split_ifs <;> simp [setCut_idealEval E G hG]

theorem groupSeparatorCall_idealCost {Q : ℕ → ℕ} {X Y : Finset V} (hXY : Disjoint X Y)
    (hQ : SizeRegular (Fintype.card V) Q) (G : WeightedGraph V) :
    idealCost G Q (groupSeparatorCall X Y) ≤ Q (Fintype.card V) := by
  by_cases hX : X = ∅
  · simp [groupSeparatorCall, hX]
  · by_cases hY : Y = ∅
    · simp [groupSeparatorCall, hX, hY]
    · have hXn : X.Nonempty := Finset.nonempty_iff_ne_empty.mpr hX
      have hYn : Y.Nonempty := Finset.nonempty_iff_ne_empty.mpr hY
      have hn : 0 < Fintype.card V := hXn.card_pos.trans_le (Finset.card_le_univ X)
      have hs : 1 ≤ Fintype.card (SetCutVertex X Y) := by
        have : Nonempty (SetCutVertex X Y) := ⟨Sum.inl 0⟩
        exact Fintype.card_pos
      simp only [groupSeparatorCall, hX, hY, ite_false, setCutCall_idealCost]
      exact regular_cost_mono hn hs (setCutVertex_card_le hXY hXn hYn) hQ

theorem groupSeparatorCall_idealCost_scaled {n : ℕ} {Q : ℕ → ℕ} {X Y : Finset V}
    (hXY : Disjoint X Y) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (G : WeightedGraph V) :
    n * idealCost G Q (groupSeparatorCall X Y) ≤ Fintype.card V * Q n := by
  by_cases hX : X = ∅
  · simp [groupSeparatorCall, hX]
  · by_cases hY : Y = ∅
    · simp [groupSeparatorCall, hX, hY]
    · have hXn : X.Nonempty := Finset.nonempty_iff_ne_empty.mpr hX
      have hYn : Y.Nonempty := Finset.nonempty_iff_ne_empty.mpr hY
      have hs : 1 ≤ Fintype.card (SetCutVertex X Y) := by
        have : Nonempty (SetCutVertex X Y) := ⟨Sum.inl 0⟩
        exact Fintype.card_pos
      have hsm := setCutVertex_card_le hXY hXn hYn
      simp only [groupSeparatorCall, hX, hY, ite_false, setCutCall_idealCost]
      calc
        _ ≤ Fintype.card (SetCutVertex X Y) * Q n := hQ _ hs (hsm.trans hvn)
        _ ≤ _ := Nat.mul_le_mul_right (Q n) hsm

/-! ### Isolating cuts -/

/-- Twin of `bitSeparatorProgram`. -/
def bitSeparatorCall (R : Finset V) : CallProg V (Fin (Nat.clog 2 R.card) → Finset V) :=
  tableProgram (Nat.clog 2 R.card) (fun j =>
    groupSeparatorCall (bitClass R j.val true) (bitClass R j.val false))

theorem bitSeparator_idealEval {M : ℕ} {QE : ℕ → ℕ} (E : CanonicalSTFamily M QE)
    (G : WeightedGraph V) (hG : InputPromise M G) (R : Finset V) :
    Prog.eval G.cut (bitSeparatorProgram E R) = idealEval G (bitSeparatorCall R) := by
  simp only [bitSeparatorProgram, bitSeparatorCall, tableProgram_eval, idealEval_tableProgram,
    groupSeparator_idealEval E G hG]

theorem bitSeparatorCall_idealCost {Q : ℕ → ℕ} (R : Finset V)
    (hQ : SizeRegular (Fintype.card V) Q) (G : WeightedGraph V) :
    idealCost G Q (bitSeparatorCall R) ≤ Nat.clog 2 R.card * Q (Fintype.card V) := by
  rw [bitSeparatorCall, idealCost_tableProgram]
  calc
    _ ≤ ∑ _j : Fin (Nat.clog 2 R.card), Q (Fintype.card V) :=
      Finset.sum_le_sum (fun j _ => groupSeparatorCall_idealCost
        (Certificate.disjoint_bitClass R j.val) hQ G)
    _ = _ := by simp

/-- Twin of `isolatingLocalProgram`. -/
def isolatingLocalCall (P : Finset V) (v : V) : CallProg V (Finset V) :=
  if hv : v ∈ P then
    if P ≠ Finset.univ then shoreCutCall P ⟨v, hv⟩ else pure ∅
  else pure ∅

theorem isolatingLocal_idealEval {M : ℕ} {QE : ℕ → ℕ} (E : CanonicalSTFamily M QE)
    (G : WeightedGraph V) (hG : InputPromise M G) (P : Finset V) (v : V) :
    Prog.eval G.cut (isolatingLocalProgram E P v) = idealEval G (isolatingLocalCall P v) := by
  unfold isolatingLocalProgram isolatingLocalCall
  split_ifs <;> simp [shoreCut_idealEval E G hG]

theorem isolatingLocalCall_idealCost (G : WeightedGraph V) (Q : ℕ → ℕ) (P : Finset V) (v : V) :
    idealCost G Q (isolatingLocalCall P v) ≤ localCharge Q P v := by
  by_cases hv : v ∈ P
  · by_cases hp : P ≠ Finset.univ
    · rw [isolatingLocalCall, dite_eq_left hv, ite_eq_left hp, localCharge, ite_eq_left ⟨hv, hp⟩,
        shoreCutCall_idealCost, shoreVertex_card]
    · simp [isolatingLocalCall, localCharge, hv, hp]
  · simp [isolatingLocalCall, localCharge, hv]

/-- Twin of `isolatingProgram`. -/
def isolatingCall (R : Finset V) : CallProg V (R → Finset V) :=
  (bitSeparatorCall R).bind (fun cuts => finiteTable
    (fun v : R => isolatingLocalCall (isolatingCell R cuts v.val) v.val))

theorem isolating_idealEval {M : ℕ} {QE : ℕ → ℕ} (E : CanonicalSTFamily M QE)
    (G : WeightedGraph V) (hG : InputPromise M G) (R : Finset V) :
    Prog.eval G.cut (isolatingProgram E R) = idealEval G (isolatingCall R) := by
  simp only [isolatingProgram, isolatingCall, Prog.eval_bind, finiteTable_eval, idealEval_bind,
    idealEval_finiteTable, bitSeparator_idealEval E G hG, isolatingLocal_idealEval E G hG]

theorem isolatingCall_idealCost {Q : ℕ → ℕ} (R : Finset V) (hn : 0 < Fintype.card V)
    (hQ : SizeRegular (Fintype.card V) Q) (G : WeightedGraph V) :
    idealCost G Q (isolatingCall R) ≤ (Nat.clog 2 R.card + 2) * Q (Fintype.card V) := by
  let cuts := idealEval G (bitSeparatorCall R)
  have hlocal : (∑ v : R, idealCost G Q
      (isolatingLocalCall (isolatingCell R cuts v.val) v.val)) ≤ 2 * Q (Fintype.card V) := by
    calc
      _ ≤ ∑ v : R, localCharge Q (isolatingCell R cuts v.val) v.val :=
        Finset.sum_le_sum (fun v _ => isolatingLocalCall_idealCost G Q _ _)
      _ = ∑ v ∈ R, localCharge Q (isolatingCell R cuts v) v := by
        rw [Finset.sum_coe_sort_eq_attach]
        exact Finset.sum_attach R (fun v => localCharge Q (isolatingCell R cuts v) v)
      _ ≤ _ := isolatingLocal_totalCharge R cuts hn hQ
  rw [isolatingCall, idealCost_bind, idealCost_finiteTable]
  have hbit := bitSeparatorCall_idealCost R hQ G
  change idealCost G Q (bitSeparatorCall R) +
    (∑ v : R, idealCost G Q (isolatingLocalCall (isolatingCell R cuts v.val) v.val)) ≤ _
  nlinarith

theorem isolatingCall_idealCost_scaled {n : ℕ} {Q : ℕ → ℕ} (R : Finset V)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) (G : WeightedGraph V) :
    n * idealCost G Q (isolatingCall R) ≤ ((Nat.clog 2 R.card + 2) * Fintype.card V) * Q n := by
  let cuts := idealEval G (bitSeparatorCall R)
  have hbit : n * idealCost G Q (bitSeparatorCall R) ≤
      Nat.clog 2 R.card * (Fintype.card V * Q n) := by
    rw [bitSeparatorCall, idealCost_tableProgram, Finset.mul_sum]
    calc
      _ ≤ ∑ _j : Fin (Nat.clog 2 R.card), Fintype.card V * Q n :=
        Finset.sum_le_sum (fun j _ => groupSeparatorCall_idealCost_scaled
          (Certificate.disjoint_bitClass R j.val) hvn hQ G)
      _ = _ := by simp
  have hlocal : n * (∑ v : R, idealCost G Q
      (isolatingLocalCall (isolatingCell R cuts v.val) v.val)) ≤
      (2 * Fintype.card V) * Q n := by
    calc
      _ ≤ n * (∑ v : R, localCharge Q (isolatingCell R cuts v.val) v.val) :=
        Nat.mul_le_mul_left n (Finset.sum_le_sum
          (fun v _ => isolatingLocalCall_idealCost G Q _ _))
      _ = n * (∑ v ∈ R, localCharge Q (isolatingCell R cuts v) v) := by
        rw [Finset.sum_coe_sort_eq_attach]
        exact congrArg (fun x => n * x)
          (Finset.sum_attach R (fun v => localCharge Q (isolatingCell R cuts v) v))
      _ ≤ _ := isolatingLocal_totalCharge_scaled R cuts hvn hQ
  rw [isolatingCall, idealCost_bind, idealCost_finiteTable, Nat.mul_add]
  change n * idealCost G Q (bitSeparatorCall R) +
    n * (∑ v : R, idealCost G Q (isolatingLocalCall (isolatingCell R cuts v.val) v.val)) ≤ _
  nlinarith

/-- Twin of `isolatingValuesProgram`: every returned shore's value is queried. -/
def isolatingValuesCall (R : Finset V) : CallProg V (R → Finset V × ℝ) :=
  (isolatingCall R).bind (fun shores =>
    finiteTable (fun v : R => (ask (shores v)).map (fun value => (shores v, value))))

/-- Bridge: the old isolating-values program run with any exact family evaluates
to the twin's ideal output. -/
theorem isolatingValues_idealEval {M : ℕ} {QE : ℕ → ℕ} (E : CanonicalSTFamily M QE)
    (G : WeightedGraph V) (hG : InputPromise M G) (R : Finset V) :
    Prog.eval G.cut (isolatingValuesProgram E R) = idealEval G (isolatingValuesCall R) := by
  simp only [isolatingValuesProgram, isolatingValuesCall, Prog.eval_bind, finiteTable_eval,
    Prog.eval_map, Prog.eval_ask, idealEval_bind, idealEval_finiteTable, idealEval_map,
    idealEval_ask, isolating_idealEval E G hG]

/-- The ideal charged cost of the twin is at most the old budget, at every charge. -/
theorem isolatingValuesCall_idealCost {Q : ℕ → ℕ} (R : Finset V) (hn : 0 < Fintype.card V)
    (hQ : SizeRegular (Fintype.card V) Q) (G : WeightedGraph V) :
    idealCost G Q (isolatingValuesCall R) ≤
      (Nat.clog 2 R.card + 2) * Q (Fintype.card V) + R.card := by
  simpa [isolatingValuesCall] using
    Nat.add_le_add_right (isolatingCall_idealCost R hn hQ G) R.card

/-! ### Groups and the guide base case -/

section Group

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Twin of `groupIsolatingProgram`: isolating cuts on the group quotient. -/
def groupIsolatingCall (U : I → Finset V) : CallProg V (I → Finset V) :=
  (contract (groupMap U) (isolatingCall (groupTerminals U))).map
    (fun output i => pull (groupMap U) (output ⟨Sum.inl i, inl_mem_groupTerminals U i⟩))

theorem groupIsolating_idealEval {M : ℕ} {QE : ℕ → ℕ} (E : CanonicalSTFamily M QE)
    (G : WeightedGraph V) (hG : InputPromise M G) (U : I → Finset V) :
    Prog.eval G.cut (groupIsolatingProgram E U) = idealEval G (groupIsolatingCall U) := by
  have hread : G.cut ∘ pull (groupMap U) = (G.contract (groupMap U)).cut := by
    funext S
    exact (cut_contract G _ S).symm
  simp only [groupIsolatingProgram, groupIsolatingCall, Prog.eval_map, queryMap_eval, hread,
    idealEval_map, idealEval_contract,
    isolating_idealEval E _ (inputPromise_contract G hG (groupMap U))]

theorem groupIsolatingCall_idealCost_scaled {n : ℕ} {Q : ℕ → ℕ} (U : I → Finset V)
    (hU : Pairwise (fun i j => Disjoint (U i) (U j))) (hne : ∀ i, (U i).Nonempty)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) (G : WeightedGraph V) :
    n * idealCost G Q (groupIsolatingCall U) ≤
      ((Nat.clog 2 (Fintype.card I) + 2) * Fintype.card V) * Q n := by
  have hsize := groupVertex_card_le U hU hne
  rw [groupIsolatingCall, idealCost_map, idealCost_contract]
  have h := isolatingCall_idealCost_scaled (groupTerminals U) (hsize.trans hvn) hQ
    (G.contract (groupMap U))
  rw [groupTerminals_card] at h
  exact h.trans (Nat.mul_le_mul_right (Q n) (Nat.mul_le_mul_left _ hsize))

end Group

section Guide

variable {N : Type} [Fintype N] [DecidableEq N]

/-- Twin of `sourceBaseProgram`. -/
def sourceBaseCall (s : V) (R : Finset V) : CallProg V (V → Option (CutCandidate V)) :=
  finiteTable (fun t : V => if t ∈ R then pairCandidateCall s t else pure none)

theorem sourceBase_idealEval {M : ℕ} {QE : ℕ → ℕ} (E : CanonicalSTFamily M QE)
    (G : WeightedGraph V) (hG : InputPromise M G) (s : V) (R : Finset V) :
    Prog.eval G.cut (sourceBaseProgram E s R) = idealEval G (sourceBaseCall s R) := by
  simp only [sourceBaseProgram, sourceBaseCall, finiteTable_eval, idealEval_finiteTable]
  funext t
  by_cases ht : t ∈ R
  · simp [ht, pairCandidate_idealEval E G hG]
  · simp [ht]

theorem sourceBaseCall_idealCost (G : WeightedGraph V) (Q : ℕ → ℕ) (s : V) (R : Finset V) :
    idealCost G Q (sourceBaseCall s R) ≤ R.card * (Q (Fintype.card V) + 1) := by
  rw [sourceBaseCall, idealCost_finiteTable]
  calc
    _ ≤ ∑ t : V, if t ∈ R then Q (Fintype.card V) + 1 else 0 := by
      apply Finset.sum_le_sum
      intro t _
      by_cases ht : t ∈ R
      · simpa only [ht, ite_true] using pairCandidateCall_idealCost G Q s t
      · simp [ht]
    _ = ∑ _t ∈ R, (Q (Fintype.card V) + 1) := by
      have hfilter : Finset.univ.filter (fun t : V => t ∈ R) = R := by
        ext t
        simp
      rw [← Finset.sum_filter, hfilter]
    _ = _ := by simp

theorem sourceBaseCall_idealCost_scaled {n : ℕ} {Q : ℕ → ℕ} (G : WeightedGraph V)
    (s : V) (R : Finset V) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) :
    n * idealCost G Q (sourceBaseCall s R) ≤ R.card * (Fintype.card V * Q n + n) := by
  have : Nonempty V := ⟨s⟩
  have hreg := hQ (Fintype.card V) Fintype.card_pos hvn
  calc
    _ ≤ n * (R.card * (Q (Fintype.card V) + 1)) :=
      Nat.mul_le_mul_left n (sourceBaseCall_idealCost G Q s R)
    _ = R.card * (n * Q (Fintype.card V) + n) := by ring
    _ ≤ _ := Nat.mul_le_mul_left R.card (Nat.add_le_add_right hreg n)

/-- Twin of `guideBaseProgram`. -/
def guideBaseCall (T : GuideTree V N) : CallProg V (V → Option (CutCandidate V)) :=
  sourceBaseCall T.source T.realVertices

omit [Fintype N] [DecidableEq N] in
theorem guideBase_idealEval {M : ℕ} {QE : ℕ → ℕ} (E : CanonicalSTFamily M QE)
    (G : WeightedGraph V) (hG : InputPromise M G) (T : GuideTree V N) :
    Prog.eval G.cut (guideBaseProgram E T) = idealEval G (guideBaseCall T) :=
  sourceBase_idealEval E G hG T.source T.realVertices

theorem guideBaseCall_idealCost (G : WeightedGraph V) (Q : ℕ → ℕ) (T : GuideTree V N)
    (hsmall : T.real.card ≤ 10) :
    idealCost G Q (guideBaseCall T) ≤ 10 * (Q (Fintype.card V) + 1) := by
  have h := sourceBaseCall_idealCost G Q T.source T.realVertices
  rw [T.realVertices_card] at h
  exact h.trans (Nat.mul_le_mul_right _ hsmall)

end Guide

end CallProg
end
end CutQueryComplexity.GHReduction.Randomized
