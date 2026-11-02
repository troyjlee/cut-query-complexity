import CutQueryComplexity.GHReduction.GroupSeparator
import CutQueryComplexity.GHReduction.IsolatingCells
import CutQueryComplexity.GHReduction.ShoreContraction
import CutQueryComplexity.GHReduction.GuideBudget

/-! # A canonical isolating-cut query program

The program makes logarithmically many group-separator calls, then one guarded
source–proxy call in each disjoint cell. The size bound includes each proxy.
The budget is valid for every oracle, and correctness uses only the exact
weighted canonical s-t family. A final variant also queries every returned
shore's value, charging these auxiliary queries explicitly.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical BigOperators
open WeightedGraph
open Certificate (bitClass)

variable {V : Type} [Fintype V] [DecidableEq V]

def bitSeparatorProgram {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (R : Finset V) : Prog (Finset V) ℝ (Fin (Nat.clog 2 R.card) → Finset V) :=
  tableProgram (Nat.clog 2 R.card) (fun j =>
    groupSeparator family (bitClass R j.val true) (bitClass R j.val false))

theorem bitSeparatorProgram_correct {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (hG : InputPromise M G) (R : Finset V)
    (j : Fin (Nat.clog 2 R.card)) :
    IsMinTraceCut G R (bitClass R j.val true)
      (Prog.eval G.cut (bitSeparatorProgram family R) j) := by
  simpa only [bitSeparatorProgram, tableProgram_eval, bitClass_union] using
    groupSeparator_correct family G hG (Certificate.disjoint_bitClass R j.val)

theorem bitSeparatorProgram_cost {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (R : Finset V) (hQ : SizeRegular (Fintype.card V) Q) (read : Finset V → ℝ) :
    Prog.cost read (bitSeparatorProgram family R) ≤ Nat.clog 2 R.card * Q (Fintype.card V) := by
  rw [bitSeparatorProgram, tableProgram_cost]
  calc
    _ ≤ ∑ _j : Fin (Nat.clog 2 R.card), Q (Fintype.card V) :=
      Finset.sum_le_sum (fun j _ => groupSeparator_cost family
        (Certificate.disjoint_bitClass R j.val) hQ read)
    _ = _ := by simp

def isolatingLocalProgram {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (P : Finset V) (v : V) : Prog (Finset V) ℝ (Finset V) :=
  if hv : v ∈ P then
    if P ≠ Finset.univ then liftDTree (shoreCutProgram family P ⟨v, hv⟩)
      else Prog.pure ∅
  else Prog.pure ∅

def localCharge (Q : ℕ → ℕ) (P : Finset V) (v : V) : ℕ :=
  if v ∈ P ∧ P ≠ Finset.univ then Q (P.card + 1) else 0

theorem isolatingLocalProgram_cost {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (P : Finset V) (v : V) (read : Finset V → ℝ) :
    Prog.cost read (isolatingLocalProgram family P v) ≤ localCharge Q P v := by
  by_cases hv : v ∈ P
  · by_cases hp : P ≠ Finset.univ
    · rw [isolatingLocalProgram, dif_pos hv, if_pos hp, localCharge, if_pos ⟨hv, hp⟩]
      simpa only [shoreVertex_card] using
        liftDTree_cost_le (shoreCutProgram family P ⟨v, hv⟩) read
    · simp [isolatingLocalProgram, localCharge, hv, hp]
  · simp [isolatingLocalProgram, localCharge, hv]

theorem isolatingLocalProgram_correct {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (hG : InputPromise M G) {R P C : Finset V} {v : V}
    (hv : v ∈ P) (hp : P ≠ Finset.univ) (hPR : P ∩ R = {v})
    (hC : IsCanonicalTraceCut G R {v} C) (hCP : C ⊆ P) :
    Prog.eval G.cut (isolatingLocalProgram family P v) = C := by
  rw [isolatingLocalProgram, dif_pos hv, if_pos hp, liftDTree_eval]
  exact shoreCutProgram_correct family G hG ⟨v, hv⟩ hPR hC hCP

/-- Linear aggregate input size is valid for arbitrary separator answers. -/
theorem isolatingLocal_totalCharge {Q : ℕ → ℕ} (R : Finset V)
    (cuts : Fin (Nat.clog 2 R.card) → Finset V)
    (hn : 0 < Fintype.card V) (hQ : SizeRegular (Fintype.card V) Q) :
    (∑ v ∈ R, localCharge Q (isolatingCell R cuts v) v) ≤ 2 * Q (Fintype.card V) := by
  let A := R.filter (fun v => v ∈ isolatingCell R cuts v ∧ isolatingCell R cuts v ≠ Finset.univ)
  have hAR : A ⊆ R := Finset.filter_subset _ _
  have hsize : (∑ v ∈ A, ((isolatingCell R cuts v).card + 1)) ≤ Fintype.card V * 2 := by
    have hcells : (∑ v ∈ A, (isolatingCell R cuts v).card) ≤ Fintype.card V :=
      (Finset.sum_le_sum_of_subset_of_nonneg hAR (fun _ _ _ => Nat.zero_le _)).trans
        (isolatingCells_size R cuts)
    have hcount : A.card ≤ Fintype.card V :=
      (Finset.card_le_card hAR).trans (Finset.card_le_univ R)
    calc
      _ = (∑ v ∈ A, (isolatingCell R cuts v).card) + A.card := by
        simp [Finset.sum_add_distrib]
      _ ≤ Fintype.card V + Fintype.card V := Nat.add_le_add hcells hcount
      _ = Fintype.card V * 2 := by omega
  have hrange : ∀ v ∈ A, 1 ≤ (isolatingCell R cuts v).card + 1 ∧
      (isolatingCell R cuts v).card + 1 ≤ Fintype.card V := by
    intro v hv
    have hp := (Finset.mem_filter.mp hv).2.2
    exact ⟨by omega, by simpa only [shoreVertex_card] using shoreVertex_card_le hp⟩
  have hsum := sum_primitive_cost_le A (fun v => (isolatingCell R cuts v).card + 1)
    Q hn hrange hQ hsize
  simpa only [A, Finset.sum_filter, localCharge] using hsum

def isolatingProgram {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (R : Finset V) : Prog (Finset V) ℝ (R → Finset V) :=
  (bitSeparatorProgram family R).bind (fun cuts => finiteTable
    (fun v : R => isolatingLocalProgram family (isolatingCell R cuts v.val) v.val))

theorem isolatingProgram_correct {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (hG : InputPromise M G) (R : Finset V) (hR : 2 ≤ R.card)
    (v : R) :
    IsCanonicalTraceCut G R {v.val} (Prog.eval G.cut (isolatingProgram family R) v) := by
  let cuts := Prog.eval G.cut (bitSeparatorProgram family R)
  have hcuts := bitSeparatorProgram_correct family G hG R
  obtain ⟨C, hC⟩ := exists_canonicalTraceCut G (Finset.singleton_subset_iff.mpr v.property)
  have hv := terminal_mem_cell G R cuts hcuts v.property
  have hp := isolatingCell_proper G R cuts hcuts hR v.property
  have hPR := isolatingCell_trace G R cuts hcuts v.property
  have hCP := canonical_iso_subset_cell G R cuts hcuts v.property hC
  rw [isolatingProgram, Prog.eval_bind, finiteTable_eval]
  change IsCanonicalTraceCut G R {v.val}
    (Prog.eval G.cut (isolatingLocalProgram family (isolatingCell R cuts v.val) v.val))
  rw [isolatingLocalProgram_correct family G hG hv hp hPR hC hCP]
  exact hC

theorem isolatingProgram_cost {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (R : Finset V) (hn : 0 < Fintype.card V) (hQ : SizeRegular (Fintype.card V) Q)
    (read : Finset V → ℝ) :
    Prog.cost read (isolatingProgram family R) ≤ (Nat.clog 2 R.card + 2) * Q (Fintype.card V) := by
  let cuts := Prog.eval read (bitSeparatorProgram family R)
  have hlocal : (∑ v : R, Prog.cost read
      (isolatingLocalProgram family (isolatingCell R cuts v.val) v.val)) ≤ 2 * Q (Fintype.card V) := by
    calc
      _ ≤ ∑ v : R, localCharge Q (isolatingCell R cuts v.val) v.val :=
        Finset.sum_le_sum (fun v _ => isolatingLocalProgram_cost family _ _ read)
      _ = ∑ v ∈ R, localCharge Q (isolatingCell R cuts v) v := by
        rw [Finset.sum_coe_sort_eq_attach]
        exact Finset.sum_attach R (fun v => localCharge Q (isolatingCell R cuts v) v)
      _ ≤ _ := isolatingLocal_totalCharge R cuts hn hQ
  rw [isolatingProgram, Prog.cost_bind, finiteTable_cost]
  have hbit := bitSeparatorProgram_cost family R hQ read
  change Prog.cost read (bitSeparatorProgram family R) +
    (∑ v : R, Prog.cost read (isolatingLocalProgram family (isolatingCell R cuts v.val) v.val)) ≤ _
  nlinarith

theorem isolatingLocal_totalCharge_scaled {n : ℕ} {Q : ℕ → ℕ} (R : Finset V)
    (cuts : Fin (Nat.clog 2 R.card) → Finset V)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) :
    n * (∑ v ∈ R, localCharge Q (isolatingCell R cuts v) v) ≤
      (2 * Fintype.card V) * Q n := by
  have hterm : ∀ v ∈ R,
      n * localCharge Q (isolatingCell R cuts v) v ≤ ((isolatingCell R cuts v).card + 1) * Q n := by
    intro v _
    by_cases ha : v ∈ isolatingCell R cuts v ∧ isolatingCell R cuts v ≠ Finset.univ
    · rw [localCharge, if_pos ha]
      have hle : (isolatingCell R cuts v).card + 1 ≤ Fintype.card V := by
        simpa only [shoreVertex_card] using shoreVertex_card_le ha.2
      exact hQ _ (by omega) (hle.trans hvn)
    · rw [localCharge, if_neg ha, Nat.mul_zero]
      exact Nat.zero_le _
  calc
    _ = ∑ v ∈ R, n * localCharge Q (isolatingCell R cuts v) v := Finset.mul_sum _ _ _
    _ ≤ ∑ v ∈ R, ((isolatingCell R cuts v).card + 1) * Q n := Finset.sum_le_sum hterm
    _ = ((∑ v ∈ R, (isolatingCell R cuts v).card) + R.card) * Q n := by
      rw [← Finset.sum_mul, Finset.sum_add_distrib]
      simp
    _ ≤ _ := Nat.mul_le_mul_right (Q n) (by
      have := isolatingCells_size R cuts
      have := Finset.card_le_univ R
      omega)

theorem isolatingProgram_cost_scaled {M n : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (R : Finset V) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (read : Finset V → ℝ) :
    n * Prog.cost read (isolatingProgram family R) ≤
      ((Nat.clog 2 R.card + 2) * Fintype.card V) * Q n := by
  let cuts := Prog.eval read (bitSeparatorProgram family R)
  have hbit : n * Prog.cost read (bitSeparatorProgram family R) ≤
      Nat.clog 2 R.card * (Fintype.card V * Q n) := by
    rw [bitSeparatorProgram, tableProgram_cost, Finset.mul_sum]
    calc
      _ ≤ ∑ _j : Fin (Nat.clog 2 R.card), Fintype.card V * Q n :=
        Finset.sum_le_sum (fun j _ => groupSeparator_cost_scaled family
          (Certificate.disjoint_bitClass R j.val) hvn hQ read)
      _ = _ := by simp
  have hlocal : n * (∑ v : R, Prog.cost read
      (isolatingLocalProgram family (isolatingCell R cuts v.val) v.val)) ≤
      (2 * Fintype.card V) * Q n := by
    calc
      _ ≤ n * (∑ v : R, localCharge Q (isolatingCell R cuts v.val) v.val) :=
        Nat.mul_le_mul_left n (Finset.sum_le_sum
          (fun v _ => isolatingLocalProgram_cost family _ _ read))
      _ = n * (∑ v ∈ R, localCharge Q (isolatingCell R cuts v) v) := by
        rw [Finset.sum_coe_sort_eq_attach]
        exact congrArg (fun x => n * x)
          (Finset.sum_attach R (fun v => localCharge Q (isolatingCell R cuts v) v))
      _ ≤ _ := isolatingLocal_totalCharge_scaled R cuts hvn hQ
  rw [isolatingProgram, Prog.cost_bind, finiteTable_cost, Nat.mul_add]
  change n * Prog.cost read (bitSeparatorProgram family R) +
    n * (∑ v : R, Prog.cost read (isolatingLocalProgram family (isolatingCell R cuts v.val) v.val)) ≤ _
  nlinarith

/-- The supplied s-t solver returns shores. Their values require and receive
one additional original cut query each. -/
def isolatingValuesProgram {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (R : Finset V) : Prog (Finset V) ℝ (R → Finset V × ℝ) :=
  (isolatingProgram family R).bind (fun shores =>
    finiteTable (fun v : R => (Prog.ask (shores v)).map (fun value => (shores v, value))))

theorem isolatingValuesProgram_correct {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (hG : InputPromise M G) (R : Finset V) (hR : 2 ≤ R.card)
    (v : R) :
    IsCanonicalTraceCut G R {v.val} (Prog.eval G.cut (isolatingValuesProgram family R) v).1 ∧
      (Prog.eval G.cut (isolatingValuesProgram family R) v).2 =
        G.cut (Prog.eval G.cut (isolatingValuesProgram family R) v).1 := by
  simp only [isolatingValuesProgram, Prog.eval_bind, finiteTable_eval, Prog.eval_map,
    Prog.eval_ask]
  exact ⟨isolatingProgram_correct family G hG R hR v, by simp⟩

theorem isolatingValuesProgram_cost {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (R : Finset V) (hn : 0 < Fintype.card V) (hQ : SizeRegular (Fintype.card V) Q)
    (read : Finset V → ℝ) :
    Prog.cost read (isolatingValuesProgram family R) ≤
      (Nat.clog 2 R.card + 2) * Q (Fintype.card V) + R.card := by
  simpa [isolatingValuesProgram] using
    Nat.add_le_add_right (isolatingProgram_cost family R hn hQ read) R.card

def isolatingTree {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q) (R : Finset V) :
    DTree (Finset V) ℝ (Option (R → Finset V × ℝ))
      ((Nat.clog 2 R.card + 2) * Q (Fintype.card V) + R.card) :=
  Prog.toDTree (isolatingValuesProgram family R) _

theorem isolatingTree_correct {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (hG : InputPromise M G) (R : Finset V) (hR : 2 ≤ R.card)
    (hQ : SizeRegular (Fintype.card V) Q) :
    ∃ output, (isolatingTree family R).eval G.cut = some output ∧
      ∀ v : R, IsCanonicalTraceCut G R {v.val} (output v).1 ∧ (output v).2 = G.cut (output v).1 := by
  have hn : 0 < Fintype.card V := by have := Finset.card_le_univ R; omega
  refine ⟨Prog.eval G.cut (isolatingValuesProgram family R), ?_, fun v =>
    isolatingValuesProgram_correct family G hG R hR v⟩
  exact Prog.toDTree_eval _ _ _ (isolatingValuesProgram_cost family R hn hQ G.cut)

end
end CutQueryComplexity.GHReduction
