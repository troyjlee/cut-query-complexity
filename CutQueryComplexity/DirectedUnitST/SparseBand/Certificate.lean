import CutQueryComplexity.DirectedUnitST.SparseBand.Grid
import CutQueryComplexity.DirectedUnitST.SparseBand.Counting
import CutQueryComplexity.Model.Deterministic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.FinRange

/-! # Executable public selection and its unconditional certificate

The search enumerates rectangular offset arrays and restricts them to canonical
pairs. This redundant enumeration avoids any noncomputable ordering of functions.
All enumeration and checking use finite lists and integer arithmetic.
The exhaustive offline search has no running-time claim; the query model charges
only calls to the hidden graph oracle, and this search makes none.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DirectedUnitST.SparseBand

/-- Explicit finite enumeration of vectors over a supplied finite list. -/
def enumerateFin {A : Type} (values : List A) : (n : ℕ) → List (Fin n → A)
  | 0 => [Fin.elim0]
  | n + 1 => values.flatMap fun a => (enumerateFin values n).map (Fin.cons a)

theorem mem_enumerateFin {A : Type} (values : List A) (n : ℕ) (f : Fin n → A)
    (hf : ∀ i, f i ∈ values) : f ∈ enumerateFin values n := by
  induction n with
  | zero =>
      have heq : f = Fin.elim0 := by funext i; exact Fin.elim0 i
      simp [enumerateFin, heq]
  | succ n ih =>
      simp only [enumerateFin, List.mem_flatMap, List.mem_map]
      exact ⟨f 0, hf 0, Fin.tail f, ih (Fin.tail f) (fun i => hf i.succ),
        Fin.cons_self_tail f⟩

def offsetCandidates (n k : ℕ) : List (OffsetTable n k) :=
  (enumerateFin (enumerateFin (List.finRange (2 * k + 1)) n) n).map
    (fun f e => f e.val.1 e.val.2)

theorem mem_offsetCandidates {n k : ℕ} (c : OffsetTable n k) :
    c ∈ offsetCandidates n k := by
  let f (i j : Fin n) : Offset k := if h : i < j then c ⟨(i, j), h⟩ else ⟨0, by omega⟩
  apply List.mem_map.mpr
  refine ⟨f, ?_, ?_⟩
  · apply mem_enumerateFin
    intro i
    apply mem_enumerateFin
    intro j
    exact List.mem_finRange _
  · funext e
    simp [f, e.property]

def firstAccepted {A : Type} (p : A → Bool) : List A → Option A
  | [] => none
  | a :: rest => if p a then some a else firstAccepted p rest

theorem firstAccepted_spec {A : Type} (p : A → Bool) (xs : List A)
    (h : ∃ a ∈ xs, p a = true) :
    ∃ a, firstAccepted p xs = some a ∧ p a = true := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
      by_cases ha : p a = true
      · exact ⟨a, by simp [firstAccepted, ha], ha⟩
      · obtain ⟨b, hb, hpb⟩ := h
        have hbx : b ∈ xs := by
          rcases List.mem_cons.mp hb with rfl | hb
          · exact False.elim (ha hpb)
          · exact hb
        obtain ⟨b, hb, hpb⟩ := ih ⟨b, hbx, hpb⟩
        exact ⟨b, by simpa [firstAccepted, ha] using hb, hpb⟩

/-- Total, deterministic public search. Existence rules out the finite fallback
whenever `k` is positive. -/
def selectOffsets (n k : ℕ) : OffsetTable n k :=
  (firstAccepted (fun c => decide (GridAccept c)) (offsetCandidates n k)).getD
    (fun _ => ⟨0, by omega⟩)

theorem selectOffsets_gridAccept (n k : ℕ) (hk : 0 < k) :
    GridAccept (selectOffsets n k) := by
  obtain ⟨c, hc⟩ := exists_gridAccept n k hk
  obtain ⟨d, hd, hgood⟩ := firstAccepted_spec (fun c => decide (GridAccept c))
    (offsetCandidates n k) ⟨c, mem_offsetCandidates c, by simpa using hc⟩
  simpa [selectOffsets, hd] using of_decide_eq_true hgood

/-- One public rational table bounds the active pairs of every real potential. -/
theorem selectOffsets_good (n k : ℕ) (hk : 0 < k) :
    BandGood (selectOffsets n k) :=
  gridAccept_bandGood hk _ (selectOffsets_gridAccept n k hk)

/-- A graph-independent mask computable from public rational potentials. -/
def rationalActivePairs {n k : ℕ} (c : OffsetTable n k) (r : Fin n → ℚ) :
    Finset (Pair n) := Finset.univ.filter
      (fun e => |r e.val.1 - r e.val.2 - offsetRat c e| < 1 / (k : ℚ))

theorem rationalActivePairs_cast {n k : ℕ} (c : OffsetTable n k) (r : Fin n → ℚ) :
    rationalActivePairs c r = activePairs c (fun v => (r v : ℝ)) := by
  classical
  ext e
  simp only [rationalActivePairs, activePairs, Finset.mem_filter, Finset.mem_univ,
    true_and, Active]
  simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using
    (Rat.cast_lt (K := ℝ) (p := |r e.val.1 - r e.val.2 - offsetRat c e|)
      (q := 1 / (k : ℚ))).symm

theorem rationalActivePairs_card_le (n k : ℕ) (hk : 0 < k) (r : Fin n → ℚ) :
    (rationalActivePairs (selectOffsets n k) r).card ≤ bandBudget n k := by
  rw [rationalActivePairs_cast]
  exact selectOffsets_good n k hk _

/-- The fractional-coefficient mask uses only one public integer per pair.
Its signed endpoint tests match the rational quantization interface. -/
def coefficientMask {n : ℕ} (Q : ℕ) (h : Pair n → ℤ) : Finset (Pair n) :=
  Finset.univ.filter (fun e => -(Q : ℤ) < h e ∧ h e < (Q : ℤ))

/-- The local quantization implication transfers the unconditional sparse-band
bound to the public coefficient mask. -/
theorem coefficientMask_card_le {n k : ℕ} (hk : 0 < k) (r : Fin n → ℝ)
    (Q : ℕ) (h : Pair n → ℤ)
    (hactive : ∀ e, -(Q : ℤ) < h e ∧ h e < (Q : ℤ) →
      Active (selectOffsets n k) r e) :
    (coefficientMask Q h).card ≤ bandBudget n k := by
  classical
  calc
    _ ≤ (activePairs (selectOffsets n k) r).card := by
      apply Finset.card_le_card
      intro e he
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hactive e (Finset.mem_filter.mp he).2⟩
    _ ≤ bandBudget n k := selectOffsets_good n k hk r

/-- The actual public table selection as a zero-query decision tree. -/
def offsetsProg (n k : ℕ) :
    DTree (Finset (Fin n)) ℕ (OffsetTable n k) 0 := DTree.pure (selectOffsets n k)

@[simp] theorem offsetsProg_eval (n k : ℕ) (read : Finset (Fin n) → ℕ) :
    (offsetsProg n k).eval read = selectOffsets n k := rfl

@[simp] theorem offsetsProg_cost (n k : ℕ) (read : Finset (Fin n) → ℕ) :
    (offsetsProg n k).cost read = 0 := rfl

theorem offsetsProg_good (n k : ℕ) (hk : 0 < k) (read : Finset (Fin n) → ℕ) :
    BandGood ((offsetsProg n k).eval read) := selectOffsets_good n k hk

#print axioms exists_component_translate
#print axioms exists_grid_cover
#print axioms gridAccept_bandGood
#print axioms offset_band_card_le_five
#print axioms finite_exp_moment
#print axioms exists_gridAccept
#print axioms mem_offsetCandidates
#print axioms selectOffsets_good
#print axioms rationalActivePairs_card_le
#print axioms coefficientMask_card_le
#print axioms selectOffsets
#print axioms offsetsProg_cost
#print axioms offsetsProg_good

end CutQueryComplexity.DirectedUnitST.SparseBand
