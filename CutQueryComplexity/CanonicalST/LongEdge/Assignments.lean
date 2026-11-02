import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# An explicit logarithmic family of separating assignments

At each doubling, existing assignments are used on both halves, with a
permutation of the right colors to make the joining edge proper. Eight new
assignments cover pairs in opposite halves. All choices are public finite
computations; neither a graph nor a separation oracle is an input.
-/

set_option autoImplicit false

namespace CutQueryComplexity.CanonicalST.LongEdge

open scoped Classical
noncomputable section

structure Assignment where
  p : ℕ → Fin 3
  q : ℕ → Bool

def Proper (ℓ : ℕ) (A : Assignment) : Prop :=
  ∀ i, i + 1 < ℓ → A.p i ≠ A.p (i + 1)

def Covers (ℓ : ℕ) (F : List Assignment) : Prop :=
  ∀ i j, j < ℓ → i + 2 ≤ j →
    ∃ A ∈ F, A.p i = A.p j ∧ A.q i ≠ A.q j

private def rotateColor (c : Fin 3) : Fin 3 := ⟨(c.val + 1) % 3, by omega⟩

private theorem rotateColor_injective : Function.Injective rotateColor := by
  decide

private theorem rotateColor_ne (c : Fin 3) : rotateColor c ≠ c := by
  fin_cases c <;> decide

private def joinColor (m : ℕ) (A : Assignment) (c : Fin 3) : Fin 3 :=
  if A.p (m - 1) = A.p 0 then rotateColor c else c

private theorem joinColor_injective (m : ℕ) (A : Assignment) :
    Function.Injective (joinColor m A) := by
  unfold joinColor
  split_ifs
  · exact rotateColor_injective
  · exact Function.injective_id

private theorem joinColor_boundary (m : ℕ) (A : Assignment) :
    A.p (m - 1) ≠ joinColor m A (A.p 0) := by
  by_cases h : A.p (m - 1) = A.p 0
  · simpa [joinColor, h] using (rotateColor_ne (A.p 0)).symm
  · simp [joinColor, h]

def liftAssignment (m : ℕ) (A : Assignment) : Assignment where
  p i := if i < m then A.p i else joinColor m A (A.p (i - m))
  q i := if i < m then A.q i else A.q (i - m)

theorem liftAssignment_proper {m : ℕ} (hm : 1 ≤ m) {A : Assignment}
    (hA : Proper m A) : Proper (2 * m) (liftAssignment m A) := by
  intro i hi
  by_cases hleft : i + 1 < m
  · simpa [liftAssignment, hleft, show i < m by omega] using hA i hleft
  · by_cases he : i + 1 = m
    · have hil : i < m := by omega
      have hie : i = m - 1 := by omega
      simp only [liftAssignment, hil, he, lt_self_iff_false, ↓reduceIte, Nat.sub_self]
      simpa only [hie] using joinColor_boundary m A
    · have hir : m ≤ i := by omega
      have hnext : ¬ i + 1 < m := by omega
      have heq : i + 1 - m = i - m + 1 := by omega
      have hlocal : i - m + 1 < m := by omega
      simp only [liftAssignment, not_lt.mpr hir, hnext, ↓reduceIte, heq]
      exact fun h => hA (i - m) hlocal (joinColor_injective m A h)

private def boundaryClash (m : ℕ) (a b : Fin 2) : Prop :=
  (m - 1) % 2 = a.val ∧ b.val = 0

private def baseColor (m : ℕ) (a b : Fin 2) (i : ℕ) : Fin 3 :=
  if i < m then (if i % 2 = a.val then 0 else 1)
  else (if (i - m) % 2 = b.val then 0 else 2)

/-- Select a parity class in each half, then repair one endpoint of the
joining edge if both selected classes contain that edge. -/
def crossAssignment (m : ℕ) (a b : Fin 2) (right : Bool) : Assignment where
  p i := if boundaryClash m a b ∧ right = false ∧ i + 1 = m then 2
    else if boundaryClash m a b ∧ right = true ∧ i = m then 1
    else baseColor m a b i
  q i := decide (m ≤ i)

private theorem baseColor_left_ne_two (m : ℕ) (a b : Fin 2) {i : ℕ} (hi : i < m) :
    baseColor m a b i ≠ 2 := by
  simp only [baseColor, hi, ↓reduceIte]
  split_ifs <;> decide

private theorem baseColor_right_ne_one (m : ℕ) (a b : Fin 2) {i : ℕ} (hi : m ≤ i) :
    baseColor m a b i ≠ 1 := by
  simp only [baseColor, not_lt.mpr hi, ↓reduceIte]
  split_ifs <;> decide

private theorem baseColor_internal (m : ℕ) (a b : Fin 2) (i : ℕ)
    (hjoin : i + 1 ≠ m) : baseColor m a b i ≠ baseColor m a b (i + 1) := by
  by_cases hl : i + 1 < m
  · have hil : i < m := by omega
    have ha := a.isLt
    simp only [baseColor, hl, hil, ↓reduceIte]
    split_ifs <;> norm_num at * <;> omega
  · have hir : ¬ i < m := by omega
    have he : i + 1 - m = i - m + 1 := by omega
    have hb := b.isLt
    simp only [baseColor, hl, hir, ↓reduceIte, he]
    split_ifs <;> norm_num at * <;> omega

private theorem baseColor_boundary {m i : ℕ} (a b : Fin 2)
    (he : i + 1 = m) (hc : ¬ boundaryClash m a b) :
    baseColor m a b i ≠ baseColor m a b (i + 1) := by
  have hil : i < m := by omega
  have hie : i = m - 1 := by omega
  simp only [baseColor, hil, he, lt_self_iff_false, ↓reduceIte, Nat.sub_self, Nat.zero_mod]
  unfold boundaryClash at hc
  split_ifs <;> norm_num at *
  omega

theorem crossAssignment_proper {m : ℕ} (_hm : 1 ≤ m)
    (a b : Fin 2) (right : Bool) : Proper (2 * m) (crossAssignment m a b right) := by
  intro i _hi
  by_cases hc : boundaryClash m a b
  · have hca := hc.1
    have hcb := hc.2
    cases right with
    | false =>
        by_cases he : i + 1 = m
        · have hz : baseColor m a b m = 0 := by simp [baseColor, hcb]
          simp [crossAssignment, hc, he, hz]
        · by_cases hn : i + 1 + 1 = m
          · simpa [crossAssignment, hc, he, hn] using
              baseColor_left_ne_two m a b (i := i) (by omega)
          · simpa [crossAssignment, hc, he, hn] using baseColor_internal m a b i he
    | true =>
        by_cases he : i + 1 = m
        · have hne : i ≠ m := by omega
          have hil : i < m := by omega
          have hie : i = m - 1 := by omega
          have hz : baseColor m a b i = 0 := by
            simp only [baseColor, hil, ↓reduceIte]
            simp only [hie, hca, ↓reduceIte]
          simp [crossAssignment, hc, he, hne, hz]
        · by_cases hi : i = m
          · simpa [crossAssignment, hc, hi, he] using
              (baseColor_right_ne_one m a b (i := i + 1) (by omega)).symm
          · simpa [crossAssignment, hc, hi, he] using baseColor_internal m a b i he
  · by_cases he : i + 1 = m
    · simpa [crossAssignment, hc] using baseColor_boundary a b he hc
    · simpa [crossAssignment, hc] using baseColor_internal m a b i he

def crossFamily (m : ℕ) : List Assignment :=
  (Finset.univ : Finset (Fin 2 × Fin 2 × Bool)).toList.map
    (fun t => crossAssignment m t.1 t.2.1 t.2.2)

theorem crossFamily_length (m : ℕ) : (crossFamily m).length = 8 := by
  simp [crossFamily]

theorem crossFamily_proper {m : ℕ} (hm : 1 ≤ m) {A : Assignment}
    (hA : A ∈ crossFamily m) : Proper (2 * m) A := by
  obtain ⟨⟨a, b, r⟩, _, rfl⟩ := List.mem_map.mp hA
  exact crossAssignment_proper hm a b r

theorem crossFamily_separates {m i j : ℕ} (_hm : 1 ≤ m)
    (hi : i < m) (hj : m ≤ j) (hgap : i + 2 ≤ j) :
    ∃ A ∈ crossFamily m, A.p i = A.p j ∧ A.q i ≠ A.q j := by
  let a : Fin 2 := ⟨i % 2, Nat.mod_lt _ (by decide)⟩
  let b : Fin 2 := ⟨(j - m) % 2, Nat.mod_lt _ (by decide)⟩
  let r : Bool := decide (i + 1 = m)
  refine ⟨crossAssignment m a b r, ?_, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨(a, b, r), Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩
  · have hli : ¬ (r = false ∧ i + 1 = m) := by simp [r]
    have hri : ¬ (r = true ∧ i = m) := by simp [r]; omega
    have hlj : j + 1 ≠ m := by omega
    have hrj : ¬ (r = true ∧ j = m) := by simp [r]; omega
    have hleft : (crossAssignment m a b r).p i = 0 := by
      simp [crossAssignment, baseColor, hi, a, hli, hri]
    have hright : (crossAssignment m a b r).p j = 0 := by
      simp [crossAssignment, baseColor, not_lt.mpr hj, b, hlj, hrj]
    exact hleft.trans hright.symm
  · simp [crossAssignment, not_le.mpr hi, hj]

def depthFamily : ℕ → List Assignment
  | 0 => []
  | k + 1 => (depthFamily k).map (liftAssignment (2 ^ k)) ++ crossFamily (2 ^ k)

theorem depthFamily_length (k : ℕ) : (depthFamily k).length = 8 * k := by
  induction k with
  | zero => simp [depthFamily]
  | succ k ih => simp [depthFamily, crossFamily_length, ih]; omega

theorem depthFamily_spec (k : ℕ) :
    (∀ A ∈ depthFamily k, Proper (2 ^ k) A) ∧ Covers (2 ^ k) (depthFamily k) := by
  induction k with
  | zero =>
      constructor
      · simp [depthFamily]
      · intro i j hj hgap
        simp only [pow_zero] at hj
        omega
  | succ k ih =>
      have hm : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by decide)
      have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      constructor
      · intro A hA
        rw [depthFamily, List.mem_append] at hA
        rcases hA with hA | hA
        · obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hA
          rw [hpow]
          exact liftAssignment_proper hm (ih.1 B hB)
        · rw [hpow]
          exact crossFamily_proper hm hA
      · intro i j hj hgap
        rw [hpow] at hj
        by_cases hjl : j < 2 ^ k
        · obtain ⟨A, hA, hp, hq⟩ := ih.2 i j hjl hgap
          refine ⟨liftAssignment (2 ^ k) A, ?_, ?_, ?_⟩
          · apply List.mem_append_left
            exact List.mem_map.mpr ⟨A, hA, rfl⟩
          · simpa [liftAssignment, hjl, show i < 2 ^ k by omega] using hp
          · simpa [liftAssignment, hjl, show i < 2 ^ k by omega] using hq
        · by_cases hil : i < 2 ^ k
          · obtain ⟨A, hA, hp, hq⟩ := crossFamily_separates hm hil (by omega) hgap
            exact ⟨A, List.mem_append_right _ hA, hp, hq⟩
          · have hir : 2 ^ k ≤ i := by omega
            have hjr : 2 ^ k ≤ j := by omega
            obtain ⟨A, hA, hp, hq⟩ := ih.2 (i - 2 ^ k) (j - 2 ^ k) (by omega) (by omega)
            refine ⟨liftAssignment (2 ^ k) A, ?_, ?_, ?_⟩
            · apply List.mem_append_left
              exact List.mem_map.mpr ⟨A, hA, rfl⟩
            · simpa [liftAssignment, hil, hjl] using congrArg (joinColor (2 ^ k) A) hp
            · simpa [liftAssignment, hil, hjl] using hq

/-- The fixed family uses no graph input and is empty for zero or one bin. -/
def family (ℓ : ℕ) : List Assignment := depthFamily (Nat.clog 2 ℓ)

theorem family_length (ℓ : ℕ) : (family ℓ).length = 8 * Nat.clog 2 ℓ :=
  depthFamily_length _

theorem family_adjacent {ℓ : ℕ} {A : Assignment} (hA : A ∈ family ℓ)
    {i : ℕ} (hi : i + 1 < ℓ) : A.p i ≠ A.p (i + 1) :=
  (depthFamily_spec _).1 A hA i (hi.trans_le (Nat.le_pow_clog (by decide) _))

theorem family_separates {ℓ i j : ℕ} (hi : i < ℓ) (hj : j < ℓ)
    (hgap : i + 2 ≤ j ∨ j + 2 ≤ i) :
    ∃ A ∈ family ℓ, A.p i = A.p j ∧ A.q i ≠ A.q j := by
  have hcover := (depthFamily_spec (Nat.clog 2 ℓ)).2
  have hℓ : ℓ ≤ 2 ^ Nat.clog 2 ℓ := Nat.le_pow_clog (by decide) _
  rcases hgap with hgap | hgap
  · exact hcover i j (hj.trans_le hℓ) hgap
  · obtain ⟨A, hA, hp, hq⟩ := hcover j i (hi.trans_le hℓ) hgap
    exact ⟨A, hA, hp.symm, hq.symm⟩

end
end CutQueryComplexity.CanonicalST.LongEdge

#print axioms CutQueryComplexity.CanonicalST.LongEdge.crossAssignment_proper
#print axioms CutQueryComplexity.CanonicalST.LongEdge.depthFamily_spec
#print axioms CutQueryComplexity.CanonicalST.LongEdge.family_length
#print axioms CutQueryComplexity.CanonicalST.LongEdge.family_adjacent
#print axioms CutQueryComplexity.CanonicalST.LongEdge.family_separates
