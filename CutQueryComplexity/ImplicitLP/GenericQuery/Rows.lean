import CutQueryComplexity.ImplicitLP.GenericQuery.Basic
import Mathlib.Data.Nat.Choose.Cast

/-! # General explicit rows, Gram and transpose identities

Every executable matrix/vector below is computed from the public explicit
list. The unknown graph appears only in semantic identities.
-/

set_option autoImplicit false

namespace CutQueryComplexity.ImplicitLP.GenericQuery

open Matrix Finset Spectral
noncomputable section
variable {n m : ℕ}

def rowVector (E : ExplicitRows n m) {G : DiGraph (Fin n)} : Row G m → Fin n → ℝ
  | .inl ⟨p, _⟩ => incVec p.1.1 p.1.2
  | .inr j => E.matrix j

def matrix (G : DiGraph (Fin n)) (E : ExplicitRows n m) :
    Matrix (Fin (rowCount G m)) (Fin n) ℝ :=
  fun i => rowVector E ((rowEquiv G m).symm i)

def iota (G : DiGraph (Fin n)) (E : ExplicitRows n m) (j : Fin n) : Fin (rowCount G m) :=
  rowEquiv G m (.inr (E.iota j))

theorem matrix_idRows (G : DiGraph (Fin n)) (E : ExplicitRows n m) :
    IdRows (matrix G E) (iota G E) := by
  refine ⟨fun a b h => ?_, fun j => ?_⟩
  · have h' := (rowEquiv G m).injective h
    exact E.identity.1 (Sum.inr.inj h')
  · simpa [matrix, iota, rowVector] using E.identity.2 j

theorem hidden_iota (G : DiGraph (Fin n)) (E : ExplicitRows n m) (j : Fin n) :
    hidden G m (iota G E j) = none := by
  simp [hidden, iota, hiddenRow]

theorem matrix_hidden (G : DiGraph (Fin n)) (E : ExplicitRows n m)
    (i : Fin (rowCount G m)) (e : Sym2 (Fin n)) (h : hidden G m i = some e) :
    vecMulVec (matrix G E i) (matrix G E i) = pairMat e := by
  simp only [hidden] at h
  simp only [matrix]
  generalize (rowEquiv G m).symm i = r at h ⊢
  rcases r with ⟨p, k⟩ | j
  · simp only [hiddenRow, Option.some.injEq] at h
    subst h
    simp [rowVector]
  · simp [hiddenRow] at h

/-- Arbitrary explicit rows contribute a fully known positive-semidefinite sum. -/
def knownGram (E : ExplicitRows n m) (d : Fin m → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ j, d j • vecMulVec (E.matrix j) (E.matrix j)

theorem explicitGram_eq (G : DiGraph (Fin n)) (E : ExplicitRows n m) (D : Point n m) :
    explicitGram (matrix G E) (vec G D) (hidden G m) = knownGram E D.explicit := by
  rw [explicitGram, sum_filter, ← (rowEquiv G m).sum_comp]
  simp only [hidden, matrix, vec, Equiv.symm_apply_apply]
  rw [Fintype.sum_sum_type]
  simp [hiddenRow, rowVector, rowIndex, knownGram, Point.explicit]

theorem gram_eq (G : DiGraph (Fin n)) (E : ExplicitRows n m) (D : Point n m)
    (hD : ∀ i, 0 < vec G D i) :
    gram (matrix G E) (vec G D) =
      lap (Sparsify.omegaR G (pairOf D.pair) 0)
        (univ.filter fun e => Sparsify.P0 (pairOf D.pair) e = true) + knownGram E D.explicit := by
  rw [gram_split (hidden G m) G (pairOf D.pair) (matrix_hidden G E)
    (vec_hidden G D) hD (hidden_count G m), explicitGram_eq]

/-- The explicit part of the transpose product needs no graph query. -/
def knownTranspose (E : ExplicitRows n m) (x : Point n m) : Fin n → ℝ :=
  E.matrixᵀ *ᵥ x.explicit

theorem transpose_vec (G : DiGraph (Fin n)) (E : ExplicitRows n m) (x : Point n m) :
    (matrix G E)ᵀ *ᵥ vec G x = DirectedMincut.divz G x.pair + knownTranspose E x := by
  funext w
  simp only [mulVec, dotProduct, transpose_apply, matrix, vec]
  rw [← (rowEquiv G m).sum_comp]
  simp only [Equiv.symm_apply_apply]
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [rowVector, rowIndex, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hz : ∑ p : CPair n, (G.sym p.1.1 p.1.2 : ℝ) *
      (incVec p.1.1 p.1.2 w * x.pair p.1.1 p.1.2) = DirectedMincut.divz G x.pair w := by
    simp only [incVec_apply, sub_mul, ite_mul, one_mul, zero_mul, mul_sub, mul_ite, mul_zero,
      sum_sub_distrib]
    have e1 := sum_cpair_fst (fun a b => (G.sym a b : ℝ) * x.pair a b) w
    have e2 := sum_cpair_snd (fun a b => (G.sym a b : ℝ) * x.pair a b) w
    simp only [eq_comm (a := w)] at e1 e2 ⊢
    rw [e1, e2, DirectedMincut.divz, ← sum_sub_distrib]
    refine sum_congr rfl fun v _ => ?_
    simp only [DirectedMincut.gz, DirectedMincut.mult]
    rcases lt_trichotomy w v with h | rfl | h
    · simp [h, not_lt.mpr h.le]
    · simp
    · simp [h, not_lt.mpr h.le]
  change (∑ p : CPair n, (G.sym p.1.1 p.1.2 : ℝ) *
      (incVec p.1.1 p.1.2 w * x.pair p.1.1 p.1.2)) +
      (∑ j, E.matrix j w * x.explicit j) = _
  rw [hz]
  rfl

/-- Public row products have canonical pair difference and arbitrary explicit dot products. -/
def rowProduct (E : ExplicitRows n m) (y : Fin n → ℝ) : Point n m :=
  Point.mk (fun u v => y u - y v) (E.matrix *ᵥ y)

theorem matrix_mulVec (G : DiGraph (Fin n)) (E : ExplicitRows n m) (y : Fin n → ℝ) :
    matrix G E *ᵥ y = vec G (rowProduct E y) := by
  funext i
  simp only [mulVec, matrix, vec]
  generalize (rowEquiv G m).symm i = r
  rcases r with ⟨p, k⟩ | j
  · exact incVec_dot _ _ _
  · rfl

/-- Public exact residual correction on the designated positive identity coordinates. -/
def repairPoint (E : ExplicitRows n m) (x : Point n m) (rho : Fin n → ℝ) : Point n m :=
  Point.mk x.pair (x.explicit - selector E.iota *ᵥ rho)

theorem vec_repairPoint (G : DiGraph (Fin n)) (E : ExplicitRows n m)
    (x : Point n m) (rho : Fin n → ℝ) :
    vec G (repairPoint E x rho) = vec G x - selector (iota G E) *ᵥ rho := by
  funext i
  obtain ⟨r, rfl⟩ := (rowEquiv G m).surjective i
  simp only [Pi.sub_apply, mulVec, dotProduct, selector, iota, Equiv.apply_eq_iff_eq,
    ite_mul, one_mul, zero_mul, vec, Equiv.symm_apply_apply]
  rcases r with ⟨p, k⟩ | j <;>
    simp [repairPoint, Point.mk, Point.pair, Point.explicit, rowIndex, selector,
      mulVec, dotProduct, ite_mul]

theorem repairPoint_feasible (G : DiGraph (Fin n)) (E : ExplicitRows n m) (x : Point n m) :
    (matrix G E)ᵀ *ᵥ vec G (repairPoint E x ((matrix G E)ᵀ *ᵥ vec G x)) = 0 := by
  rw [vec_repairPoint]
  exact repair_feasible (matrix_idRows G E) (vec G x)

theorem cpair_card (n : ℕ) : Fintype.card (CPair n) = n.choose 2 := by
  rw [Fintype.card_subtype]
  simpa using (Finset.card_product_filter_lt (s := (univ : Finset (Fin n))))

theorem rowCount_le (G : DiGraph (Fin n)) {C : ℝ}
    (hC : ∀ u v, (G.sym u v : ℝ) ≤ C) :
    (rowCount G m : ℝ) ≤ C * n * ((n : ℝ) - 1) / 2 + m := by
  rw [rowCount_eq, Nat.cast_add, Nat.cast_sum]
  have hs : ∑ p : CPair n, (G.sym p.1.1 p.1.2 : ℝ) ≤ C * Fintype.card (CPair n) := by
    calc
      _ ≤ ∑ _p : CPair n, C := sum_le_sum fun p _ => hC p.1.1 p.1.2
      _ = _ := by simp [mul_comm]
  rw [cpair_card, Nat.cast_choose_two] at hs
  nlinarith

/-- The explicit original row envelope suffices for every semantic row. -/
theorem matrix_row_bounds (G : DiGraph (Fin n)) (E : ExplicitRows n m)
    {a0 : ℝ} (ha0 : 0 ≤ a0) (ha1 : a0 ≤ 1)
    (he : ∀ j, a0 ^ 2 ≤ ∑ v, E.matrix j v ^ 2 ∧ ∑ v, E.matrix j v ^ 2 ≤ 2)
    (i : Fin (rowCount G m)) :
    a0 ^ 2 ≤ ∑ v, matrix G E i v ^ 2 ∧ ∑ v, matrix G E i v ^ 2 ≤ 2 := by
  simp only [matrix]
  generalize (rowEquiv G m).symm i = r
  rcases r with ⟨p, k⟩ | j
  · have hown : (incVec p.1.1 p.1.2 p.1.1) ^ 2 = 1 := by
      simp [incVec_apply, p.2.ne]
    have hlo : (1 : ℝ) ≤ ∑ v, (incVec p.1.1 p.1.2 v) ^ 2 := by
      rw [← hown]
      exact single_le_sum (fun v _ => sq_nonneg _) (mem_univ _)
    refine ⟨?_, ?_⟩
    · change a0 ^ 2 ≤ ∑ v, (incVec p.1.1 p.1.2 v) ^ 2
      nlinarith
    · simpa [rowVector, incVec_apply] using sum_sq_ind_sub_le p.1.1 p.1.2
  · exact he j

theorem matrix_row_ne_zero (G : DiGraph (Fin n)) (E : ExplicitRows n m)
    {a0 : ℝ} (ha0 : 0 < a0) (ha1 : a0 ≤ 1)
    (he : ∀ j, a0 ^ 2 ≤ ∑ v, E.matrix j v ^ 2 ∧ ∑ v, E.matrix j v ^ 2 ≤ 2)
    (i : Fin (rowCount G m)) : matrix G E i ≠ 0 := by
  intro hz
  have hlo := (matrix_row_bounds G E ha0.le ha1 he i).1
  have hs : (∑ v, matrix G E i v ^ 2) = 0 := by simp [hz]
  have hp : 0 < a0 ^ 2 := sq_pos_of_pos ha0
  linarith

theorem rowCount_pos (G : DiGraph (Fin n)) (E : ExplicitRows n m) (hn : 0 < n) :
    0 < rowCount G m := Fin.pos (iota G E ⟨0, hn⟩)

#print axioms matrix_idRows
#print axioms explicitGram_eq
#print axioms gram_eq
#print axioms transpose_vec
#print axioms matrix_mulVec
#print axioms vec_repairPoint
#print axioms repairPoint_feasible
#print axioms rowCount_le
#print axioms matrix_row_bounds
#print axioms matrix_row_ne_zero

end
end CutQueryComplexity.ImplicitLP.GenericQuery
