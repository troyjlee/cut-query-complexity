import CutQueryComplexity.ImplicitLP.FrozenQuery
import CutQueryComplexity.DirectedMincut.LPReduction

/-! # The rows of the directed LP as an implicit-LP matrix (D7)

The penalized terminal LP of `DirectedMincut.LPReduction` has the constraint
`Bᵀz + qχ + y⁺ − y⁻ = b`. As an implicit LP `Aᵀx = b` its rows (`LPRow G`) are:
* one hidden row `1_u − 1_v` for each of the `sym(u,v)` copies of a canonical pair `u < v`;
* the explicit `q` row `χ = e_s − e_t`;
* the explicit `y⁺` rows `+e_j`, which form the `+I_n` block (`lpA_idRows`);
* the explicit `y⁻` rows `−e_j`.

Frozen weights are a public pair formula `w` on hidden rows and explicit values elsewhere
(`lpD`). Transported to `Fin M` with `Fintype.equivFin`, this data satisfies every hypothesis
of `gram_split`. Hence `gram (lpA) (lpD) = lap(omegaR G w 0) + E` (`lp_gram_split`), and the
frozen-solve theorems apply to the actual LP. Copies of a point `(z, q, y⁺, y⁻)` give
`Aᵀx = Bᵀz + qχ + y⁺ − y⁻` (`lpA_transpose_lpVec`), the LP's own constraint.
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset Spectral

noncomputable section

variable {n : ℕ} (G : DiGraph (Fin n))

/-- Canonical pairs `u < v`. -/
abbrev CPair (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

/-- Row indices of the directed LP: hidden pair copies, then `q`, `y⁺`, `y⁻`. -/
abbrev LPRow := (Σ p : CPair n, Fin (G.sym p.1.1 p.1.2)) ⊕ (Unit ⊕ (Fin n ⊕ Fin n))

variable {G}

/-- The row vector of each LP row. -/
def lpRowVec (s t : Fin n) : LPRow G → Fin n → ℝ
  | .inl ⟨p, _⟩ => incVec p.1.1 p.1.2
  | .inr (.inl ()) => DirectedMincut.chi s t
  | .inr (.inr (.inl j)) => Pi.single j 1
  | .inr (.inr (.inr j)) => -Pi.single j 1

/-- Which rows are hidden copies, and of which pair. -/
def lpHid : LPRow G → Option (Sym2 (Fin n))
  | .inl ⟨p, _⟩ => some s(p.1.1, p.1.2)
  | .inr _ => none

/-- Frozen weights: the public pair formula `w` on hidden rows, explicit values elsewhere. -/
def lpWeight (w : Sym2 (Fin n) → ℝ) (dq : ℝ) (dp dm : Fin n → ℝ) : LPRow G → ℝ
  | .inl ⟨p, _⟩ => w s(p.1.1, p.1.2)
  | .inr (.inl ()) => dq
  | .inr (.inr (.inl j)) => dp j
  | .inr (.inr (.inr j)) => dm j

variable (G)

/-- The number of rows. -/
abbrev lpM : ℕ := Fintype.card (LPRow G)

/-- The row enumeration. -/
def lpEquiv : LPRow G ≃ Fin (lpM G) := Fintype.equivFin _

/-- The LP matrix on `Fin M`. -/
def lpA (s t : Fin n) : Matrix (Fin (lpM G)) (Fin n) ℝ := fun i => lpRowVec s t ((lpEquiv G).symm i)

def lpHidF : Fin (lpM G) → Option (Sym2 (Fin n)) := fun i => lpHid ((lpEquiv G).symm i)

def lpD (w : Sym2 (Fin n) → ℝ) (dq : ℝ) (dp dm : Fin n → ℝ) : Fin (lpM G) → ℝ :=
  fun i => lpWeight w dq dp dm ((lpEquiv G).symm i)

/-- The `+I_n` block: the `y⁺` rows. -/
def lpIota : Fin n → Fin (lpM G) := fun j => lpEquiv G (.inr (.inr (.inl j)))

theorem lpA_idRows (s t : Fin n) : IdRows (lpA G s t) (lpIota G) := by
  refine ⟨fun a b h => ?_, fun j => ?_⟩
  · have := (lpEquiv G).injective h
    simpa using this
  · simp [lpA, lpIota, lpRowVec]

theorem lpHid_iota (j : Fin n) : lpHidF G (lpIota G j) = none := by
  simp [lpHidF, lpIota, lpHid]

theorem lpA_hrow (s t : Fin n) (i : Fin (lpM G)) (e : Sym2 (Fin n)) (h : lpHidF G i = some e) :
    vecMulVec (lpA G s t i) (lpA G s t i) = pairMat e := by
  simp only [lpHidF] at h
  simp only [lpA]
  generalize (lpEquiv G).symm i = x at h ⊢
  rcases x with ⟨p, _⟩ | _
  · simp only [lpHid, Option.some.injEq] at h
    subst h
    simp [lpRowVec]
  · simp [lpHid] at h

theorem lpD_hD (w : Sym2 (Fin n) → ℝ) (dq : ℝ) (dp dm : Fin n → ℝ) (i : Fin (lpM G))
    (e : Sym2 (Fin n)) (h : lpHidF G i = some e) : lpD G w dq dp dm i = w e := by
  simp only [lpHidF] at h
  simp only [lpD]
  generalize (lpEquiv G).symm i = x at h ⊢
  rcases x with ⟨p, _⟩ | _
  · simp only [lpHid, Option.some.injEq] at h
    subst h; rfl
  · simp [lpHid] at h

/-- Copies of `e` among the rows: there are `symS G e` of them. -/
theorem lp_hcount (e : Sym2 (Fin n)) :
    (univ.filter fun i => lpHidF G i = some e).card = Spanner.symS G e := by
  -- transport to the row type
  have h1 : (univ.filter fun i => lpHidF G i = some e).card =
      (univ.filter fun x : LPRow G => lpHid x = some e).card := by
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    exact Fintype.card_congr ((lpEquiv G).symm.subtypeEquiv fun _ => Iff.rfl)
  -- only hidden rows of the pair `e` count
  rw [h1, card_filter, Fintype.sum_sum_type]
  simp only [lpHid, reduceCtorEq, ite_false, sum_const_zero, add_zero, Option.some.injEq]
  rw [Fintype.sum_sigma]
  -- `Σ_{p : u < v} [s(u,v) = e] · sym(u,v) = symS G e`
  induction e using Sym2.ind with
  | h a b =>
      rw [Spanner.symS_mk]
      rcases lt_trichotomy a b with hab | rfl | hab
      · rw [sum_eq_single ⟨(a, b), hab⟩]
        · simp
        · rintro ⟨⟨c, d⟩, hcd⟩ _ hne
          refine sum_eq_zero fun _ _ => ?_
          simp only [ite_eq_right_iff]
          intro h; exfalso
          rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hne rfl
          · exact absurd hab (not_lt.mpr hcd.le)
        · simp
      · rw [DiGraph.sym_self]
        refine sum_eq_zero fun ⟨⟨c, d⟩, hcd⟩ _ => ?_
        refine sum_eq_zero fun _ _ => ?_
        simp only [ite_eq_right_iff]
        intro h; exfalso
        rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact lt_irrefl _ hcd
      · rw [sum_eq_single ⟨(b, a), hab⟩]
        · simp [Sym2.eq_swap, G.sym_comm]
        · rintro ⟨⟨c, d⟩, hcd⟩ _ hne
          refine sum_eq_zero fun _ _ => ?_
          simp only [ite_eq_right_iff]
          intro h; exfalso
          rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact absurd hab (not_lt.mpr hcd.le)
          · exact hne rfl
        · simp

/-- **The LP's frozen normal matrix splits** into the hidden Laplacian (D4's input energy) and
the explicit part. -/
theorem lp_gram_split (s t : Fin n) {w : Sym2 (Fin n) → ℝ} {dq : ℝ} {dp dm : Fin n → ℝ}
    (hDpos : ∀ i, 0 < lpD G w dq dp dm i) :
    gram (lpA G s t) (lpD G w dq dp dm) =
      lap (Sparsify.omegaR G w 0) (univ.filter fun e => Sparsify.P0 w e = true) +
        explicitGram (lpA G s t) (lpD G w dq dp dm) (lpHidF G) :=
  gram_split (lpHidF G) G w (lpA_hrow G s t) (lpD_hD G w dq dp dm) hDpos (lp_hcount G)


/-! ## The LP's own constraint -/

/-- An LP point, copied to every hidden row of its pair. -/
def lpVal (pt : DirectedMincut.LPPoint (Fin n)) : LPRow G → ℝ
  | .inl ⟨p, _⟩ => pt.z p.1.1 p.1.2
  | .inr (.inl ()) => pt.q
  | .inr (.inr (.inl j)) => pt.yp j
  | .inr (.inr (.inr j)) => pt.ym j

def lpVec (pt : DirectedMincut.LPPoint (Fin n)) : Fin (lpM G) → ℝ :=
  fun i => lpVal G pt ((lpEquiv G).symm i)

/-- Sums over canonical pairs with a fixed first or second endpoint. -/
theorem sum_cpair_fst (f : Fin n → Fin n → ℝ) (w : Fin n) :
    ∑ p : CPair n, (if p.1.1 = w then f p.1.1 p.1.2 else 0) =
      ∑ x, if w < x then f w x else 0 := by
  rw [← sum_subtype (univ.filter fun q : Fin n × Fin n => q.1 < q.2) (by simp)
    (fun q : Fin n × Fin n => if q.1 = w then f q.1 q.2 else 0), sum_filter,
    Fintype.sum_prod_type]
  simp only [← ite_and]
  rw [sum_eq_single w]
  · refine sum_congr rfl fun x _ => ?_
    by_cases h : w < x <;> simp [h]
  · intro a _ ha
    refine sum_eq_zero fun x _ => ?_
    simp [ha]
  · simp

theorem sum_cpair_snd (f : Fin n → Fin n → ℝ) (w : Fin n) :
    ∑ p : CPair n, (if p.1.2 = w then f p.1.1 p.1.2 else 0) =
      ∑ x, if x < w then f x w else 0 := by
  rw [← sum_subtype (univ.filter fun q : Fin n × Fin n => q.1 < q.2) (by simp)
    (fun q : Fin n × Fin n => if q.2 = w then f q.1 q.2 else 0), sum_filter,
    Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_eq_single w]
  · by_cases h : x < w <;> simp [h]
  · intro a _ ha
    simp [ha]
  · simp

/-- **`Aᵀx` is the LP's constraint map** `Bᵀz + qχ + y⁺ − y⁻` on copied points. -/
theorem lpA_transpose_lpVec (s t : Fin n) (pt : DirectedMincut.LPPoint (Fin n)) :
    (lpA G s t)ᵀ *ᵥ lpVec G pt = fun w =>
      DirectedMincut.divz G pt.z w + pt.q * DirectedMincut.chi s t w + pt.yp w - pt.ym w := by
  funext w
  simp only [mulVec, dotProduct, transpose_apply, lpA, lpVec]
  rw [← (lpEquiv G).sum_comp]
  simp only [Equiv.symm_apply_apply]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [lpRowVec, lpVal, Fintype.univ_punit, Pi.single_apply, Pi.neg_apply,
    sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hz : ∑ p : CPair n, (G.sym p.1.1 p.1.2 : ℝ) * (incVec p.1.1 p.1.2 w * pt.z p.1.1 p.1.2) =
      DirectedMincut.divz G pt.z w := by
    simp only [incVec_apply, sub_mul, ite_mul, one_mul, zero_mul, mul_sub, mul_ite, mul_zero,
      sum_sub_distrib]
    have e1 := sum_cpair_fst (fun a b => (G.sym a b : ℝ) * pt.z a b) w
    have e2 := sum_cpair_snd (fun a b => (G.sym a b : ℝ) * pt.z a b) w
    simp only [eq_comm (a := w)] at e1 e2 ⊢
    rw [e1, e2, DirectedMincut.divz, ← sum_sub_distrib]
    refine sum_congr rfl fun x _ => ?_
    simp only [DirectedMincut.gz, DirectedMincut.mult]
    rcases lt_trichotomy w x with h | rfl | h
    · simp [h, not_lt.mpr h.le]
    · simp
    · simp [h, not_lt.mpr h.le]
  rw [hz]
  simp [ite_mul]
  ring


set_option maxHeartbeats 1600000 in
/-- **The directed LP's frozen normal solve as a query program.** For the actual LP rows
`lpA`, every structural hypothesis of `lp_frozen_query_solve` (hidden rows, copy counts,
frozen weights, the `+I_n` block) is discharged. What remains are the numerical envelopes,
the D4 output, and the bit bound. -/
theorem lp_rows_frozen_query_solve (s t : Fin n) {w : Sym2 (Fin n) → ℝ} {dq : ℝ}
    {dp dm : Fin n → ℝ} (hDpos : ∀ i, 0 < lpD G w dq dp dm i) {dmin : ℝ} (hdmin : 0 < dmin)
    (hdp : ∀ j, dmin ≤ dp j) (hw0 : ∀ e, 0 ≤ w e)
    {K t' R : ℕ} {δ ε : ℝ} {out : Sym2 (Fin n) → ℝ} (hgood : Sparsify.Good G w K t' δ R out)
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 8) (hδlo : 1 - ε ≤ (1 - δ) ^ R) (hδhi : (1 + δ) ^ R ≤ 1 + ε)
    (b xs : Fin n → ℝ) (hxs : gram (lpA G s t) (lpD G w dq dp dm) *ᵥ xs = b)
    {ℓ Λ : ℝ} (hℓ : 0 < ℓ) (hΛ : 0 ≤ Λ)
    (hlo : ∀ x, ℓ * euc x ^ 2 ≤ x ⬝ᵥ (gram (lpA G s t) (lpD G w dq dp dm) *ᵥ x))
    (hup : ∀ x, x ⬝ᵥ (gram (lpA G s t) (lpD G w dq dp dm) *ᵥ x) ≤ Λ * euc x ^ 2)
    {Xh Eh W : ℝ} (hXh : euc xs ≤ Xh)
    (hEh : enorm (gram (lpA G s t) (lpD G w dq dp dm)) xs ≤ Eh) (hW : ∀ e, |w e| ≤ W)
    {ew : ℤ} (hwg : ∀ e, ∃ m : ℤ, w e = m * (2 : ℝ) ^ ew) (p B : ℕ)
    (hB : W * (2 * (Xh + Real.sqrt (1 / ℓ) *
      (Eh + 2 * (Real.sqrt Λ * (Real.sqrt n * (1 / 2 ^ p)))))) < (2 : ℝ) ^ B * (2 : ℝ) ^ (ew - p))
    (k : ℕ) :
    let P := lap out univ + explicitGram (lpA G s t) (lpD G w dq dp dm) (lpHidF G)
    let xk := (frozenSolveProg w ew p B (explicitGram (lpA G s t) (lpD G w dq dp dm) (lpHidF G))
      P⁻¹ b k 0).eval G.out
    enorm (gram (lpA G s t) (lpD G w dq dp dm)) (xk - xs) ≤
      (1 / 2) ^ k * enorm (gram (lpA G s t) (lpD G w dq dp dm)) xs +
        2 * (Real.sqrt Λ * (Real.sqrt n * (1 / 2 ^ p))) :=
  lp_frozen_query_solve (lpA_hrow G s t) (lpD_hD G w dq dp dm) hDpos (lp_hcount G)
    (lpA_idRows G s t) (lpHid_iota G) hdmin (fun j => by simpa [lpD, lpIota, lpWeight] using hdp j)
    hw0 hgood hε0 hε hδlo hδhi b xs hxs hℓ hΛ hlo hup hXh hEh hW hwg p B hB k

end

end ImplicitLP
end CutQueryComplexity
