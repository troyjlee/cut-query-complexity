import CutQueryComplexity.ImplicitLP.LPRows
import CutQueryComplexity.ImplicitLP.Aggregate

/-! # Hidden `Aᵀy` products as row aggregates (D7 item 1/5)

Two hidden products enter the Newton step: the right-hand side `Aᵀ(D̂q̂)` of the frozen
system, and the repair residual `Aᵀh̃`. Both apply `Aᵀ` to a vector that is constant on the
copies of each pair. By `lpA_transpose_lpVec` their hidden part is `divz G z`, and
`divz G z w = Σ_{x ≠ w} sym(w,x) · g(w,x)` with the antisymmetric public pair formula
`g(w,x) = z(w,x)` for `w < x` and `−z(x,w)` for `x < w` (`divz_eq_row`). So one row aggregate
computes it. It is exact on the grid (`hiddenDiv_exact`), and within `deg(w)·2^{−p}` after
rounding a real formula (`hiddenDiv_err`). It costs `6Bn` queries.
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset

noncomputable section

variable {n : ℕ}

/-- The antisymmetric public pair formula of a pair vector `z` (canonical orientation `u < v`). -/
def antiForm (z : Fin n → Fin n → ℝ) (w x : Fin n) : ℝ :=
  if w < x then z w x else if x < w then -z x w else 0

/-- **The hidden divergence is a row aggregate.** -/
theorem divz_eq_row (G : DiGraph (Fin n)) (z : Fin n → Fin n → ℝ) (w : Fin n) :
    DirectedMincut.divz G z w = ∑ x ∈ univ.erase w, (G.sym w x : ℝ) * antiForm z w x := by
  rw [DirectedMincut.divz, ← sum_erase_add _ _ (mem_univ w)]
  have h0 : DirectedMincut.gz G z w w = 0 := by simp [DirectedMincut.gz]
  rw [h0, add_zero]
  refine sum_congr rfl fun x _ => ?_
  simp only [DirectedMincut.gz, DirectedMincut.mult, antiForm]
  rcases lt_trichotomy w x with h | rfl | h
  · simp [h]
  · simp
  · simp [h, not_lt.mpr h.le, G.sym_comm x w]

/-- **Exact hidden divergence** on a grid: if `antiForm z` is an integer multiple of `2^e` with
`B` magnitude bits, one `allRowsUniv` call returns `divz G z`. -/
theorem hiddenDiv_exact (G : DiGraph (Fin n)) (z : Fin n → Fin n → ℝ) (e : ℤ) (B : ℕ)
    (hm : ∀ w x, ∃ m : ℤ, antiForm z w x = m * (2 : ℝ) ^ e)
    (hB : ∀ w x, |antiForm z w x| < (2 : ℝ) ^ B * (2 : ℝ) ^ e) :
    (allRowsUniv (intFormula (fun w x => ⌊antiForm z w x / (2 : ℝ) ^ e⌋) e B)
      fun _ _ => true).eval G.out = DirectedMincut.divz G z := by
  funext w
  rw [allRowsUniv_correct, divz_eq_row, rowCand_true]
  refine sum_congr rfl fun x _ => ?_
  congr 1
  obtain ⟨m, hmx⟩ := hm w x
  have h2 : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) e
  have hfl : ⌊antiForm z w x / (2 : ℝ) ^ e⌋ = m := by
    rw [hmx, mul_div_cancel_right₀ _ h2.ne', Int.floor_intCast]
  have hmB : m.natAbs < 2 ^ B := by
    have hb := hB w x
    rw [hmx, abs_mul, abs_of_pos h2] at hb
    have h3 : |(m : ℝ)| < 2 ^ B := lt_of_mul_lt_mul_right hb h2.le
    have h4 : ((m.natAbs : ℕ) : ℝ) < ((2 ^ B : ℕ) : ℝ) := by
      rw [Nat.cast_natAbs, Nat.cast_pow, Nat.cast_ofNat]
      simpa [Int.cast_abs] using h3
    exact_mod_cast h4
  rw [intFormula_val _ e B (by simpa [hfl] using hmB), hfl, hmx]

/-- **Certified hidden divergence** of a real pair vector, rounded to `2^{−p}`. -/
theorem hiddenDiv_err (G : DiGraph (Fin n)) (z : Fin n → Fin n → ℝ) {p B : ℕ}
    (hB : ∀ w x, (⌊antiForm z w x * 2 ^ p⌋).natAbs < 2 ^ B) (w : Fin n) :
    |(allRowsUniv (roundFormula (antiForm z) p B) fun _ _ => true).eval G.out w -
        DirectedMincut.divz G z w| ≤
      (∑ x ∈ univ.erase w, (G.sym w x : ℝ)) * (1 / 2 ^ p) := by
  have h := certRow_err G (φ := antiForm z) (p := p) (B := B) (fun _ _ => true) w
    (fun x _ => hB w x)
  rw [rowCand_true] at h
  rwa [divz_eq_row]

/-- **The full `Aᵀx`** of the LP on copied points: the hidden aggregate plus explicit terms. -/
theorem lp_transpose_eq_div (G : DiGraph (Fin n)) (s t : Fin n)
    (pt : DirectedMincut.LPPoint (Fin n)) (w : Fin n) :
    ((lpA G s t)ᵀ *ᵥ lpVec G pt) w =
      (∑ x ∈ univ.erase w, (G.sym w x : ℝ) * antiForm pt.z w x) +
        pt.q * DirectedMincut.chi s t w + pt.yp w - pt.ym w := by
  rw [lpA_transpose_lpVec]
  dsimp only
  rw [divz_eq_row]

end

end ImplicitLP
end CutQueryComplexity
