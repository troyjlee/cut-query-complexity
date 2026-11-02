import CutQueryComplexity.Sparsify.Asymptotic
import Mathlib.Data.Nat.Size

/-! # Structural guarantees for every returned output (D4)

Unlike the spectral approximation, the structural properties hold on **every** execution, with
no probability attached. `sinv_next` preserves them for an arbitrary mask, and every returned
bundle is valid (`bundleQ_valid`). Hence:

* `levelQ_support`, `runLevels_support`: every reachable state satisfies the structural
  invariant `SInv`;
* `sparsify_support`: every `some out` in the output distribution's support has nonnegative
  weights, is supported on actual pairs of positive public weight, has at most `R t capH` pairs,
  and stores each pair once with weight `c_e 4^{r'} w_e` for some `r' < R`;
* `spectral_primitive_support`: with the public parameters, the support size is at most
  `2·10^7 C ε⁻² n D⁶` (`size_le`);
* `stored_dyadic`: if `w_e = m 2^z` is dyadic, the stored weight is `m' 2^z` with the same
  exponent, and the mantissa grows by at most `2R + size(C)` bits: `size m' ≤ size m + 2R +
  size C`. This is `O(R + log C)` bits.
-/

namespace CutQueryComplexity
namespace Sparsify

open Finset Probability Spanner Spectral
open scoped ENNReal

noncomputable section

attribute [local instance 10] Classical.propDecidable

variable {n : ℕ} {G : DiGraph (Fin n)} {w : Sym2 (Fin n) → ℝ} {K J t : ℕ}

/-- **Every state a level can return satisfies the structural invariant.** -/
theorem levelQ_support (hw0 : ∀ e, 0 ≤ w e) (hK : n ≤ 2 ^ K) {r : ℕ} {st : LState n}
    (hI : SInv G w K t r st) {st' : LState n}
    (h : some st' ∈ ((levelQ w K J t r st).eval G.out).support) :
    SInv G w K t (r + 1) st' := by
  have hK' : Fintype.card (Fin n) ≤ 2 ^ K := by simpa using hK
  have hℓ : ∀ e, 0 ≤ 1 / w e := fun e => one_div_nonneg.mpr (hw0 e)
  unfold levelQ at h
  rw [RTree.eval_bind, PMF.mem_support_bind_iff] at h
  obtain ⟨o, ho, h⟩ := h
  cases o with
  | none => simp at h
  | some L =>
      obtain ⟨hlen, hL⟩ := bundleQ_valid (keyW_injective w) (fun e f hf => keyW_mono w e f hf) hℓ
        G hK' hK' st.P t L ho
      simp only [RTree.eval_cast, RTree.eval_bind, eval_ofDet, PMF.pure_bind, RTree.eval_pure,
        PMF.support_map, Set.mem_image] at h
      obtain ⟨ξ, -, hξ⟩ := h
      cases hξ
      have hBcard := card_bunion_le hL
      rw [hlen] at hBcard
      refine sinv_next hw0 hI hL hlen (fun e he => multQ_correct G hBcard (fun f hf =>
        not_diag_of_pos (by
          have := bunion_subset hL hf; simp [support] at this; exact this.1)) he) ξ

/-- **Every state the levels can return satisfies the structural invariant.** -/
theorem runLevels_support (hw0 : ∀ e, 0 ≤ w e) (hK : n ≤ 2 ^ K) :
    ∀ (j r : ℕ) (st : LState n), SInv G w K t r st → ∀ st',
      some st' ∈ ((runLevels w K J t j r st).eval G.out).support → SInv G w K t (r + j) st' := by
  intro j
  induction j with
  | zero =>
      intro r st hI st' h
      simp only [runLevels, RTree.eval_pure, PMF.support_pure, Set.mem_singleton_iff,
        Option.some.injEq] at h
      subst h; exact hI
  | succ j ih =>
      intro r st hI st' h
      simp only [runLevels, RTree.eval_cast, RTree.eval_bind, PMF.mem_support_bind_iff] at h
      obtain ⟨o, ho, h⟩ := h
      cases o with
      | none => simp at h
      | some st'' =>
          have := ih (r + 1) st'' (levelQ_support hw0 hK hI ho) st' h
          rwa [show r + 1 + j = r + (j + 1) by omega] at this

theorem sinv_st0 : SInv G w K t 0 (st0 w) where
  hP e he := by simpa [st0, P0] using he
  hout0 _ := le_rfl
  hsupp e he := absurd rfl he
  hsize := by simp [st0]
  hform e he := absurd rfl he

/-- **Structural guarantees for every returned output**, with no probability attached. -/
theorem sparsify_support (hw0 : ∀ e, 0 ≤ w e) (hK : n ≤ 2 ^ K) (R : ℕ)
    {out : Sym2 (Fin n) → ℝ} (h : some out ∈ ((sparsify w K J t R).eval G.out).support) :
    (∀ e, 0 ≤ out e) ∧ (∀ e, out e ≠ 0 → 0 < symS G e ∧ 0 < w e) ∧
      (univ.filter fun e => out e ≠ 0).card ≤ R * (t * capH (Fin n) K) ∧
      ∀ e, out e ≠ 0 → ∃ r' < R, out e = (symS G e : ℝ) * (4 : ℝ) ^ r' * w e := by
  simp only [sparsify, RTree.eval_bind, PMF.mem_support_bind_iff] at h
  obtain ⟨o, ho, h⟩ := h
  cases o with
  | none => simp at h
  | some st =>
      have hI := runLevels_support (t := t) hw0 hK R 0 (st0 w) sinv_st0 st ho
      rw [zero_add] at hI
      simp only [eval_ofDet, termQ_eval, PMF.support_pure, Set.mem_singleton_iff] at h
      split_ifs at h with he
      · cases h
        exact ⟨hI.hout0, hI.hsupp, hI.hsize, fun e he' => (hI.hform e he').2⟩

/-- **With the public parameters**, every returned output has at most
`2·10^7 C ε⁻² n D⁶` pairs. -/
theorem spectral_primitive_support {C ε ζ : ℝ} (h : Hyp n C ε ζ) (hw0 : ∀ e, 0 ≤ w e)
    {out : Sym2 (Fin n) → ℝ}
    (hout : some out ∈ ((sparsify w (pK n) (pJ n C ε ζ) (pt n C ε ζ) (pR n ζ)).eval G.out).support) :
    (∀ e, 0 ≤ out e) ∧ (∀ e, out e ≠ 0 → 0 < symS G e ∧ 0 < w e) ∧
      ((univ.filter fun e => out e ≠ 0).card : ℝ) ≤
        2 * 10 ^ 7 * C / ε ^ 2 * n * Dlog n C ε ζ ^ 6 ∧
      ∀ e, out e ≠ 0 → ∃ r' < pR n ζ, out e = (symS G e : ℝ) * (4 : ℝ) ^ r' * w e := by
  have hK := (params_ok h.hn h.hC h.hε h.hε2 h.hζ h.hζ2).1
  obtain ⟨h1, h2, h3, h4⟩ := sparsify_support hw0 hK (pR n ζ) hout
  refine ⟨h1, h2, ?_, h4⟩
  exact (by exact_mod_cast h3 : ((univ.filter fun e => out e ≠ 0).card : ℝ) ≤
    ((pR n ζ * (pt n C ε ζ * capH (Fin n) (pK n)) : ℕ) : ℝ)).trans (size_le h)

/-- **Dyadic bit growth.** A stored weight `c 4^{r'} w` with dyadic `w = m 2^z` is `m' 2^z`,
whose mantissa has at most `size m + 2R + size C` bits. -/
theorem stored_dyadic {R C₀ c r' m : ℕ} (hc : c ≤ C₀) (hr : r' < R) (z : ℤ) :
    ∃ m' : ℕ, (c : ℝ) * (4 : ℝ) ^ r' * ((m : ℝ) * (2 : ℝ) ^ z) = m' * (2 : ℝ) ^ z ∧
      Nat.size m' ≤ Nat.size m + 2 * R + Nat.size C₀ := by
  refine ⟨c * 4 ^ r' * m, by push_cast; ring, ?_⟩
  rw [Nat.size_le]
  have h1 : c < 2 ^ Nat.size C₀ := lt_of_le_of_lt hc (Nat.lt_size_self C₀)
  have h2 : 4 ^ r' < 2 ^ (2 * R) := by
    rw [pow_mul]; norm_num
    exact Nat.pow_lt_pow_right (by norm_num) hr
  have h3 : m < 2 ^ Nat.size m := Nat.lt_size_self m
  calc c * 4 ^ r' * m < 2 ^ Nat.size C₀ * 2 ^ (2 * R) * 2 ^ Nat.size m :=
        Nat.mul_lt_mul'' (Nat.mul_lt_mul'' h1 h2) h3
    _ = 2 ^ (Nat.size m + 2 * R + Nat.size C₀) := by rw [← pow_add, ← pow_add]; ring_nf

/-- **Every returned weight is dyadic** with the input exponent and `O(R + log C)` more bits. -/
theorem sparsify_dyadic (hw0 : ∀ e, 0 ≤ w e) (hK : n ≤ 2 ^ K) (R : ℕ) {C₀ : ℕ}
    (hC : ∀ e, symS G e ≤ C₀) {m : Sym2 (Fin n) → ℕ} {z : Sym2 (Fin n) → ℤ}
    (hw : ∀ e, w e = m e * (2 : ℝ) ^ z e) {out : Sym2 (Fin n) → ℝ}
    (h : some out ∈ ((sparsify w K J t R).eval G.out).support) (e : Sym2 (Fin n)) :
    ∃ m' : ℕ, out e = m' * (2 : ℝ) ^ z e ∧ Nat.size m' ≤ Nat.size (m e) + 2 * R + Nat.size C₀ := by
  by_cases he : out e = 0
  · exact ⟨0, by rw [he]; simp, by simp⟩
  · obtain ⟨r', hr', hval⟩ := (sparsify_support hw0 hK R h).2.2.2 e he
    obtain ⟨m', hm', hsize⟩ := stored_dyadic (hC e) hr' (z e) (m := m e)
    refine ⟨m', ?_, hsize⟩
    rw [hval, hw e, hm']

end

end Sparsify
end CutQueryComplexity
