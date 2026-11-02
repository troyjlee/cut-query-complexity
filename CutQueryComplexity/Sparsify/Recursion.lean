import CutQueryComplexity.Sparsify.Level

/-! # The spectral sparsification recursion (D4; source `thm:main`)

`runLevels`: `R` levels (`levelQ`), aborting on any failure. `termQ`: at depth `R`, test with
one filtered-neighbor count per vertex whether the actual residual is empty. Return the stored
weights if so, and fail otherwise. `sparsify` composes them.

`sparsify_fail_le`: outside probability `R (t 2^{-J} + γ) + |E(P₀)| 4^{-R}`, where
`γ = 2n exp(−δ² t / (8 C (2K + 1)))`, the output `Q` satisfies
`(1 − δ)^R xᵀLx ≤ xᵀL_Q x ≤ (1 + δ)^R xᵀLx` for every real vector. Its pairs are actual pairs of
positive weight, its weights are nonnegative, and it has at most `R t capH` pairs (`Good`). The
proof combines:
* the per-level invariant (`levelQ_good`, adaptive union bound over levels);
* the survival potential: each original pair survives a level with probability at most `1/4`,
  whatever the bundle (`levelQ_expect`), so a nonempty terminal residual has probability at most
  `|E(P₀)| 4^{-R}` (Markov);
* exact detection of the empty residual by the terminal counts (`termQ_eval`).

Every execution, including failures, uses at most `R · levelBudget + 3n` queries (the type).
-/

namespace CutQueryComplexity
namespace Sparsify

open Finset Probability Spanner Spectral
open scoped ENNReal

noncomputable section

attribute [local instance 10] Classical.propDecidable

variable {n : ℕ} (w : Sym2 (Fin n) → ℝ) (K J t : ℕ)

/-- `j` levels starting at level `r`. -/
def runLevels : (j : ℕ) → ℕ → LState n →
    RTree (Finset (Fin n)) ℕ (Option (LState n)) (j * levelBudget (n := n) K J t)
  | 0, _, st => RTree.pure (PMF.pure (some st))
  | j + 1, r, st => ((levelQ w K J t r st).bind fun o => match o with
      | none => RTree.pure (PMF.pure none)
      | some st' => runLevels j (r + 1) st').cast (by ring)

/-- The terminal emptiness test over listed vertices. -/
def termList (P : Sym2 (Fin n) → Bool) :
    (vs : List (Fin n)) → DTree (Finset (Fin n)) ℕ Bool (3 * vs.length)
  | [] => DTree.pure true
  | v :: vs => ((nbrCount v (univ.filter fun u => u ≠ v ∧ P s(v, u) = true)).bind fun a =>
      (termList P vs).map fun b => decide (a = 0) && b).cast (by simp only [List.length_cons]; ring)

/-- The terminal test: return the stored weights if the actual residual is empty. -/
def termQ (st : LState n) : DTree (Finset (Fin n)) ℕ (Option (Sym2 (Fin n) → ℝ)) (3 * n) :=
  ((termList st.P (univ : Finset (Fin n)).toList).map fun b => if b then some st.out else none).cast
    (by rw [length_toList, card_univ, Fintype.card_fin])

/-- The initial state. -/
def st0 : LState n := ⟨P0 w, fun _ => 0⟩

/-- **The spectral sparsifier.** -/
def sparsify (R : ℕ) :
    RTree (Finset (Fin n)) ℕ (Option (Sym2 (Fin n) → ℝ))
      (R * levelBudget (n := n) K J t + 3 * n) :=
  (runLevels w K J t R 0 (st0 w)).bind fun o => match o with
  | none => RTree.pure (PMF.pure none)
  | some st => RTree.ofDeterministic (termQ st)

variable {w K J t} {G : DiGraph (Fin n)}

theorem termList_eval (P : Sym2 (Fin n) → Bool) (vs : List (Fin n)) :
    (termList P vs).eval G.out = true ↔
      ∀ v ∈ vs, ∀ u, u ≠ v → P s(v, u) = true → G.sym v u = 0 := by
  induction vs with
  | nil => simp [termList]
  | cons v vs ih =>
      simp only [termList, DTree.eval_cast, DTree.eval_bind, DTree.eval_map, Bool.and_eq_true,
        decide_eq_true_eq, ih, List.mem_cons, forall_eq_or_imp]
      rw [nbrCount_eval G (by simp)]
      rw [sum_eq_zero_iff]
      simp only [mem_filter, mem_univ, true_and, and_imp]

theorem termQ_eval (st : LState n) :
    (termQ st).eval G.out = if resid G st.P = ∅ then some st.out else none := by
  simp only [termQ, DTree.eval_cast, DTree.eval_map]
  have h : (termList st.P (univ : Finset (Fin n)).toList).eval G.out = true ↔
      resid G st.P = ∅ := by
    rw [termList_eval]
    constructor
    · intro h
      ext e
      simp only [resid, mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false, not_and]
      intro hP hpos
      induction e using Sym2.ind with
      | h v u =>
          by_cases huv : u = v
          · subst huv; simp at hpos
          · have := h v (mem_toList.mpr (mem_univ v)) u huv hP
            simp [this] at hpos
    · intro h v _ u huv hP
      have : s(v, u) ∉ resid G st.P := by rw [h]; exact Finset.notMem_empty _
      simp only [resid, mem_filter, mem_univ, true_and, not_and, not_lt] at this
      have := this hP
      simpa using this
  by_cases he : resid G st.P = ∅
  · simp only [he, ↓reduceIte, h.mpr he]
  · simp only [he, ↓reduceIte]
    have : (termList st.P (univ : Finset (Fin n)).toList).eval G.out = false := by
      cases hb : (termList st.P (univ : Finset (Fin n)).toList).eval G.out
      · rfl
      · exact absurd (h.mp hb) he
    rw [this]; rfl

/-- **Levels keep the invariant** outside probability `j (t 2^{-J} + γ)`. -/
theorem runLevels_good {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ e, (symS G e : ℝ) ≤ C)
    (hw0 : ∀ e, 0 ≤ w e) (hK : n ≤ 2 ^ K) (ht : 0 < t) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∀ (j r : ℕ) (st : LState n), Inv G w K t δ r st →
      mass ((runLevels w K J t j r st).eval G.out)
        (fun o => ¬ ∃ st', o = some st' ∧ Inv G w K t δ (r + j) st') ≤
      j * (t * (2⁻¹ : ℝ≥0∞) ^ J +
        ENNReal.ofReal (2 * n * Real.exp (-(δ ^ 2) / (8 * (C * (2 * K + 1 : ℕ) / t))))) := by
  intro j
  induction j with
  | zero => intro r st hI; simp [runLevels, hI]
  | succ j ih =>
      intro r st hI
      simp only [runLevels, RTree.eval_cast, RTree.eval_bind]
      have h := mass_bind_le_add ((levelQ w K J t r st).eval G.out)
        (fun o => (match o with
          | none => RTree.pure (PMF.pure none)
          | some st' => runLevels w K J t j (r + 1) st' :
          RTree (Finset (Fin n)) ℕ (Option (LState n)) (j * levelBudget (n := n) K J t)).eval G.out)
        (fun o => ¬ ∃ st', o = some st' ∧ Inv G w K t δ (r + 1) st')
        (fun o => ¬ ∃ st', o = some st' ∧ Inv G w K t δ (r + (j + 1)) st')
        (levelQ_good (J := J) hC0 hC hw0 hK ht hδ hδ1 hI) (fun o ho => by
          push Not at ho
          obtain ⟨st', rfl, hI'⟩ := not_not.mp (by simpa using ho)
          have := ih (r + 1) st' hI'
          rw [show r + 1 + j = r + (j + 1) by omega] at this
          exact this)
      refine h.trans (le_of_eq ?_)
      generalize (t : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ J +
        ENNReal.ofReal (2 * n * Real.exp (-(δ ^ 2) / (8 * (C * (2 * K + 1 : ℕ) / t)))) = X
      rw [Nat.cast_succ]; ring

/-- **The expected terminal residual is at most `|E| 4^{-j}`.** -/
theorem runLevels_expect :
    ∀ (j r : ℕ) (st : LState n), expect ((runLevels w K J t j r st).eval G.out) (phi G) ≤
      (resid G st.P).card * (4⁻¹ : ℝ≥0∞) ^ j := by
  intro j
  induction j with
  | zero => intro r st; simp [runLevels, phi]
  | succ j ih =>
      intro r st
      simp only [runLevels, RTree.eval_cast, RTree.eval_bind, expect_bind]
      calc _ ≤ expect ((levelQ w K J t r st).eval G.out) (fun o => phi G o * (4⁻¹ : ℝ≥0∞) ^ j) :=
            expect_mono_on_support _ fun o _ => by
              cases o with
              | none => simp [phi]
              | some st' => exact ih (r + 1) st'
        _ = expect ((levelQ w K J t r st).eval G.out) (phi G) * (4⁻¹ : ℝ≥0∞) ^ j :=
            expect_mul_const _ _ _
        _ ≤ (resid G st.P).card * 4⁻¹ * (4⁻¹ : ℝ≥0∞) ^ j :=
            mul_le_mul_left (levelQ_expect r st) _
        _ = _ := by rw [pow_succ]; ring

/-- A good output: the spectral approximation, supported in positive input pairs, small. -/
def Good (G : DiGraph (Fin n)) (w : Sym2 (Fin n) → ℝ) (K t : ℕ) (δ : ℝ) (R : ℕ)
    (out : Sym2 (Fin n) → ℝ) : Prop :=
  (∀ x, (1 - δ) ^ R * E0 G w x ≤ Eo out x ∧ Eo out x ≤ (1 + δ) ^ R * E0 G w x) ∧
    (∀ e, 0 ≤ out e) ∧ (∀ e, out e ≠ 0 → 0 < symS G e ∧ 0 < w e) ∧
    (univ.filter fun e => out e ≠ 0).card ≤ R * (t * capH (Fin n) K) ∧
    ∀ e, out e ≠ 0 → ∃ r' < R, out e = (symS G e : ℝ) * (4 : ℝ) ^ r' * w e

theorem inv_st0 (δ : ℝ) : Inv G w K t δ 0 (st0 w) where
  hP e he := by simpa [st0, P0] using he
  hout0 _ := le_rfl
  hsupp e he := absurd rfl he
  hsize := by simp [st0]
  hform e he := absurd rfl he
  hen x := by simp [st0, Eo, E0]

/-- An empty residual has zero energy. -/
theorem Er_eq_zero {P : Sym2 (Fin n) → Bool} (h : resid G P = ∅) (r : ℕ) (x : Fin n → ℝ) :
    Er G w P r x = 0 := by
  unfold Er energy
  refine sum_eq_zero fun e he => ?_
  have hz : symS G e = 0 := by
    by_contra hne
    have : e ∈ resid G P := by
      simp only [resid, mem_filter, mem_univ, true_and] at he ⊢
      exact ⟨he, Nat.pos_of_ne_zero hne⟩
    rw [h] at this; exact Finset.notMem_empty e this
  simp [omegaR, cR, hz]

/-- **The spectral sparsifier succeeds** outside probability
`R (t 2^{-J} + γ) + |E(P₀)| 4^{-R}`. -/
theorem sparsify_fail_le {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ e, (symS G e : ℝ) ≤ C)
    (hw0 : ∀ e, 0 ≤ w e) (hK : n ≤ 2 ^ K) (ht : 0 < t) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (R : ℕ) :
    mass ((sparsify w K J t R).eval G.out) (fun o => ¬ ∃ out, o = some out ∧ Good G w K t δ R out) ≤
      R * (t * (2⁻¹ : ℝ≥0∞) ^ J +
        ENNReal.ofReal (2 * n * Real.exp (-(δ ^ 2) / (8 * (C * (2 * K + 1 : ℕ) / t))))) +
      (resid G (P0 w)).card * (4⁻¹ : ℝ≥0∞) ^ R := by
  set p := (runLevels w K J t R 0 (st0 w)).eval G.out
  have hgood := runLevels_good (J := J) hC0 hC hw0 hK ht hδ hδ1 R 0 (st0 w) (inv_st0 δ)
  have hexp := runLevels_expect (G := G) (w := w) (K := K) (J := J) (t := t) R 0 (st0 w)
  simp only [zero_add] at hgood
  simp only [sparsify, RTree.eval_bind, mass_bind]
  -- pointwise bound on the terminal failure
  have hpt : ∀ o, mass ((match o with
      | none => RTree.pure (PMF.pure none)
      | some st => RTree.ofDeterministic (termQ st) :
        RTree (Finset (Fin n)) ℕ (Option (Sym2 (Fin n) → ℝ)) (3 * n)).eval G.out)
        (fun o => ¬ ∃ out, o = some out ∧ Good G w K t δ R out) ≤
      (if ¬ ∃ st', o = some st' ∧ Inv G w K t δ R st' then 1 else 0) + phi G o := by
    intro o
    by_cases hI : ∃ st', o = some st' ∧ Inv G w K t δ R st'
    · obtain ⟨st, rfl, hI⟩ := hI
      simp only [eval_ofDet, termQ_eval, phi]
      by_cases he : resid G st.P = ∅
      · have hgo : Good G w K t δ R st.out := by
          refine ⟨fun x => ?_, hI.hout0, hI.hsupp, hI.hsize, fun e he => (hI.hform e he).2⟩
          have := hI.hen x
          rwa [Er_eq_zero he, add_zero] at this
        have hz : mass (PMF.pure (if resid G st.P = ∅ then some st.out else none))
            (fun o => ¬ ∃ out, o = some out ∧ Good G w K t δ R out) = 0 := by
          rw [mass_pure]; simp [he, hgo]
        rw [hz]; exact bot_le
      · have hne : 1 ≤ ((resid G st.P).card : ℝ≥0∞) := by
          exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
        calc _ ≤ 1 := mass_le_one _ _
          _ ≤ _ := hne
          _ ≤ _ := le_add_self
    · simp only [hI, not_false_eq_true, ↓reduceIte]
      exact le_trans (mass_le_one _ _) le_self_add
  calc ∑' o, p o * mass _ _ ≤ ∑' o, p o * ((if ¬ ∃ st', o = some st' ∧ Inv G w K t δ R st'
          then 1 else 0) + phi G o) :=
        ENNReal.tsum_le_tsum fun o => mul_le_mul_right (hpt o) _
    _ = mass p (fun o => ¬ ∃ st', o = some st' ∧ Inv G w K t δ R st') + expect p (phi G) := by
        rw [mass_eq_tsum, Probability.expect, ← ENNReal.tsum_add]
        congr 1; funext o
        split_ifs <;> simp [mul_add]
    _ ≤ _ := add_le_add hgood hexp

end

end Sparsify
end CutQueryComplexity
