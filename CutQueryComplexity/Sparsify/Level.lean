import CutQueryComplexity.Sparsify.Bundle
import CutQueryComplexity.Probability.FiniteEvents

/-! # One level of the recursion (D4; source recursion steps 1–3, `lem:bernstein`)

Vertices are `Fin n`, and public pair weights `w ≥ 0`. Pairs are ordered by `keyW`
(length `1/w`, then a fixed index). The state (`LState`) holds the public support predicate `P`
and the stored output weights `out`. The level-`r` Laplacian has conductances `4^r c_e w_e` on
pairs with `P e` (`Er`; non-pairs have `c_e = 0`).

`levelQ`:
1. Build a bundle of `t` capped spanners on `P` (`bundleQ`); a failure aborts.
2. Learn the multiplicities of the selected pairs and store them with weight `c_e 4^r w_e`
   (`multQ`). Stored weights are never rescaled.
3. After the bundle is fixed, draw a fresh quarter mask over the public list of remaining
   eligible pairs (`remF`, `remP`), and keep those pairs for the next level.

`levelQ_fail_le` (from `Inv r`): with probability at least `1 − t 2^{-J} − 2n exp(−δ² t/(8 C α))`
the level returns a state satisfying `Inv (r + 1)`. The energy part of the invariant is
`(1−δ)^r xᵀLx ≤ E_out(x) + E_r(x) ≤ (1+δ)^r xᵀLx`.

`levelQ_expect`: the expected number of actual residual pairs drops by a factor of four.
-/

namespace CutQueryComplexity
namespace Sparsify

open Finset Probability Spanner Spectral
open scoped ENNReal

noncomputable section

attribute [local instance 10] Classical.propDecidable

variable {n : ℕ}

/-! ## Keys from public weights -/

/-- A fixed injective index of pairs. -/
def pidx (e : Sym2 (Fin n)) : ℕ := (Fintype.equivFin (Sym2 (Fin n)) e).val

theorem pidx_injective : Function.Injective (pidx (n := n)) := fun _ _ h =>
  (Fintype.equivFin (Sym2 (Fin n))).injective (Fin.ext h)

/-- The key: length `1/w`, then the index. -/
def keyW (w : Sym2 (Fin n) → ℝ) (e : Sym2 (Fin n)) : Lex (ℝ × ℕ) := toLex (1 / w e, pidx e)

theorem keyW_injective (w : Sym2 (Fin n) → ℝ) : Function.Injective (keyW w) := fun e f h => by
  have := congrArg (fun z => (ofLex z).2) h
  exact pidx_injective this

theorem keyW_mono (w : Sym2 (Fin n) → ℝ) (e f : Sym2 (Fin n)) (h : keyW w f ≤ keyW w e) :
    1 / w f ≤ 1 / w e := by
  rcases (Prod.Lex.le_iff).mp h with h | ⟨h, -⟩
  · exact h.le
  · exact h.le

/-! ## Energies -/

variable (G : DiGraph (Fin n)) (w : Sym2 (Fin n) → ℝ)

/-- The real multiplicity of a pair. -/
def cR (e : Sym2 (Fin n)) : ℝ := symS G e

/-- The conductance at level `r`. -/
def omegaR (r : ℕ) (e : Sym2 (Fin n)) : ℝ := (4 : ℝ) ^ r * cR G e * w e

/-- The level-`r` residual energy on the public support `P`. -/
def Er (P : Sym2 (Fin n) → Bool) (r : ℕ) (x : Fin n → ℝ) : ℝ :=
  energy (omegaR G w r) (univ.filter fun e => P e = true) x

/-- The stored output energy. -/
def Eo (out : Sym2 (Fin n) → ℝ) (x : Fin n → ℝ) : ℝ := ∑ e, out e * pairSq x e

/-- The initial predicate: positive public weight. -/
def P0 (w : Sym2 (Fin n) → ℝ) (e : Sym2 (Fin n)) : Bool := decide (0 < w e)

/-- The target energy `xᵀ L x`, `L = Σ_e c_e w_e a_e a_eᵀ`. -/
def E0 (x : Fin n → ℝ) : ℝ := Er G w (P0 w) 0 x

/-- The recursion state. -/
structure LState (n : ℕ) where
  P : Sym2 (Fin n) → Bool
  out : Sym2 (Fin n) → ℝ

/-- The remaining public candidates after deleting the bundle. -/
def remF (P : Sym2 (Fin n) → Bool) (B : Finset (Sym2 (Fin n))) : Finset (Sym2 (Fin n)) :=
  univ.filter fun e => P e = true ∧ e ∉ B

/-- Their public enumeration. -/
def remP (P : Sym2 (Fin n) → Bool) (B : Finset (Sym2 (Fin n))) :
    Fin (remF P B).card → Sym2 (Fin n) := fun i => ((remF P B).equivFin.symm i).val

theorem remP_injective (P : Sym2 (Fin n) → Bool) (B : Finset (Sym2 (Fin n))) :
    Function.Injective (remP P B) := fun _ _ h =>
  (remF P B).equivFin.symm.injective (Subtype.ext h)

theorem remP_mem (P : Sym2 (Fin n) → Bool) (B : Finset (Sym2 (Fin n))) (i) :
    remP P B i ∈ remF P B := ((remF P B).equivFin.symm i).property

/-- The next state from the bundle `B`, multiplicities `m`, and mask `ξ`. -/
def nextSt (r : ℕ) (st : LState n) (B : Finset (Sym2 (Fin n))) (m : Sym2 (Fin n) → ℕ)
    (ξ : Fin (remF st.P B).card → Bool) : LState n where
  P e := decide (∃ i, remP st.P B i = e ∧ ξ i = true)
  out e := st.out e + if e ∈ B then (m e : ℝ) * (4 : ℝ) ^ r * w e else 0

variable (K J t : ℕ)

/-- The query budget of one level. -/
abbrev levelBudget : ℕ := t * (J * capQ (Fin n) K K) + 3 * (t * capH (Fin n) K)

/-- **One level.** -/
def levelQ (r : ℕ) (st : LState n) :
    RTree (Finset (Fin n)) ℕ (Option (LState n)) (levelBudget (n := n) K J t) :=
  (bundleQ (keyW w) K K J st.P t).bind fun o => match o with
  | none => RTree.pure (PMF.pure none)
  | some L => ((RTree.ofDeterministic (multQ (t * capH (Fin n) K) (bunion L))).bind fun m =>
      RTree.pure (q := 0) ((maskPMF (remF st.P (bunion L)).card).map fun ξ =>
        some (nextSt w r st (bunion L) m ξ))).cast (by ring)

/-! ## The level invariant -/

/-- The invariant after `r` levels. -/
structure Inv (δ : ℝ) (r : ℕ) (st : LState n) : Prop where
  hP : ∀ e, st.P e = true → 0 < w e
  hout0 : ∀ e, 0 ≤ st.out e
  hsupp : ∀ e, st.out e ≠ 0 → 0 < symS G e ∧ 0 < w e
  hsize : (univ.filter fun e => st.out e ≠ 0).card ≤ r * (t * capH (Fin n) K)
  hform : ∀ e, st.out e ≠ 0 → st.P e = false ∧
    ∃ r' < r, st.out e = (symS G e : ℝ) * (4 : ℝ) ^ r' * w e
  hen : ∀ x, (1 - δ) ^ r * E0 G w x ≤ Eo st.out x + Er G w st.P r x ∧
    Eo st.out x + Er G w st.P r x ≤ (1 + δ) ^ r * E0 G w x

/-- The structural part of the invariant; it holds after every mask. -/
structure SInv (r : ℕ) (st : LState n) : Prop where
  hP : ∀ e, st.P e = true → 0 < w e
  hout0 : ∀ e, 0 ≤ st.out e
  hsupp : ∀ e, st.out e ≠ 0 → 0 < symS G e ∧ 0 < w e
  hsize : (univ.filter fun e => st.out e ≠ 0).card ≤ r * (t * capH (Fin n) K)
  hform : ∀ e, st.out e ≠ 0 → st.P e = false ∧
    ∃ r' < r, st.out e = (symS G e : ℝ) * (4 : ℝ) ^ r' * w e

variable {G w K J t}

theorem Inv.toSInv {δ : ℝ} {r : ℕ} {st : LState n} (hI : Inv G w K t δ r st) :
    SInv G w K t r st := ⟨hI.hP, hI.hout0, hI.hsupp, hI.hsize, hI.hform⟩

theorem omegaR_nonneg (hw0 : ∀ e, 0 ≤ w e) (r : ℕ) (e : Sym2 (Fin n)) : 0 ≤ omegaR G w r e := by
  unfold omegaR cR; have := hw0 e; positivity

theorem Eo_nonneg {out : Sym2 (Fin n) → ℝ} (h : ∀ e, 0 ≤ out e) (x : Fin n → ℝ) :
    0 ≤ Eo out x := sum_nonneg fun e _ => mul_nonneg (h e) (pairSq_nonneg x e)

theorem not_diag_of_pos {e : Sym2 (Fin n)} (h : 0 < symS G e) : ¬ e.IsDiag := by
  induction e using Sym2.ind with
  | h u v =>
      intro hd
      rw [Sym2.mk_isDiag_iff] at hd
      subst hd; simp at h

/-- Energies over the public support agree with those over the actual support. -/
theorem energy_support (r : ℕ) (P : Sym2 (Fin n) → Bool) (x : Fin n → ℝ) :
    energy (fun f => (4 : ℝ) ^ r * cR G f * w f) (support G P) x = Er G w P r x := by
  unfold Er energy omegaR
  refine sum_subset (fun e he => by simp [support] at he ⊢; exact he.2) fun e he hns => ?_
  have : symS G e = 0 := by
    by_contra h
    exact hns (by simp [support] at he ⊢; exact ⟨Nat.pos_of_ne_zero h, he⟩)
  simp [cR, this]

theorem card_bunion_le {ℓ : Sym2 (Fin n) → ℝ} {α cap : ℕ} {E : Finset (Sym2 (Fin n))} :
    ∀ {L : List (Finset (Sym2 (Fin n)))}, ValidBundle ℓ α cap E L →
      (bunion L).card ≤ L.length * cap
  | [], _ => by simp
  | H :: L, ⟨hL, _, hcard, _⟩ => by
      simp only [bunion_cons, List.length_cons]
      refine (card_union_le _ _).trans ?_
      have := card_bunion_le hL
      nlinarith

theorem bunion_subset {ℓ : Sym2 (Fin n) → ℝ} {α cap : ℕ} {E : Finset (Sym2 (Fin n))}
    {L : List (Finset (Sym2 (Fin n)))} (hL : ValidBundle ℓ α cap E L) : bunion L ⊆ E :=
  fun e he => by
    obtain ⟨H, hH, he⟩ := mem_bunion.mp he
    exact ValidBundle.subset hL H hH he

/-- The mask keeps a given remaining pair with probability `1/4`. -/
theorem mass_mask_true {N : ℕ} (i : Fin N) :
    mass (maskPMF N) (fun ξ => ξ i = true) = 1 / 4 := by
  rw [mass, ← PMF.toMeasure_apply_eq_toOuterMeasure, maskPMF_toMeasure, maskMeasure]
  have hmp := MeasureTheory.measurePreserving_eval (fun _ : Fin N => quarter.toMeasure) i
  have : {ξ : Fin N → Bool | ξ i = true} = (Function.eval i : (Fin N → Bool) → Bool) ⁻¹'
      ({true} : Set Bool) := rfl
  rw [this, hmp.measure_preimage (MeasurableSet.singleton true).nullMeasurableSet,
    PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton true)]
  simp [quarter]

theorem image_remP (P : Sym2 (Fin n) → Bool) (B : Finset (Sym2 (Fin n))) :
    univ.image (remP P B) = remF P B := by
  ext e
  constructor
  · rintro hm
    obtain ⟨i, -, rfl⟩ := mem_image.mp hm
    exact remP_mem P B i
  · intro he
    exact mem_image.mpr ⟨(remF P B).equivFin ⟨e, he⟩, mem_univ _, by simp [remP]⟩

theorem eval_ofDet {I A O : Type} {q : ℕ} (T : DTree I A O q) (read : I → A) :
    (RTree.ofDeterministic T).eval read = PMF.pure (T.eval read) := by
  rw [RTree.eval, RTree.run_ofDeterministic, PMF.pure_map]; rfl

/-- **Energy bookkeeping across one level.** -/
theorem next_energy {r : ℕ} {st : LState n} {B : Finset (Sym2 (Fin n))}
    (hB : B ⊆ univ.filter fun e => st.P e = true) {m : Sym2 (Fin n) → ℕ}
    (hm : ∀ e ∈ B, m e = symS G e) (ξ : Fin (remF st.P B).card → Bool) (x : Fin n → ℝ) :
    Eo (nextSt w r st B m ξ).out x + Er G w (nextSt w r st B m ξ).P (r + 1) x =
      Eo st.out x + sampledEnergy (omegaR G w r) (univ.filter fun e => st.P e = true)
        (remP st.P B) ξ x := by
  -- the stored part
  have h1 : Eo (nextSt w r st B m ξ).out x = Eo st.out x + ∑ e ∈ B, omegaR G w r e * pairSq x e := by
    simp only [Eo, nextSt, add_mul, sum_add_distrib, ite_mul, zero_mul]
    rw [← sum_filter]
    congr 1
    refine sum_congr (by ext e; simp) fun e he => ?_
    rw [hm e (by simpa using he)]
    simp only [omegaR, cR]; ring
  -- the bundle part of the sampled energy
  have h2 : (univ.filter fun e => st.P e = true) \ univ.image (remP st.P B) = B := by
    rw [image_remP]
    ext e
    simp only [remF, mem_sdiff, mem_filter, mem_univ, true_and, not_and, not_not]
    constructor
    · rintro ⟨hP, h⟩; exact h hP
    · intro he; exact ⟨by simpa using hB he, fun _ => he⟩
  -- the sampled part
  have h3 : Er G w (nextSt w r st B m ξ).P (r + 1) x =
      ∑ i, (if ξ i then 4 else 0) * (omegaR G w r (remP st.P B i) * pairSq x (remP st.P B i)) := by
    have hfil : (univ.filter fun e => (nextSt w r st B m ξ).P e = true) =
        (univ.filter fun i => ξ i = true).image (remP st.P B) := by
      ext e
      simp only [nextSt, decide_eq_true_eq, mem_filter, mem_univ, true_and, mem_image]
      constructor <;> rintro ⟨i, h1, h2⟩ <;> exact ⟨i, h2, h1⟩
    unfold Er energy
    rw [hfil, sum_image fun i _ j _ h => remP_injective st.P B h, sum_filter]
    refine sum_congr rfl fun i _ => ?_
    split_ifs
    · simp only [omegaR, pow_succ]; ring
    · simp
  rw [h1, h3, sampledEnergy, h2, energy]
  ring

/-- **The bundle bound for every remaining candidate.** -/
theorem lev_bound {C : ℝ} (hC : ∀ e, (symS G e : ℝ) ≤ C) (hw0 : ∀ e, 0 ≤ w e) {r : ℕ}
    {st : LState n} (hP : ∀ e, st.P e = true → 0 < w e) {L : List (Finset (Sym2 (Fin n)))}
    (hL : ValidBundle (fun e => 1 / w e) (2 * K + 1) (capH (Fin n) K) (support G st.P) L)
    (hlen : L.length = t) (ht : 0 < t) (i : Fin (remF st.P (bunion L)).card) (y : Fin n → ℝ) :
    omegaR G w r (remP st.P (bunion L) i) * pairSq y (remP st.P (bunion L) i) ≤
      C * (2 * K + 1 : ℕ) / t * energy (omegaR G w r) (univ.filter fun e => st.P e = true) y := by
  have hE := energy_nonneg (omegaR_nonneg (G := G) hw0 r) (univ.filter fun e => st.P e = true) y
  have hC0 : 0 ≤ C := (Nat.cast_nonneg _).trans (hC (remP st.P (bunion L) i))
  have hlam : 0 ≤ C * (2 * K + 1 : ℕ) / t := by positivity
  have hmem := remP_mem st.P (bunion L) i
  simp only [remF, mem_filter, mem_univ, true_and] at hmem
  by_cases hact : 0 < symS G (remP st.P (bunion L) i)
  · -- an actual remaining pair: bundle domination
    have he : remP st.P (bunion L) i ∈ support G st.P \ bunion L := by
      simp [support, hact, hmem.1, hmem.2]
    generalize hge : remP st.P (bunion L) i = e at he hmem hact ⊢
    induction e using Sym2.ind with
    | h u v =>
        have := ValidBundle.dominated hL (by omega) (by positivity : (0 : ℝ) < 4 ^ r)
          (w := w) (c := cR G) (fun f hf => hP f (by simp [support] at hf; exact hf.2))
          (fun f hf => by
            simp only [support, mem_filter, mem_univ, true_and] at hf
            simp only [cR]; exact_mod_cast hf.1) rfl he (hC _) y
        rw [hlen, energy_support] at this
        simp only [omegaR]
        rw [show (Er G w st.P r y) = energy (omegaR G w r) (univ.filter fun e => st.P e = true) y
          from rfl] at this
        linarith
  · have : symS G (remP st.P (bunion L) i) = 0 := Nat.eq_zero_of_not_pos hact
    simp only [omegaR, cR, this, Nat.cast_zero, mul_zero, zero_mul]
    exact mul_nonneg hlam hE

/-- **The structural invariant holds after every mask.** -/
theorem sinv_next (hw0 : ∀ e, 0 ≤ w e) {r : ℕ}
    {st : LState n} (hI : SInv G w K t r st) {L : List (Finset (Sym2 (Fin n)))}
    (hL : ValidBundle (fun e => 1 / w e) (2 * K + 1) (capH (Fin n) K) (support G st.P) L)
    (hlen : L.length = t) {m : Sym2 (Fin n) → ℕ} (hm : ∀ e ∈ bunion L, m e = symS G e)
    (ξ : Fin (remF st.P (bunion L)).card → Bool) :
    SInv G w K t (r + 1) (nextSt w r st (bunion L) m ξ) := by
  have hBsupp := bunion_subset hL
  have hBP : bunion L ⊆ univ.filter fun e => st.P e = true := fun e he => by
    have := hBsupp he; simp [support] at this ⊢; exact this.2
  have hBcard := card_bunion_le hL
  rw [hlen] at hBcard
  refine ⟨fun e he => ?_, fun e => ?_, fun e he => ?_, ?_, fun e he => ?_⟩
  · simp only [nextSt, decide_eq_true_eq] at he
    obtain ⟨i, rfl, -⟩ := he
    have := remP_mem st.P (bunion L) i
    simp only [remF, mem_filter, mem_univ, true_and] at this
    exact hI.hP _ this.1
  · simp only [nextSt]
    have := hI.hout0 e; have := hw0 e
    split_ifs <;> positivity
  · simp only [nextSt] at he
    by_cases ho : st.out e = 0
    · rw [ho, zero_add] at he
      split_ifs at he with hB
      · have := hBsupp hB
        simp only [support, mem_filter, mem_univ, true_and] at this
        exact ⟨this.1, hI.hP e this.2⟩
      · exact absurd rfl he
    · exact hI.hsupp e ho
  · calc (univ.filter fun e => (nextSt w r st (bunion L) m ξ).out e ≠ 0).card
        ≤ ((univ.filter fun e => st.out e ≠ 0) ∪ bunion L).card := by
          refine card_le_card fun e he => ?_
          have he' := (mem_filter.mp he).2
          simp only [nextSt] at he'
          simp only [mem_union, mem_filter, mem_univ, true_and]
          by_contra h
          push Not at h
          apply he'; rw [h.1, ite_eq_right_iff.mpr (fun hh => absurd hh h.2)]; simp
      _ ≤ r * (t * capH (Fin n) K) + t * capH (Fin n) K :=
          (card_union_le _ _).trans (add_le_add hI.hsize hBcard)
      _ = (r + 1) * (t * capH (Fin n) K) := by ring
  · -- each stored weight is `c_e 4^{r'} w_e`, stored once
    have hP'false : ∀ f, st.P f = false → (nextSt w r st (bunion L) m ξ).P f = false := by
      intro f hf
      simp only [nextSt, decide_eq_false_iff_not, not_exists, not_and]
      intro i hi
      have := remP_mem st.P (bunion L) i
      rw [hi] at this
      simp only [remF, mem_filter, mem_univ, true_and] at this
      rw [hf] at this; exact absurd this.1 (by simp)
    simp only [nextSt] at he ⊢
    by_cases hB : e ∈ bunion L
    · have hPe : st.P e = true := by have := hBP hB; simpa using this
      have hout : st.out e = 0 := by
        by_contra ho; rw [(hI.hform e ho).1] at hPe; exact absurd hPe (by simp)
      refine ⟨?_, r, Nat.lt_succ_self r, ?_⟩
      · simp only [decide_eq_false_iff_not, not_exists, not_and]
        intro i hi
        have := remP_mem st.P (bunion L) i
        rw [hi] at this
        simp only [remF, mem_filter, mem_univ, true_and] at this
        exact (this.2 hB).elim
      · simp only [hout, zero_add, hB, ↓reduceIte, hm e hB]
    · simp only [hB, ↓reduceIte, add_zero] at he ⊢
      obtain ⟨hPf, r', hr', hval⟩ := hI.hform e he
      refine ⟨?_, r', Nat.lt_succ_of_lt hr', hval⟩
      have := hP'false e hPf
      simpa [nextSt] using this

/-- One level preserves the invariant on the good mask event. -/
theorem inv_next (hw0 : ∀ e, 0 ≤ w e) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {r : ℕ}
    {st : LState n} (hI : Inv G w K t δ r st) {L : List (Finset (Sym2 (Fin n)))}
    (hL : ValidBundle (fun e => 1 / w e) (2 * K + 1) (capH (Fin n) K) (support G st.P) L)
    (hlen : L.length = t) {m : Sym2 (Fin n) → ℕ} (hm : ∀ e ∈ bunion L, m e = symS G e)
    (ξ : Fin (remF st.P (bunion L)).card → Bool)
    (hξ : ∀ x, |sampledEnergy (omegaR G w r) (univ.filter fun e => st.P e = true)
      (remP st.P (bunion L)) ξ x - energy (omegaR G w r) (univ.filter fun e => st.P e = true) x| ≤
      δ * energy (omegaR G w r) (univ.filter fun e => st.P e = true) x) :
    Inv G w K t δ (r + 1) (nextSt w r st (bunion L) m ξ) := by
  have hBsupp := bunion_subset hL
  have hBP : bunion L ⊆ univ.filter fun e => st.P e = true := fun e he => by
    have := hBsupp he; simp [support] at this ⊢; exact this.2
  obtain ⟨h1, h2, h3, h4, h5⟩ := sinv_next hw0 hI.toSInv hL hlen hm ξ
  refine ⟨h1, h2, h3, h4, h5, fun x => ?_⟩
  · have hnext := next_energy (G := G) (w := w) (r := r) hBP hm ξ x
    have hErdef : energy (omegaR G w r) (univ.filter fun e => st.P e = true) x = Er G w st.P r x := rfl
    have hgood := hξ x
    rw [hErdef, abs_le] at hgood
    have hEo := Eo_nonneg hI.hout0 x
    have hEr : 0 ≤ Er G w st.P r x := energy_nonneg (omegaR_nonneg hw0 r) _ x
    obtain ⟨hlo, hhi⟩ := hI.hen x
    have h1δ : 0 ≤ 1 - δ := by linarith
    constructor
    · rw [hnext, pow_succ]
      calc (1 - δ) ^ r * (1 - δ) * E0 G w x = (1 - δ) * ((1 - δ) ^ r * E0 G w x) := by ring
        _ ≤ (1 - δ) * (Eo st.out x + Er G w st.P r x) := mul_le_mul_of_nonneg_left hlo h1δ
        _ ≤ _ := by nlinarith
    · rw [hnext, pow_succ]
      calc Eo st.out x + sampledEnergy (omegaR G w r) (univ.filter fun e => st.P e = true)
            (remP st.P (bunion L)) ξ x ≤ (1 + δ) * (Eo st.out x + Er G w st.P r x) := by nlinarith
        _ ≤ (1 + δ) * ((1 + δ) ^ r * E0 G w x) := mul_le_mul_of_nonneg_left hhi (by linarith)
        _ = _ := by ring

/-- **One level succeeds** with probability at least
`1 − t 2^{-J} − 2n exp(−δ² t / (8 C (2K + 1)))`. -/
theorem levelQ_good {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ e, (symS G e : ℝ) ≤ C) (hw0 : ∀ e, 0 ≤ w e)
    (hK : n ≤ 2 ^ K) (ht : 0 < t) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {r : ℕ} {st : LState n}
    (hI : Inv G w K t δ r st) :
    mass ((levelQ w K J t r st).eval G.out)
        (fun o => ¬ ∃ st', o = some st' ∧ Inv G w K t δ (r + 1) st') ≤
      t * (2⁻¹ : ℝ≥0∞) ^ J +
        ENNReal.ofReal (2 * n * Real.exp (-(δ ^ 2) / (8 * (C * (2 * K + 1 : ℕ) / t)))) := by
  have hK' : Fintype.card (Fin n) ≤ 2 ^ K := by simpa using hK
  have hinj := keyW_injective w
  have hmono : ∀ e f, keyW w f ≤ keyW w e → 1 / w f ≤ 1 / w e := fun e f h => keyW_mono w e f h
  have hℓ : ∀ e, 0 ≤ 1 / w e := fun e => one_div_nonneg.mpr (hw0 e)
  unfold levelQ
  rw [RTree.eval_bind]
  refine mass_bind_le_add _ _
    (fun o => ¬ ∃ L, o = some L ∧ L.length = t ∧
      ValidBundle (fun e => 1 / w e) (2 * K + 1) (capH (Fin n) K) (support G st.P) L)
    _ ?_ ?_
  · -- bundle failure
    refine le_trans (mass_mono_on_support _ fun o ho hbad => ?_)
      (bundleQ_fail_le hinj G hK' hK' st.P t)
    cases o with
    | none => rfl
    | some L =>
        exact absurd ⟨L, rfl, bundleQ_valid hinj hmono hℓ G hK' hK' st.P t L ho⟩ hbad
  · intro o hgood
    push Not at hgood
    obtain ⟨L, rfl, hlen, hL⟩ := hgood
    simp only [RTree.eval_cast, RTree.eval_bind, eval_ofDet, PMF.pure_bind, RTree.eval_pure,
      mass_map]
    set B := bunion L
    have hBcard := card_bunion_le hL
    rw [hlen] at hBcard
    have hm : ∀ e ∈ B, (multQ (t * capH (Fin n) K) B).eval G.out e = symS G e := fun e he =>
      multQ_correct G hBcard (fun f hf => not_diag_of_pos (by
        have := bunion_subset hL hf; simp [support] at this; exact this.1)) he
    have hround := Spectral.one_round (omegaR_nonneg (G := G) hw0 r)
      (remP_injective st.P B) (fun i => by
        have := remP_mem st.P B i; simp [remF] at this ⊢; exact this.1)
      (by positivity)
      (lev_bound hC hw0 hI.hP hL hlen ht) hδ hδ1
    refine le_trans (mass_mono _ fun ξ hξ => ?_)
      ((ENNReal.le_ofReal_iff_toReal_le (mass_ne_top _ _) (by positivity)).mpr hround)
    intro hgoodξ
    exact hξ ⟨_, rfl, inv_next hw0 hδ hδ1 hI hL hlen hm ξ hgoodξ⟩

/-! ## Surviving pairs -/

variable (G)

/-- The number of actual residual pairs. -/
def resid (P : Sym2 (Fin n) → Bool) : Finset (Sym2 (Fin n)) :=
  univ.filter fun e => P e = true ∧ 0 < symS G e

/-- The potential of an optional state; an aborted run has none. -/
def phi : Option (LState n) → ℝ≥0∞
  | none => 0
  | some st => (resid G st.P).card

variable {G}

/-- **The expected number of residual pairs drops by a factor of four**, whatever the bundle. -/
theorem levelQ_expect (r : ℕ) (st : LState n) :
    expect ((levelQ w K J t r st).eval G.out) (phi G) ≤ (resid G st.P).card * 4⁻¹ := by
  unfold levelQ
  rw [RTree.eval_bind, expect_bind]
  refine expect_le_of_le_on_support _ fun o _ => ?_
  cases o with
  | none => simp [phi]
  | some L =>
      simp only [RTree.eval_cast, RTree.eval_bind, eval_ofDet, PMF.pure_bind, RTree.eval_pure,
        expect_map]
      set B := bunion L
      set A : Finset (Fin (remF st.P B).card) := univ.filter fun i => 0 < symS G (remP st.P B i)
      have hcount : ∀ ξ : Fin (remF st.P B).card → Bool,
          phi G (some (nextSt w r st B ((multQ (t * capH (Fin n) K) B).eval G.out) ξ)) =
            ((A.filter fun i => ξ i = true).card : ℝ≥0∞) := by
        intro ξ
        simp only [phi]
        congr 1
        have : resid G (nextSt w r st B ((multQ (t * capH (Fin n) K) B).eval G.out) ξ).P =
            (A.filter fun i => ξ i = true).image (remP st.P B) := by
          ext e
          simp only [resid, nextSt, decide_eq_true_eq, mem_filter, mem_univ, true_and, mem_image,
            A]
          constructor
          · rintro ⟨⟨i, rfl, hi⟩, hpos⟩; exact ⟨i, ⟨hpos, hi⟩, rfl⟩
          · rintro ⟨i, ⟨hpos, hi⟩, rfl⟩; exact ⟨⟨i, rfl, hi⟩, hpos⟩
        rw [this, card_image_of_injective _ (remP_injective st.P B)]
      simp only [hcount]
      rw [expect_card_filter (maskPMF (remF st.P B).card) A (fun ξ i => ξ i = true)]
      simp only [mass_mask_true]
      rw [sum_const, nsmul_eq_mul]
      have hA : A.card ≤ (resid G st.P).card := by
        rw [← card_image_of_injective A (remP_injective st.P B)]
        refine card_le_card fun e he => ?_
        obtain ⟨i, hi, rfl⟩ := mem_image.mp he
        have := remP_mem st.P B i
        simp only [remF, mem_filter, mem_univ, true_and, A] at this hi
        exact mem_filter.mpr ⟨mem_univ _, this.1, (mem_filter.mp hi).2⟩
      rw [one_div]
      exact mul_le_mul_left (by exact_mod_cast hA) _

end

end Sparsify
end CutQueryComplexity
