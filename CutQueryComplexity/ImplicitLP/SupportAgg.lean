import CutQueryComplexity.ImplicitLP.SupportMain
import CutQueryComplexity.ImplicitLP.Aggregate
import Mathlib.Algebra.BigOperators.Sym

/-! # The support oracle from certified hidden aggregates (`lem:support`, D7 item 6)

**Hidden sums.** The `M` LP coordinates are hidden copies of canonical pairs plus explicit
coordinates (`hid : Fin M → Option (Sym2 (Fin n))`, `symS G e` copies of `e`, as in
`gram_split`). A coordinate formula constant on copies splits as an explicit sum plus a pair
aggregate (`hidden_sum_split`), and the rounded pair aggregate `hiddenSumProg` gives the sum to
within `M · 2^{−p}` in `6Bn` queries (`hiddenSumProg_err`).

**Inexact fixed-`τ` evaluator.** Only approximate values `Ñ(λ)` of `‖z(λ)‖₂²` and `P̃(λ)` of
`aᵀz(λ)` are available (errors `δ`, `δ_P`). Test `Ñ(0) ≤ r²`, else bisect `[0, Λ]` on the test
`Ñ(λ) ≤ r²` (`ibisect`), rescale `z(λ̂)` conservatively by `c = min{1, r/√(Ñ + δ)}` and output the
interval `ℓ = cP̃ − cδ_P − ρc²(Ñ + δ)`, `u = P̃ + δ_P − (ρ+λ̂)(Ñ − δ) + λ̂r²`. Then
`ℓ ≤ f_ρ(ẑ) ≤ G_ρ(τ) ≤ u` and
`u − ℓ ≤ Λ²‖a‖₂/(ρ²2ⁿ) + (3Λ + 4ρ + ‖a‖₂/(2r₀))δ + 4δ_P` (`ievaluator`).

**Support oracle.** `support_of_eval` is `support_main` for any certified evaluator; with the
inexact evaluator (`support_inexact`) and with the hidden aggregates (`support_hidden`) the loss is
`ρ + Lh + 3ε_agg + L(1 − 2h)(2/3)ᴺ`.

**Program.** `ievalProg` (`k + 3` sum programs), `trisectProg` (`1 + 2N` evaluations, tracking
the incumbent's point) and `supportProg` are `DTree`s; `supportProg_hidden` gives the support
guarantee for the program's output and the cap `(2N + 2)(m + 3) · 6Bn` outgoing-cut queries.
Offline real arithmetic (comparisons, `√`, explicit sums) is free, as in `frozenSolveProg`.
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Finset Real Set

noncomputable section

/-! ## Hidden sums -/

section HiddenSum

variable {M n : ℕ}

/-- `symS`-weighted sums over unordered pairs are sums over canonical pairs `u < v`. -/
theorem sum_symS_eq_pairs (G : DiGraph (Fin n)) (f : Sym2 (Fin n) → ℝ) :
    ∑ e, (Spanner.symS G e : ℝ) * f e =
      ∑ u, ∑ v ∈ univ.filter (u < ·), (G.sym u v : ℝ) * f s(u, v) := by
  rw [← Finset.sym2_univ, ← sum_filter_add_sum_filter_not _ (fun e : Sym2 (Fin n) => e.IsDiag)]
  have hdiag : ∑ e ∈ (univ : Finset (Fin n)).sym2 with e.IsDiag,
      (Spanner.symS G e : ℝ) * f e = 0 := by
    refine sum_eq_zero fun e he => ?_
    have hd := (mem_filter.mp he).2
    induction e using Sym2.ind with
    | h a b =>
        rw [Sym2.mk_isDiag_iff] at hd
        subst hd
        simp
  rw [hdiag, zero_add, sum_sym2_filter_not_isDiag]
  rw [show (univ : Finset (Fin n)).offDiag.filter (fun i => i.1 < i.2) =
      ((Finset.univ : Finset (Fin n)) ×ˢ (Finset.univ : Finset (Fin n))).filter (fun i : Fin n × Fin n => i.1 < i.2) by
    ext ⟨a, b⟩; simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, Finset.mem_product, true_and]
    exact ⟨fun h => h.2, fun h => ⟨ne_of_lt h, h⟩⟩]
  rw [sum_filter, sum_product]
  refine sum_congr rfl fun u _ => ?_
  rw [sum_filter]
  rfl

/-- **Hidden-sum split.** If `ψ` is constant on the copies of each pair, its coordinate sum is
the explicit part plus the canonical pair sum `Σ_{u<v} sym(u,v) ψ̄(uv)`. -/
theorem hidden_sum_split (hid : Fin M → Option (Sym2 (Fin n))) (G : DiGraph (Fin n))
    (hcount : ∀ e, (univ.filter fun i => hid i = some e).card = Spanner.symS G e)
    {ψ : Fin M → ℝ} {ψb : Sym2 (Fin n) → ℝ} (hψ : ∀ i e, hid i = some e → ψ i = ψb e) :
    ∑ i, ψ i = ∑ i ∈ univ.filter (fun i => hid i = none), ψ i +
      ∑ u, ∑ v ∈ univ.filter (u < ·), (G.sym u v : ℝ) * ψb s(u, v) := by
  rw [← sum_fiberwise_of_maps_to (g := hid) (t := univ) (fun _ _ => mem_univ _),
    Fintype.sum_option, ← sum_symS_eq_pairs]
  congr 1
  refine sum_congr rfl fun e _ => ?_
  rw [← hcount e, ← nsmul_eq_mul, ← sum_const]
  exact sum_congr rfl fun i hi => hψ i e (mem_filter.mp hi).2

/-- The total pair multiplicity is the number of hidden coordinates, so at most `M`. -/
theorem pairMult_le (hid : Fin M → Option (Sym2 (Fin n))) (G : DiGraph (Fin n))
    (hcount : ∀ e, (univ.filter fun i => hid i = some e).card = Spanner.symS G e) :
    (∑ u, ∑ v ∈ univ.filter (u < ·), (G.sym u v : ℝ)) ≤ M := by
  have h := hidden_sum_split (ψ := fun _ => (1 : ℝ)) (ψb := fun _ => 1) hid G hcount
    (fun _ _ _ => rfl)
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  have h0 : (0 : ℝ) ≤ ((univ.filter fun i => hid i = none).card : ℝ) := Nat.cast_nonneg _
  linarith

theorem roundFormula_pos_length (φ : Fin n → Fin n → ℝ) (p B : ℕ) :
    (roundFormula φ p B).pos.length = B := by
  simp [roundFormula, intFormula]

/-- **The hidden-sum program**: the explicit part `X` (computed offline) plus the rounded pair
aggregate of `ψ̄`, in `6Bn` outgoing-cut queries. -/
def hiddenSumProg (X : ℝ) (ψb : Sym2 (Fin n) → ℝ) (p B : ℕ) :
    DTree (Finset (Fin n)) ℕ ℝ (6 * B * n) :=
  ((pairAgg (roundFormula (fun u v => ψb s(u, v)) p B)).map (X + ·)).cast
    (by rw [roundFormula_pos_length, Fintype.card_fin])

/-- **Certified hidden sum.** With `X` the explicit part and `B` magnitude bits for the rounded
pair values, the program is within `M · 2^{−p}` of `Σᵢ ψᵢ`. -/
theorem hiddenSumProg_err (hid : Fin M → Option (Sym2 (Fin n))) (G : DiGraph (Fin n))
    (hcount : ∀ e, (univ.filter fun i => hid i = some e).card = Spanner.symS G e)
    {ψ : Fin M → ℝ} {ψb : Sym2 (Fin n) → ℝ} (hψ : ∀ i e, hid i = some e → ψ i = ψb e)
    {p B : ℕ} (hB : ∀ u v : Fin n, u < v → (⌊ψb s(u, v) * 2 ^ p⌋).natAbs < 2 ^ B) :
    |(hiddenSumProg (∑ i ∈ univ.filter (fun i => hid i = none), ψ i) ψb p B).eval G.out -
        ∑ i, ψ i| ≤ M / 2 ^ p := by
  rw [hiddenSumProg, DTree.eval_cast, DTree.eval_map, hidden_sum_split hid G hcount hψ,
    add_sub_add_left_eq_sub]
  refine (certPair_err G (φ := fun u v => ψb s(u, v)) hB).trans ?_
  rw [mul_one_div]
  exact div_le_div_of_nonneg_right (pairMult_le hid G hcount) (by positivity)

theorem hiddenSumProg_cost (G : DiGraph (Fin n)) (X : ℝ) (ψb : Sym2 (Fin n) → ℝ) (p B : ℕ) :
    (hiddenSumProg X ψb p B).cost G.out ≤ 6 * B * n :=
  DTree.cost_le _ _

end HiddenSum

/-! ## The inexact fixed-`τ` evaluator -/

section Inexact

variable {M : ℕ} {κ a : Fin M → ℝ} {ρ : ℝ}

/-- Bisection on `λ` driven by approximate squared norms `Ñ`, starting from `[0, Λ]`. -/
def ibisect (Nt : ℝ → ℝ) (r2 Λ : ℝ) : ℕ → ℝ × ℝ
  | 0 => (0, Λ)
  | k + 1 =>
      let p := ibisect Nt r2 Λ k
      if Nt ((p.1 + p.2) / 2) ≤ r2 then (p.1, (p.1 + p.2) / 2) else ((p.1 + p.2) / 2, p.2)

theorem ibisect_inv {Nt : ℝ → ℝ} {r2 Λ : ℝ} (hΛ : 0 ≤ Λ) (h0 : r2 < Nt 0) (hΛr : Nt Λ ≤ r2)
    (k : ℕ) :
    0 ≤ (ibisect Nt r2 Λ k).1 ∧ (ibisect Nt r2 Λ k).1 ≤ (ibisect Nt r2 Λ k).2 ∧
      (ibisect Nt r2 Λ k).2 ≤ Λ ∧
      (ibisect Nt r2 Λ k).2 - (ibisect Nt r2 Λ k).1 = Λ / 2 ^ k ∧
      Nt (ibisect Nt r2 Λ k).2 ≤ r2 ∧ r2 < Nt (ibisect Nt r2 Λ k).1 := by
  induction k with
  | zero => simp [ibisect, hΛ, h0, hΛr]
  | succ k ih =>
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih
      simp only [ibisect]
      split_ifs with hm
      · refine ⟨h1, by linarith, by linarith, ?_, hm, h6⟩
        rw [pow_succ, ← div_div, ← h4]; ring
      · refine ⟨by linarith, by linarith, h3, ?_, h5, lt_of_not_ge hm⟩
        rw [pow_succ, ← div_div, ← h4]; ring

/-- The multiplier: `0` if the test passes at `0`, else the passing end of the bracket. -/
def ilam (Nt : ℝ → ℝ) (r2 Λ : ℝ) (k : ℕ) : ℝ :=
  if Nt 0 ≤ r2 then 0 else (ibisect Nt r2 Λ k).2

/-- The conservative scale `min{1, r/√(Ñ + δ)}`. -/
def iscale (Nh δ r : ℝ) : ℝ := if Real.sqrt (Nh + δ) ≤ r then 1 else r / Real.sqrt (Nh + δ)

/-- The certified lower value `cP̃ − cδ_P − ρc²(Ñ + δ)` of `f_ρ(c z)`. -/
def ilow (Ph Nh δ δP ρ c : ℝ) : ℝ := c * Ph - c * δP - ρ * c ^ 2 * (Nh + δ)

/-- The certified upper value `P̃ + δ_P − (ρ+λ)(Ñ − δ) + λr²` of the dual value `D(λ)`. -/
def iupp (Ph Nh δ δP ρ r lm : ℝ) : ℝ := Ph + δP - (ρ + lm) * (Nh - δ) + lm * r ^ 2

/-- The evaluator's output `(λ̂, c, ℓ, u)` from the approximate sums. -/
def ieval (Nt Pt : ℝ → ℝ) (δ δP ρ r Λ : ℝ) (k : ℕ) : ℝ × ℝ × ℝ × ℝ :=
  let lm := ilam Nt (r ^ 2) Λ k
  let c := iscale (Nt lm) δ r
  (lm, c, ilow (Pt lm) (Nt lm) δ δP ρ c, iupp (Pt lm) (Nt lm) δ δP ρ r lm)

theorem iscale_mem {Nh δ r : ℝ} (hr : 0 ≤ r) : 0 ≤ iscale Nh δ r ∧ iscale Nh δ r ≤ 1 := by
  unfold iscale
  split_ifs with h
  · exact ⟨zero_le_one, le_rfl⟩
  · push Not at h
    have hs : 0 < Real.sqrt (Nh + δ) := lt_of_le_of_lt hr h
    exact ⟨div_nonneg hr hs.le, (div_le_one hs).mpr h.le⟩

/-- **The squared-norm gap at the passing end.** If the failing end `lo` has
`r² − ‖z(lo)‖² < δ`, then `r² − ‖z(hi)‖² ≤ δ + 2(‖a‖₂/(2ρ²))(hi − lo)`. -/
theorem sqgap_le (hκ : ∀ i, 0 < κ i) (hρ : 0 < ρ) {τ lo hi δ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1)
    (hlo : 0 ≤ lo) (hlh : lo ≤ hi) (hδ : 0 ≤ δ)
    (hlo' : (1 - τ) ^ 2 - euc (zlam a κ ρ τ lo) ^ 2 < δ) :
    (1 - τ) ^ 2 - euc (zlam a κ ρ τ hi) ^ 2 ≤ δ + 2 * (euc a / (2 * ρ ^ 2) * (hi - lo)) := by
  set r := 1 - τ
  set el := euc (zlam a κ ρ τ lo)
  set eh := euc (zlam a κ ρ τ hi)
  set d := euc a / (2 * ρ ^ 2) * (hi - lo)
  have hr0 : 0 ≤ r := by simp only [r]; linarith [hτ.2]
  have hr1 : r ≤ 1 := by simp only [r]; linarith [hτ.1]
  have hel0 : 0 ≤ el := euc_nonneg _
  have heh0 : 0 ≤ eh := euc_nonneg _
  have hd0 : 0 ≤ d := mul_nonneg (div_nonneg (euc_nonneg a) (by positivity)) (by linarith)
  have hanti : eh ≤ el := euc_zlam_antitone hκ hτ.1 (by linarith) hlh
  have hd : el - eh ≤ d := by
    have h1 : el - eh ≤ euc (zlam a κ ρ τ lo - zlam a κ ρ τ hi) := by
      have := euc_add_le (zlam a κ ρ τ lo - zlam a κ ρ τ hi) (zlam a κ ρ τ hi)
      rw [sub_add_cancel] at this; simp only [el, eh]; linarith
    have h2 := euc_zlam_sub (a := a) (κ := κ) (τ := τ) hρ hlo (by linarith : 0 ≤ hi)
    rw [abs_of_nonpos (by linarith), neg_sub] at h2
    linarith
  by_cases hpos : r ^ 2 - eh ^ 2 ≤ 0
  · linarith
  push Not at hpos
  have hehr : eh < r := by nlinarith
  by_cases hc : r ≤ el
  · have h1 : r - eh ≤ d := by linarith
    have h2 : (r - eh) * (r + eh) ≤ d * 2 :=
      mul_le_mul h1 (by linarith) (by linarith) hd0
    nlinarith
  · push Not at hc
    have h2 : (el - eh) * (el + eh) ≤ d * 2 :=
      mul_le_mul hd (by linarith) (by linarith) hd0
    nlinarith

/-- **The certified fixed-`τ` evaluator from approximate sums.** Suppose the approximate squared
norms `Ñ(λ)` and objective sums `P̃(λ)` are within `δ` and `δ_P` of `‖z(λ)‖₂²` and `aᵀz(λ)`
for all `λ ≥ 0`, that `r = 1 − τ ≥ r₀ > 0`, and that the start `Λ` passes with margin,
`‖z(Λ)‖₂² + δ ≤ r²`. Then the rescaled output `ẑ = c z(λ̂)` is feasible and sign-aligned, and
`ℓ ≤ f_ρ(ẑ) ≤ G_ρ(τ) ≤ u` with
`u − ℓ ≤ Λ²‖a‖₂/(ρ²2ᵏ) + (3Λ + 4ρ + ‖a‖₂/(2r₀))δ + 4δ_P`. -/
theorem ievaluator (hκ : ∀ i, 0 < κ i) (hρ : 0 < ρ) {τ Λ δ δP r₀ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) 1) (hr₀ : 0 < r₀) (hr₀τ : r₀ ≤ 1 - τ) (hΛ : 0 ≤ Λ) (hδ : 0 ≤ δ)
    (hδP : 0 ≤ δP) {Nt Pt : ℝ → ℝ}
    (hN : ∀ lm, 0 ≤ lm → |Nt lm - euc (zlam a κ ρ τ lm) ^ 2| ≤ δ)
    (hP : ∀ lm, 0 ≤ lm → |Pt lm - a ⬝ᵥ zlam a κ ρ τ lm| ≤ δP)
    (hΛr : euc (zlam a κ ρ τ Λ) ^ 2 + δ ≤ (1 - τ) ^ 2) (k : ℕ) :
    let o := ieval Nt Pt δ δP ρ (1 - τ) Λ k
    let zh := o.2.1 • zlam a κ ρ τ o.1
    0 ≤ o.1 ∧ o.1 ≤ Λ ∧ zh ∈ Fset κ τ ∧ (∀ i, 0 ≤ a i * zh i) ∧ o.2.2.1 ≤ fobj a ρ zh ∧
      o.2.2.1 ≤ Gval a κ ρ τ ∧ Gval a κ ρ τ ≤ o.2.2.2 ∧
      o.2.2.2 - o.2.2.1 ≤
        Λ ^ 2 * euc a / (ρ ^ 2 * 2 ^ k) + (3 * Λ + 4 * ρ + euc a / (2 * r₀)) * δ + 4 * δP := by
  intro o zh
  set r := 1 - τ with hr
  have hr0 : 0 < r := by linarith
  set E := Λ ^ 2 * euc a / (ρ ^ 2 * 2 ^ k) with hEdef
  have hE0 : 0 ≤ E := div_nonneg (mul_nonneg (sq_nonneg _) (euc_nonneg a)) (by positivity)
  set lm := ilam Nt (r ^ 2) Λ k with hlmdef
  have ho1 : o.1 = lm := rfl
  -- the multiplier and its complementarity gap
  have hlm : 0 ≤ lm ∧ lm ≤ Λ ∧ Nt lm ≤ r ^ 2 ∧
      lm * (r ^ 2 - euc (zlam a κ ρ τ lm) ^ 2) ≤ Λ * δ + E := by
    simp only [lm, ilam]
    split_ifs with h0
    · refine ⟨le_rfl, hΛ, h0, ?_⟩
      rw [zero_mul]; positivity
    · push Not at h0
      have hNΛ : Nt Λ ≤ r ^ 2 := by have := hN Λ hΛ; rw [abs_le] at this; linarith
      obtain ⟨hl0, hlh, hhΛ, hw, hfe, hin⟩ := ibisect_inv hΛ h0 hNΛ k
      set lo := (ibisect Nt (r ^ 2) Λ k).1
      set hi := (ibisect Nt (r ^ 2) Λ k).2
      refine ⟨by linarith, hhΛ, hfe, ?_⟩
      have hlo' : r ^ 2 - euc (zlam a κ ρ τ lo) ^ 2 < δ := by
        have := hN lo hl0; rw [abs_le] at this; linarith
      have hg := sqgap_le hκ hρ hτ hl0 hlh hδ hlo'
      rw [hw] at hg
      set d := euc a / (2 * ρ ^ 2) * (Λ / 2 ^ k)
      have hd0 : 0 ≤ d := mul_nonneg (div_nonneg (euc_nonneg a) (by positivity)) (by positivity)
      have hE : Λ * (2 * d) = E := by simp only [d, E]; field_simp
      calc hi * (r ^ 2 - euc (zlam a κ ρ τ hi) ^ 2) ≤ hi * (δ + 2 * d) :=
            mul_le_mul_of_nonneg_left hg (by linarith)
        _ ≤ Λ * (δ + 2 * d) := mul_le_mul_of_nonneg_right hhΛ (by positivity)
        _ = Λ * δ + E := by rw [← hE]; ring
  obtain ⟨hlm0, hlmΛ, hNlm, hgap⟩ := hlm
  set z := zlam a κ ρ τ lm with hz
  set N := euc z ^ 2 with hNdef
  set P := a ⬝ᵥ z with hPdef
  have hNe : -δ ≤ Nt lm - N ∧ Nt lm - N ≤ δ := abs_le.mp (hN lm hlm0)
  have hPe : -δP ≤ Pt lm - P ∧ Pt lm - P ≤ δP := abs_le.mp (hP lm hlm0)
  -- conservative rescaling
  have hzn : euc z ≤ Real.sqrt (Nt lm + δ) := by
    rw [show euc z = Real.sqrt (euc z ^ 2) from (Real.sqrt_sq (euc_nonneg z)).symm]
    exact Real.sqrt_le_sqrt (by linarith)
  have hnt : Real.sqrt (Nt lm + δ) ≤ r + δ / (2 * r₀) := by
    have ht0 : 0 ≤ δ / (2 * r₀) := by positivity
    rw [Real.sqrt_le_left (by linarith)]
    have h2 : δ ≤ 2 * r * (δ / (2 * r₀)) := by
      rw [show 2 * r * (δ / (2 * r₀)) = r / r₀ * δ by field_simp]
      exact le_mul_of_one_le_left hδ ((one_le_div hr₀).mpr hr₀τ)
    nlinarith [sq_nonneg (δ / (2 * r₀))]
  have hbox : ∀ i, |z i| ≤ τ * κ i := fun i => zlam_box hκ hτ.1 (by linarith) i
  have hsign : ∀ i, 0 ≤ a i * z i := fun i => zlam_sign hκ hτ.1 (by linarith) i
  set c := iscale (Nt lm) δ r with hcdef
  have ho2 : o.2.1 = c := rfl
  have hres : c • z ∈ Fset κ τ ∧ (∀ i, 0 ≤ a i * (c • z) i) ∧
      fobj a ρ z - δ / (2 * r₀) * euc a ≤ fobj a ρ (c • z) :=
    rescale_feasible hρ.le hτ hbox hsign hzn hnt (by positivity)
  obtain ⟨hmem, hsgn, hloss⟩ := hres
  have hc0 : 0 ≤ c := (iscale_mem (Nh := Nt lm) (δ := δ) hr0.le).1
  have hc1 : c ≤ 1 := (iscale_mem (Nh := Nt lm) (δ := δ) hr0.le).2
  have hzh : zh = c • z := rfl
  -- values
  have hfz : fobj a ρ z = P - ρ * N := rfl
  have hfzh : fobj a ρ (c • z) = c * P - ρ * c ^ 2 * N := by
    unfold fobj
    rw [dotProduct_smul, euc_smul, abs_of_nonneg hc0, smul_eq_mul]; ring
  have hG : Gval a κ ρ τ ≤ P - ρ * N + lm * (r ^ 2 - N) := Gval_le_Dval hκ hρ hτ hlm0
  have hℓ : o.2.2.1 = c * Pt lm - c * δP - ρ * c ^ 2 * (Nt lm + δ) := rfl
  have hu : o.2.2.2 = Pt lm + δP - (ρ + lm) * (Nt lm - δ) + lm * r ^ 2 := rfl
  have hc2 : c ^ 2 ≤ 1 := by nlinarith
  have hρc : 0 ≤ ρ * c ^ 2 := by positivity
  -- `ℓ ≤ f_ρ(ẑ)`
  have hlow : o.2.2.1 ≤ fobj a ρ zh := by
    rw [hℓ, hzh, hfzh]
    have h1 : c * (Pt lm - δP) ≤ c * P :=
      mul_le_mul_of_nonneg_left (by linarith only [hPe.2]) hc0
    have h2 : ρ * c ^ 2 * N ≤ ρ * c ^ 2 * (Nt lm + δ) :=
      mul_le_mul_of_nonneg_left (by linarith only [hNe.1]) hρc
    linarith only [h1, h2]
  refine ⟨hlm0, hlmΛ, hmem, hsgn, hlow, hlow.trans (le_Gval a κ ρ τ hmem), ?_, ?_⟩
  · rw [hu]
    have h1 : 0 ≤ (ρ + lm) * (N - Nt lm + δ) :=
      mul_nonneg (by linarith only [hρ, hlm0]) (by linarith only [hNe.2])
    linarith only [h1, hG, hPe.1]
  · rw [hℓ, hu]
    have hfzl := hloss
    rw [hfz, hfzh] at hfzl
    have h1 : (ρ + lm) * (N - 2 * δ) ≤ (ρ + lm) * (Nt lm - δ) :=
      mul_le_mul_of_nonneg_left (by linarith only [hNe.1]) (by linarith only [hρ, hlm0])
    have h2 : c * (P - δP) ≤ c * Pt lm := mul_le_mul_of_nonneg_left (by linarith only [hPe.1]) hc0
    have h3 : ρ * c ^ 2 * (Nt lm + δ) ≤ ρ * c ^ 2 * (N + 2 * δ) :=
      mul_le_mul_of_nonneg_left (by linarith only [hNe.2]) hρc
    have h4 : c * δP ≤ δP := mul_le_of_le_one_left hδP hc1
    have h5 : ρ * c ^ 2 * δ ≤ ρ * δ := by
      have := mul_le_mul_of_nonneg_left hc2 (mul_nonneg hρ.le hδ); linarith only [this]
    have h6 : lm * δ ≤ Λ * δ := mul_le_mul_of_nonneg_right hlmΛ hδ
    have h7 : δ / (2 * r₀) * euc a = euc a / (2 * r₀) * δ := by ring
    have hgap' : lm * (r ^ 2 - N) ≤ Λ * δ + E := hgap
    linarith only [hfzl, h1, h2, h3, h4, h5, h6, h7, hgap', hPe.2]

end Inexact

/-! ## Assembling the support oracle -/

section Assembly

variable {M : ℕ}

/-- **The support oracle from any certified evaluator.** `support_main` with the exact evaluator
replaced by explicit functions `ẑ(τ)`, `ℓ(τ)`, `u(τ)` that give, on `[h, 1 − h]`, a feasible
sign-aligned `ẑ(τ)` with `ℓ(τ) ≤ f_ρ(ẑ(τ))`, `ℓ(τ) ≤ G_ρ(τ) ≤ u(τ) ≤ ℓ(τ) + ε`. Trisection's
incumbent is attained at some `t₀`, and every `t₀ ∈ [h, 1 − h]` with `best ≤ ℓ(t₀)` gives an
output `v̂` in the ball, sign-aligned with `q`, with
`⟨q, v⟩ ≤ ⟨q, v̂⟩ + ρ + Lh + 3ε + L(1 − 2h)(2/3)ⁿ` for every `v` in the ball. -/
theorem support_of_eval {C Cs : ℝ} {w q : Fin M → ℝ} (hC : 0 < C) (hCs : 0 < Cs)
    (hw : ∀ i, 0 < w i) {ρ h ε : ℝ} (hρ : 0 < ρ) (hh0 : 0 < h) (hh : h ≤ 1 / 2)
    (zf : ℝ → Fin M → ℝ) (lf uf : ℝ → ℝ) (n : ℕ) :
    let κ : Fin M → ℝ := fun i => C * Real.sqrt (w i)
    let a : Fin M → ℝ := fun i => Cs * q i / (C * Real.sqrt (w i))
    let L := max (euc a) (∑ i, |a i| * κ i)
    (∀ τ ∈ Icc h (1 - h), zf τ ∈ Fset κ τ ∧ (∀ i, 0 ≤ a i * zf τ i) ∧
        lf τ ≤ fobj a ρ (zf τ) ∧ lf τ ≤ Gval a κ ρ τ ∧ Gval a κ ρ τ ≤ uf τ ∧
        uf τ ≤ lf τ + ε) →
    (∃ t₀ ∈ Icc h (1 - h), (trisect lf uf h (1 - h) n).best = lf t₀) ∧
    ∀ t₀ ∈ Icc h (1 - h), (trisect lf uf h (1 - h) n).best ≤ lf t₀ →
      let vh : Fin M → ℝ := fun i => Cs * zf t₀ i / (C * Real.sqrt (w i))
      mixed C w vh ≤ Cs ∧ (∀ i, 0 ≤ q i * vh i) ∧
      ∀ v, mixed C w v ≤ Cs →
        q ⬝ᵥ v ≤ q ⬝ᵥ vh + (ρ + L * h + 3 * ε + L * ((1 - 2 * h) * (2 / 3) ^ n)) := by
  intro κ a L hev
  have hsq : ∀ i, 0 < Real.sqrt (w i) := fun i => Real.sqrt_pos.mpr (hw i)
  have hκ : ∀ i, 0 < κ i := fun i => mul_pos hC (hsq i)
  have hL0 : 0 ≤ L := (euc_nonneg a).trans (le_max_left _ _)
  have hcc : ∀ s ∈ Icc h (1 - h), ∀ t ∈ Icc h (1 - h), ∀ θ ∈ Icc (0 : ℝ) 1,
      θ * Gval a κ ρ s + (1 - θ) * Gval a κ ρ t ≤ Gval a κ ρ (θ * s + (1 - θ) * t) :=
    fun s hs t ht θ hθ => Gval_concave hκ hρ.le ⟨by linarith [hs.1], by linarith [hs.2]⟩
      ⟨by linarith [ht.1], by linarith [ht.2]⟩ hθ
  have hlip : ∀ s ∈ Icc h (1 - h), ∀ t ∈ Icc h (1 - h),
      Gval a κ ρ s ≤ Gval a κ ρ t + L * |s - t| :=
    fun s hs t ht => Gval_lipschitz hκ hρ.le ⟨by linarith [hs.1], by linarith [hs.2]⟩
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have horacle : ∀ t ∈ Icc h (1 - h), lf t ≤ Gval a κ ρ t ∧ Gval a κ ρ t ≤ uf t ∧
      uf t ≤ lf t + ε := fun t ht => by
    obtain ⟨-, -, -, h4, h5, h6⟩ := hev t ht
    exact ⟨h4, h5, h6⟩
  have hε0 : 0 ≤ ε := by
    have := horacle h ⟨le_rfl, by linarith⟩
    linarith [this.1, this.2.1, this.2.2]
  obtain ⟨⟨t₀, ht₀, hbest⟩, hbound⟩ := trisect_bound (by linarith) hε0 hcc hlip horacle hL0 n
  refine ⟨⟨t₀, ht₀, hbest⟩, fun t₁ ht₁ hb => ?_⟩
  intro vh
  set best := (trisect lf uf h (1 - h) n).best
  obtain ⟨hzmem, hzsign, hzval, -, -, -⟩ := hev t₁ ht₁
  set zh := zf t₁
  have hnorm := support_normalize (q := q) hC hCs hw vh
  have hzv' : ∀ i, C / Cs * Real.sqrt (w i) * vh i = zh i := fun i => by
    simp only [vh]; field_simp [(hsq i).ne', hC.ne', hCs.ne']; rfl
  simp only [hzv'] at hnorm
  have ht₁01 : t₁ ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht₁.1], by linarith [ht₁.2]⟩
  refine ⟨hnorm.1.mpr ((split_iff hκ zh).mpr ⟨t₁, ht₁01, hzmem⟩), fun i => ?_, ?_⟩
  · have : q i * vh i = a i * zh i := by
      simp only [vh, a]; field_simp [(hsq i).ne', hC.ne']; rfl
    rw [this]; exact hzsign i
  · intro v hv
    have hnv := support_normalize (q := q) hC hCs hw v
    set z : Fin M → ℝ := fun i => C / Cs * Real.sqrt (w i) * v i
    obtain ⟨τ, hτ, hzτ⟩ := (split_iff hκ z).mp (hnv.1.mp hv)
    have h1 : q ⬝ᵥ v ≤ Gval a κ 0 τ := by
      rw [hnv.2]
      have := le_Gval a κ 0 τ hzτ
      simpa [fobj] using this
    have h2 := Gval_zero_le (a := a) hκ hρ.le hτ
    set τc := max h (min τ (1 - h))
    have hτc : τc ∈ Icc h (1 - h) := ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
    have hτc01 : τc ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hτc.1], by linarith [hτc.2]⟩
    have hdist : |τ - τc| ≤ h := by
      rw [abs_le]; constructor
      · simp only [τc]
        rcases le_total τ (1 - h) with h' | h'
        · rw [min_eq_left h']
          rcases le_total h τ with h'' | h''
          · rw [max_eq_right h'']; linarith
          · rw [max_eq_left h'']; linarith [hτ.1]
        · rw [min_eq_right h', max_eq_right (by linarith)]; linarith
      · simp only [τc]
        rcases le_total τ (1 - h) with h' | h'
        · rw [min_eq_left h']
          rcases le_total h τ with h'' | h''
          · rw [max_eq_right h'']; linarith
          · rw [max_eq_left h'']; linarith
        · rw [min_eq_right h', max_eq_right (by linarith)]; linarith [hτ.2]
    have h3 := Gval_lipschitz (a := a) hκ hρ.le hτ hτc01
    have h4 := hbound τc hτc
    have h5 : best ≤ q ⬝ᵥ vh := by
      refine hb.trans (hzval.trans ((fobj_le_dot hρ.le zh).trans (le_of_eq ?_)))
      rw [hnorm.2]
    have h6 := mul_le_mul_of_nonneg_left hdist hL0
    linarith

/-- The starting multiplier `Λ = A₊/h` passes with margin: `‖z(Λ)‖₂ ≤ h/2`. -/
theorem euc_zlam_start {M : ℕ} {a κ : Fin M → ℝ} (hκ : ∀ i, 0 < κ i) {ρ h Ap τ : ℝ}
    (hρ : 0 < ρ) (hh0 : 0 < h) (hAp : euc a ≤ Ap) (hτ : 0 ≤ τ) :
    euc (zlam a κ ρ τ (Ap / h)) ≤ h / 2 := by
  have hAp0 : 0 ≤ Ap := (euc_nonneg a).trans hAp
  have hpos : 0 < ρ + Ap / h := by positivity
  refine (euc_zlam_le hκ hτ hpos).trans ?_
  rw [div_le_iff₀ (by positivity)]
  have : h / 2 * (2 * (ρ + Ap / h)) = h * ρ + Ap := by field_simp
  rw [this]
  nlinarith [mul_pos hh0 hρ]

/-- **The support oracle from approximate sums.** Trisection over `[h, 1 − h]` with `N` steps,
each evaluation the inexact evaluator `ieval` with `m` bisection steps from `Λ = A₊/h`, using
any approximate squared norms `Ñ(τ, λ)` and objective sums `P̃(τ, λ)` with errors `δ ≤ 3h²/4`
and `δ_P`. The loss is `ρ + Lh + 3ε + L(1 − 2h)(2/3)ᴺ` with
`ε = Λ²‖a‖₂/(ρ²2ᵐ) + (3Λ + 4ρ + ‖a‖₂/(2h))δ + 4δ_P`. -/
theorem support_inexact {C Cs : ℝ} {w q : Fin M → ℝ} (hC : 0 < C) (hCs : 0 < Cs)
    (hw : ∀ i, 0 < w i) {ρ h Ap δ δP : ℝ} (hρ : 0 < ρ) (hh0 : 0 < h) (hh : h ≤ 1 / 2)
    (hAp : euc (fun i => Cs * q i / (C * Real.sqrt (w i))) ≤ Ap) (hδ : 0 ≤ δ) (hδP : 0 ≤ δP)
    (hδh : δ ≤ 3 * h ^ 2 / 4) (Nt Pt : ℝ → ℝ → ℝ) (N m : ℕ) :
    let κ : Fin M → ℝ := fun i => C * Real.sqrt (w i)
    let a : Fin M → ℝ := fun i => Cs * q i / (C * Real.sqrt (w i))
    let L := max (euc a) (∑ i, |a i| * κ i)
    let Λ := Ap / h
    let ε := Λ ^ 2 * euc a / (ρ ^ 2 * 2 ^ m) + (3 * Λ + 4 * ρ + euc a / (2 * h)) * δ + 4 * δP
    let ev : ℝ → ℝ × ℝ × ℝ × ℝ := fun τ => ieval (Nt τ) (Pt τ) δ δP ρ (1 - τ) Λ m
    let zf : ℝ → Fin M → ℝ := fun τ => (ev τ).2.1 • zlam a κ ρ τ (ev τ).1
    let best := (trisect (fun τ => (ev τ).2.2.1) (fun τ => (ev τ).2.2.2) h (1 - h) N).best
    (∀ τ ∈ Icc h (1 - h), ∀ lm, 0 ≤ lm → |Nt τ lm - euc (zlam a κ ρ τ lm) ^ 2| ≤ δ ∧
        |Pt τ lm - a ⬝ᵥ zlam a κ ρ τ lm| ≤ δP) →
    (∃ t₀ ∈ Icc h (1 - h), best = (ev t₀).2.2.1) ∧
    ∀ t₀ ∈ Icc h (1 - h), best ≤ (ev t₀).2.2.1 →
      let vh : Fin M → ℝ := fun i => Cs * zf t₀ i / (C * Real.sqrt (w i))
      mixed C w vh ≤ Cs ∧ (∀ i, 0 ≤ q i * vh i) ∧
      ∀ v, mixed C w v ≤ Cs →
        q ⬝ᵥ v ≤ q ⬝ᵥ vh + (ρ + L * h + 3 * ε + L * ((1 - 2 * h) * (2 / 3) ^ N)) := by
  intro κ a L Λ ε ev zf best hNP
  have hκ : ∀ i, 0 < κ i := fun i => mul_pos hC (Real.sqrt_pos.mpr (hw i))
  have hΛ0 : 0 ≤ Λ := div_nonneg ((euc_nonneg a).trans hAp) hh0.le
  have hev : ∀ τ ∈ Icc h (1 - h), zf τ ∈ Fset κ τ ∧ (∀ i, 0 ≤ a i * zf τ i) ∧
      (ev τ).2.2.1 ≤ fobj a ρ (zf τ) ∧ (ev τ).2.2.1 ≤ Gval a κ ρ τ ∧
      Gval a κ ρ τ ≤ (ev τ).2.2.2 ∧ (ev τ).2.2.2 ≤ (ev τ).2.2.1 + ε := by
    intro τ hτ
    have hτ01 : τ ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have hΛr : euc (zlam a κ ρ τ Λ) ^ 2 + δ ≤ (1 - τ) ^ 2 := by
      have h1 := euc_zlam_start hκ hρ hh0 hAp hτ01.1
      have h2 : h ≤ 1 - τ := by linarith [hτ.2]
      have h3 : euc (zlam a κ ρ τ Λ) ^ 2 ≤ (h / 2) ^ 2 :=
        pow_le_pow_left₀ (euc_nonneg _) h1 2
      nlinarith
    obtain ⟨-, -, h1, h2, h3, h4, h5, h6⟩ := ievaluator hκ hρ hτ01 hh0 (by linarith [hτ.2]) hΛ0
      hδ hδP (Nt := Nt τ) (Pt := Pt τ) (fun lm hlm => (hNP τ hτ lm hlm).1)
      (fun lm hlm => (hNP τ hτ lm hlm).2) hΛr m
    exact ⟨h1, h2, h3, h4, h5, by linarith⟩
  exact support_of_eval hC hCs hw hρ hh0 hh zf (fun τ => (ev τ).2.2.1) (fun τ => (ev τ).2.2.2) N
    hev

end Assembly

/-! ## All sums from certified hidden aggregates -/

section Hidden

variable {M n : ℕ}

/-- `|z(λ)ᵢ| ≤ |aᵢ|/(2ρ)` for `λ ≥ 0`. -/
theorem abs_clip_le {x B ρ lm : ℝ} (hB : 0 ≤ B) (hρ : 0 < ρ) (hlm : 0 ≤ lm) :
    |clip x B (ρ + lm)| ≤ |x| / (2 * ρ) := by
  rw [clip_abs hB (by linarith)]
  exact (min_le_right _ _).trans
    (div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (by linarith))

/-- The two pair formulas have magnitude at most `Ā²/(4ρ²)` and `Ā²/(2ρ)`. -/
theorem clip_formula_bounds {x B ρ lm Abar : ℝ} (hB : 0 ≤ B) (hρ : 0 < ρ) (hlm : 0 ≤ lm)
    (hx : |x| ≤ Abar) :
    |clip x B (ρ + lm) ^ 2| ≤ Abar ^ 2 / (4 * ρ ^ 2) ∧
      |x * clip x B (ρ + lm)| ≤ Abar ^ 2 / (2 * ρ) := by
  have h1 := abs_clip_le (x := x) hB hρ hlm
  have h0 : 0 ≤ |x| := abs_nonneg x
  have h2 : |x| / (2 * ρ) ≤ Abar / (2 * ρ) := div_le_div_of_nonneg_right hx (by positivity)
  have hc0 : 0 ≤ |clip x B (ρ + lm)| := abs_nonneg _
  constructor
  · rw [abs_pow]
    calc |clip x B (ρ + lm)| ^ 2 ≤ (Abar / (2 * ρ)) ^ 2 :=
          pow_le_pow_left₀ hc0 (h1.trans h2) 2
      _ = Abar ^ 2 / (4 * ρ ^ 2) := by ring
  · rw [abs_mul]
    calc |x| * |clip x B (ρ + lm)| ≤ Abar * (Abar / (2 * ρ)) :=
          mul_le_mul hx (h1.trans h2) hc0 (h0.trans hx)
      _ = Abar ^ 2 / (2 * ρ) := by ring

/-- **The support oracle with every hidden sum a certified pair aggregate.** The `M` LP
coordinates are hidden copies of pairs (`hid`, multiplicities `symS G e`) and explicit
coordinates; the norm weights and objective are constant on copies (`wb`, `qb`). Each squared
norm `‖z(λ)‖₂²` and objective sum `aᵀz(λ)` is the explicit part plus one rounded pair aggregate
`hiddenSumProg` of the coordinate formula `eq:supportkkt` (`6Bn` queries each), certified to
`δ = M/2^p`. With the public magnitude bound `Ā` on the normalized objective, `B` bits suffice
(`Φ 2^p + 1 ≤ 2^B`). If `M/2^p ≤ 3h²/4`, the output satisfies the support guarantee with loss
`ρ + Lh + 3ε + L(1 − 2h)(2/3)ᴺ`, `ε = Λ²‖a‖₂/(ρ²2ᵐ) + (3Λ + 4ρ + ‖a‖₂/(2h))δ + 4δ`. -/
theorem support_hidden (G : DiGraph (Fin n)) (hid : Fin M → Option (Sym2 (Fin n)))
    (hcount : ∀ e, (univ.filter fun i => hid i = some e).card = Spanner.symS G e)
    {C Cs : ℝ} {w q : Fin M → ℝ} {wb qb : Sym2 (Fin n) → ℝ}
    (hwb : ∀ i e, hid i = some e → w i = wb e) (hqb : ∀ i e, hid i = some e → q i = qb e)
    (hC : 0 < C) (hCs : 0 < Cs) (hw : ∀ i, 0 < w i) {ρ h Ap Abar Φ : ℝ} (hρ : 0 < ρ)
    (hh0 : 0 < h) (hh : h ≤ 1 / 2)
    (hAp : euc (fun i => Cs * q i / (C * Real.sqrt (w i))) ≤ Ap)
    (hAbar : ∀ e, |Cs * qb e / (C * Real.sqrt (wb e))| ≤ Abar)
    (hΦ1 : Abar ^ 2 / (4 * ρ ^ 2) ≤ Φ) (hΦ2 : Abar ^ 2 / (2 * ρ) ≤ Φ)
    {p B : ℕ} (hB : Φ * 2 ^ p + 1 ≤ 2 ^ B) (hp : (M : ℝ) / 2 ^ p ≤ 3 * h ^ 2 / 4) (N m : ℕ) :
    let κ : Fin M → ℝ := fun i => C * Real.sqrt (w i)
    let a : Fin M → ℝ := fun i => Cs * q i / (C * Real.sqrt (w i))
    let L := max (euc a) (∑ i, |a i| * κ i)
    let ab : Sym2 (Fin n) → ℝ := fun e => Cs * qb e / (C * Real.sqrt (wb e))
    let κb : Sym2 (Fin n) → ℝ := fun e => C * Real.sqrt (wb e)
    let δ : ℝ := M / 2 ^ p
    let Nt : ℝ → ℝ → ℝ := fun τ lm =>
      (hiddenSumProg (∑ i ∈ univ.filter (fun i => hid i = none), zlam a κ ρ τ lm i ^ 2)
        (fun e => clip (ab e) (τ * κb e) (ρ + lm) ^ 2) p B).eval G.out
    let Pt : ℝ → ℝ → ℝ := fun τ lm =>
      (hiddenSumProg (∑ i ∈ univ.filter (fun i => hid i = none), a i * zlam a κ ρ τ lm i)
        (fun e => ab e * clip (ab e) (τ * κb e) (ρ + lm)) p B).eval G.out
    let Λ := Ap / h
    let ε := Λ ^ 2 * euc a / (ρ ^ 2 * 2 ^ m) + (3 * Λ + 4 * ρ + euc a / (2 * h)) * δ + 4 * δ
    let ev : ℝ → ℝ × ℝ × ℝ × ℝ := fun τ => ieval (Nt τ) (Pt τ) δ δ ρ (1 - τ) Λ m
    let zf : ℝ → Fin M → ℝ := fun τ => (ev τ).2.1 • zlam a κ ρ τ (ev τ).1
    let best := (trisect (fun τ => (ev τ).2.2.1) (fun τ => (ev τ).2.2.2) h (1 - h) N).best
    (∃ t₀ ∈ Icc h (1 - h), best = (ev t₀).2.2.1) ∧
    ∀ t₀ ∈ Icc h (1 - h), best ≤ (ev t₀).2.2.1 →
      let vh : Fin M → ℝ := fun i => Cs * zf t₀ i / (C * Real.sqrt (w i))
      mixed C w vh ≤ Cs ∧ (∀ i, 0 ≤ q i * vh i) ∧
      ∀ v, mixed C w v ≤ Cs →
        q ⬝ᵥ v ≤ q ⬝ᵥ vh + (ρ + L * h + 3 * ε + L * ((1 - 2 * h) * (2 / 3) ^ N)) := by
  intro κ a L ab κb δ Nt Pt Λ ε ev zf best
  have hδ : 0 ≤ δ := by positivity
  -- data are constant on copies
  have ha : ∀ i e, hid i = some e → a i = ab e := fun i e he => by
    simp only [a, ab, hwb i e he, hqb i e he]
  have hκe : ∀ i e, hid i = some e → κ i = κb e := fun i e he => by
    simp only [κ, κb, hwb i e he]
  have hz : ∀ τ lm i e, hid i = some e →
      zlam a κ ρ τ lm i = clip (ab e) (τ * κb e) (ρ + lm) := fun τ lm i e he => by
    simp only [zlam, ha i e he, hκe i e he]
  have hNP : ∀ τ ∈ Icc h (1 - h), ∀ lm, 0 ≤ lm →
      |Nt τ lm - euc (zlam a κ ρ τ lm) ^ 2| ≤ δ ∧
        |Pt τ lm - a ⬝ᵥ zlam a κ ρ τ lm| ≤ δ := by
    intro τ hτ lm hlm
    have hτ0 : 0 ≤ τ := by linarith [hτ.1]
    have hbd : ∀ u v : Fin n, u < v →
        |clip (ab s(u, v)) (τ * κb s(u, v)) (ρ + lm) ^ 2| ≤ Φ ∧
          |ab s(u, v) * clip (ab s(u, v)) (τ * κb s(u, v)) (ρ + lm)| ≤ Φ := fun u v _ => by
      have := clip_formula_bounds (B := τ * κb s(u, v)) (lm := lm)
        (mul_nonneg hτ0 (mul_nonneg hC.le (Real.sqrt_nonneg _))) hρ hlm (hAbar s(u, v))
      exact ⟨this.1.trans hΦ1, this.2.trans hΦ2⟩
    constructor
    · rw [euc_sq]
      exact hiddenSumProg_err hid G hcount (fun i e he => by rw [hz τ lm i e he])
        (fun u v huv => floor_natAbs_lt (hbd u v huv).1 hB)
    · have := hiddenSumProg_err hid G hcount
        (ψ := fun i => a i * zlam a κ ρ τ lm i)
        (ψb := fun e => ab e * clip (ab e) (τ * κb e) (ρ + lm))
        (fun i e he => by simp only [ha i e he, hz τ lm i e he])
        (fun u v huv => floor_natAbs_lt (hbd u v huv).2 hB)
      exact this
  exact support_inexact hC hCs hw hρ hh0 hh hAp hδ hδ hp Nt Pt N m hNP

end Hidden

/-! ## The support oracle as a query program -/

section Program

variable {I A : Type} {Q : ℕ}

/-- The bisection as a program: one approximate squared norm per step. -/
def ibisectProg (NP : ℝ → DTree I A ℝ Q) (r2 Λ : ℝ) : (k : ℕ) → DTree I A (ℝ × ℝ) (k * Q)
  | 0 => DTree.pure (0, Λ)
  | k + 1 => ((ibisectProg NP r2 Λ k).bind fun p => (NP ((p.1 + p.2) / 2)).map fun x =>
      if x ≤ r2 then (p.1, (p.1 + p.2) / 2) else ((p.1 + p.2) / 2, p.2)).cast
        (by rw [Nat.succ_mul])

theorem ibisectProg_eval (NP : ℝ → DTree I A ℝ Q) (r2 Λ : ℝ) (read : I → A) (k : ℕ) :
    (ibisectProg NP r2 Λ k).eval read = ibisect (fun lm => (NP lm).eval read) r2 Λ k := by
  induction k with
  | zero => simp [ibisectProg, ibisect]
  | succ k ih =>
      simp only [ibisectProg, DTree.eval_cast, DTree.eval_bind, DTree.eval_map, ih, ibisect]

/-- **The fixed-`τ` evaluator as a program**: the test at `0`, `k` bisection steps, and the two
sums at `λ̂`, so `(k + 3)` sum programs. -/
def ievalProg (NP PP : ℝ → DTree I A ℝ Q) (δ δP ρ r Λ : ℝ) (k : ℕ) :
    DTree I A (ℝ × ℝ × ℝ × ℝ) ((k + 3) * Q) :=
  ((NP 0).bind fun n0 => (ibisectProg NP (r ^ 2) Λ k).bind fun br =>
    let lm := if n0 ≤ r ^ 2 then 0 else br.2
    (NP lm).bind fun nh => (PP lm).map fun ph =>
      let c := iscale nh δ r
      (lm, c, ilow ph nh δ δP ρ c, iupp ph nh δ δP ρ r lm)).cast (by ring)

theorem ievalProg_eval (NP PP : ℝ → DTree I A ℝ Q) (δ δP ρ r Λ : ℝ) (k : ℕ) (read : I → A) :
    (ievalProg NP PP δ δP ρ r Λ k).eval read =
      ieval (fun lm => (NP lm).eval read) (fun lm => (PP lm).eval read) δ δP ρ r Λ k := by
  simp only [ievalProg, DTree.eval_cast, DTree.eval_bind, DTree.eval_map, ibisectProg_eval,
    ieval, ilam]

/-- One trisection step on the evaluator outputs `(ℓ₁, u₁)` at `m₁` and `(ℓ₂, u₂)` at `m₂`,
also tracking a point `arg` attaining the incumbent. -/
def tstepA (l1 u1 l2 u2 : ℝ) (s : TState × ℝ) : TState × ℝ :=
  let m₁ := s.1.lo + (s.1.hi - s.1.lo) / 3
  let m₂ := s.1.hi - (s.1.hi - s.1.lo) / 3
  let b := max s.1.best (max l1 l2)
  let arg := if max l1 l2 ≤ s.1.best then s.2 else if l2 ≤ l1 then m₁ else m₂
  (if u1 < l2 then ⟨m₁, s.1.hi, b, m₂⟩
    else if u2 < l1 then ⟨s.1.lo, m₂, b, m₁⟩
    else ⟨m₁, m₂, b, m₁⟩, arg)

/-- **Trisection as a program**: `1 + 2N` evaluations of `EV`, tracking the incumbent's point. -/
def trisectProg (EV : ℝ → DTree I A (ℝ × ℝ × ℝ × ℝ) Q) (α β : ℝ) :
    (N : ℕ) → DTree I A (TState × ℝ) (Q + N * (Q + Q))
  | 0 => ((EV α).map fun o => ((⟨α, β, o.2.2.1, α⟩ : TState), α)).cast (by ring)
  | N + 1 => ((trisectProg EV α β N).bind fun s =>
      (EV (s.1.lo + (s.1.hi - s.1.lo) / 3)).bind fun o1 =>
        (EV (s.1.hi - (s.1.hi - s.1.lo) / 3)).map fun o2 =>
          tstepA o1.2.2.1 o1.2.2.2 o2.2.2.1 o2.2.2.2 s).cast (by ring)

theorem trisect_lohi {ℓ u : ℝ → ℝ} {α β : ℝ} (hαβ : α ≤ β) (N : ℕ) :
    α ≤ (trisect ℓ u α β N).lo ∧ (trisect ℓ u α β N).lo ≤ (trisect ℓ u α β N).hi ∧
      (trisect ℓ u α β N).hi ≤ β := by
  induction N with
  | zero => exact ⟨le_rfl, hαβ, le_rfl⟩
  | succ N ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      simp only [trisect, tstep]
      split_ifs
      · exact ⟨by linarith, by linarith, h3⟩
      · exact ⟨h1, by linarith, by linarith⟩
      · exact ⟨by linarith, by linarith, by linarith⟩

/-- The program's trisection state is `trisect ℓ u`, and its tracked point `t₀ ∈ [α, β]` has
`ℓ(t₀) = best`. -/
theorem trisectProg_eval (EV : ℝ → DTree I A (ℝ × ℝ × ℝ × ℝ) Q) {α β : ℝ} (hαβ : α ≤ β)
    (read : I → A) (N : ℕ) :
    let ℓ : ℝ → ℝ := fun τ => ((EV τ).eval read).2.2.1
    let u : ℝ → ℝ := fun τ => ((EV τ).eval read).2.2.2
    ((trisectProg EV α β N).eval read).1 = trisect ℓ u α β N ∧
      ((trisectProg EV α β N).eval read).2 ∈ Icc α β ∧
      ℓ ((trisectProg EV α β N).eval read).2 = (trisect ℓ u α β N).best := by
  intro ℓ u
  induction N with
  | zero =>
      refine ⟨?_, ?_, ?_⟩ <;> simp [trisectProg, trisect, hαβ, ℓ]
  | succ N ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      simp only [trisectProg, DTree.eval_cast, DTree.eval_bind, DTree.eval_map]
      set s := (trisectProg EV α β N).eval read with hs
      have hb := trisect_lohi (ℓ := ℓ) (u := u) hαβ N
      rw [← h1] at hb
      obtain ⟨hb1, hb2, hb3⟩ := hb
      have hst : trisect ℓ u α β (N + 1) = tstep ℓ u s.1 := by
        simp only [trisect, h1]
      rw [hst]
      refine ⟨rfl, ?_, ?_⟩
      · simp only [tstepA]
        split_ifs
        · exact h2
        · exact ⟨by linarith, by linarith⟩
        · exact ⟨by linarith, by linarith⟩
      · simp only [tstepA, tstep]
        set l1 := ℓ (s.1.lo + (s.1.hi - s.1.lo) / 3)
        set l2 := ℓ (s.1.hi - (s.1.hi - s.1.lo) / 3)
        have hbest : (if u (s.1.lo + (s.1.hi - s.1.lo) / 3) < l2 then
            (⟨s.1.lo + (s.1.hi - s.1.lo) / 3, s.1.hi, max s.1.best (max l1 l2),
              s.1.hi - (s.1.hi - s.1.lo) / 3⟩ : TState)
          else if u (s.1.hi - (s.1.hi - s.1.lo) / 3) < l1 then
            ⟨s.1.lo, s.1.hi - (s.1.hi - s.1.lo) / 3, max s.1.best (max l1 l2),
              s.1.lo + (s.1.hi - s.1.lo) / 3⟩
          else ⟨s.1.lo + (s.1.hi - s.1.lo) / 3, s.1.hi - (s.1.hi - s.1.lo) / 3,
              max s.1.best (max l1 l2), s.1.lo + (s.1.hi - s.1.lo) / 3⟩).best =
            max s.1.best (max l1 l2) := by
          split_ifs <;> rfl
        rw [hbest]
        have h3' : ℓ s.2 = s.1.best := by rw [h3, h1]
        split_ifs with hA hB
        · rw [max_eq_left hA, h3']
        · push Not at hA
          rw [max_eq_right hA.le, max_eq_left hB]
        · push Not at hA hB
          rw [max_eq_right hA.le, max_eq_right hB.le]

/-- **The support program**: trisection, then one more evaluation at the incumbent's point.
It outputs `(t₀, (λ̂, c, ℓ, u))`; the vector is the public formula `c z(λ̂)` at `t₀`. -/
def supportProg (EV : ℝ → DTree I A (ℝ × ℝ × ℝ × ℝ) Q) (h : ℝ) (N : ℕ) :
    DTree I A (ℝ × (ℝ × ℝ × ℝ × ℝ)) ((2 * N + 2) * Q) :=
  ((trisectProg EV h (1 - h) N).bind fun s => (EV s.2).map fun o => (s.2, o)).cast (by ring)

end Program

section HiddenProgram

variable {M n : ℕ}

/-- **The support oracle as an outgoing-cut query program**, with every hidden sum a certified
pair aggregate. Under the hypotheses of `support_hidden`, the program's output `(t₀, (λ̂, c, -, -))`
gives `v̂ = unscale(c z(λ̂))` at `τ = t₀`, which lies in the ball, is sign-aligned with `q`, and
satisfies `⟨q, v⟩ ≤ ⟨q, v̂⟩ + ρ + Lh + 3ε + L(1 − 2h)(2/3)ᴺ` for every `v` in the ball. The program
uses at most `(2N + 2)(m + 3) · 6Bn` queries. -/
theorem supportProg_hidden (G : DiGraph (Fin n)) (hid : Fin M → Option (Sym2 (Fin n)))
    (hcount : ∀ e, (univ.filter fun i => hid i = some e).card = Spanner.symS G e)
    {C Cs : ℝ} {w q : Fin M → ℝ} {wb qb : Sym2 (Fin n) → ℝ}
    (hwb : ∀ i e, hid i = some e → w i = wb e) (hqb : ∀ i e, hid i = some e → q i = qb e)
    (hC : 0 < C) (hCs : 0 < Cs) (hw : ∀ i, 0 < w i) {ρ h Ap Abar Φ : ℝ} (hρ : 0 < ρ)
    (hh0 : 0 < h) (hh : h ≤ 1 / 2)
    (hAp : euc (fun i => Cs * q i / (C * Real.sqrt (w i))) ≤ Ap)
    (hAbar : ∀ e, |Cs * qb e / (C * Real.sqrt (wb e))| ≤ Abar)
    (hΦ1 : Abar ^ 2 / (4 * ρ ^ 2) ≤ Φ) (hΦ2 : Abar ^ 2 / (2 * ρ) ≤ Φ)
    {p B : ℕ} (hB : Φ * 2 ^ p + 1 ≤ 2 ^ B) (hp : (M : ℝ) / 2 ^ p ≤ 3 * h ^ 2 / 4) (N m : ℕ) :
    let κ : Fin M → ℝ := fun i => C * Real.sqrt (w i)
    let a : Fin M → ℝ := fun i => Cs * q i / (C * Real.sqrt (w i))
    let L := max (euc a) (∑ i, |a i| * κ i)
    let ab : Sym2 (Fin n) → ℝ := fun e => Cs * qb e / (C * Real.sqrt (wb e))
    let κb : Sym2 (Fin n) → ℝ := fun e => C * Real.sqrt (wb e)
    let δ : ℝ := M / 2 ^ p
    let NP : ℝ → ℝ → DTree (Finset (Fin n)) ℕ ℝ (6 * B * n) := fun τ lm =>
      hiddenSumProg (∑ i ∈ univ.filter (fun i => hid i = none), zlam a κ ρ τ lm i ^ 2)
        (fun e => clip (ab e) (τ * κb e) (ρ + lm) ^ 2) p B
    let PP : ℝ → ℝ → DTree (Finset (Fin n)) ℕ ℝ (6 * B * n) := fun τ lm =>
      hiddenSumProg (∑ i ∈ univ.filter (fun i => hid i = none), a i * zlam a κ ρ τ lm i)
        (fun e => ab e * clip (ab e) (τ * κb e) (ρ + lm)) p B
    let Λ := Ap / h
    let ε := Λ ^ 2 * euc a / (ρ ^ 2 * 2 ^ m) + (3 * Λ + 4 * ρ + euc a / (2 * h)) * δ + 4 * δ
    let EV := fun τ => ievalProg (NP τ) (PP τ) δ δ ρ (1 - τ) Λ m
    let out := (supportProg EV h N).eval G.out
    let vh : Fin M → ℝ := fun i =>
      Cs * (out.2.2.1 • zlam a κ ρ out.1 out.2.1) i / (C * Real.sqrt (w i))
    out.1 ∈ Icc h (1 - h) ∧ mixed C w vh ≤ Cs ∧ (∀ i, 0 ≤ q i * vh i) ∧
      (∀ v, mixed C w v ≤ Cs →
        q ⬝ᵥ v ≤ q ⬝ᵥ vh + (ρ + L * h + 3 * ε + L * ((1 - 2 * h) * (2 / 3) ^ N))) ∧
      (supportProg EV h N).cost G.out ≤ (2 * N + 2) * ((m + 3) * (6 * B * n)) := by
  intro κ a L ab κb δ NP PP Λ ε EV out vh
  have hmain := support_hidden G hid hcount hwb hqb hC hCs hw hρ hh0 hh hAp hAbar hΦ1 hΦ2 hB hp
    N m
  have hEV : ∀ τ, (EV τ).eval G.out =
      ieval (fun lm => (NP τ lm).eval G.out) (fun lm => (PP τ lm).eval G.out) δ δ ρ (1 - τ) Λ m :=
    fun τ => ievalProg_eval _ _ _ _ _ _ _ _ _
  obtain ⟨htr, harg, hval⟩ := trisectProg_eval EV (by linarith : h ≤ 1 - h) G.out N
  have hout : out = (((trisectProg EV h (1 - h) N).eval G.out).2,
      (EV ((trisectProg EV h (1 - h) N).eval G.out).2).eval G.out) := by
    simp only [out, supportProg, DTree.eval_cast, DTree.eval_bind, DTree.eval_map]
  set t₀ := ((trisectProg EV h (1 - h) N).eval G.out).2
  have hℓ : (fun τ => ((EV τ).eval G.out).2.2.1) =
      (fun τ => (ieval (fun lm => (NP τ lm).eval G.out) (fun lm => (PP τ lm).eval G.out)
        δ δ ρ (1 - τ) Λ m).2.2.1) := funext fun τ => by rw [hEV]
  have hu : (fun τ => ((EV τ).eval G.out).2.2.2) =
      (fun τ => (ieval (fun lm => (NP τ lm).eval G.out) (fun lm => (PP τ lm).eval G.out)
        δ δ ρ (1 - τ) Λ m).2.2.2) := funext fun τ => by rw [hEV]
  rw [hℓ, hu] at hval
  have hval' : (trisect (fun τ => (ieval (fun lm => (NP τ lm).eval G.out)
      (fun lm => (PP τ lm).eval G.out) δ δ ρ (1 - τ) Λ m).2.2.1)
      (fun τ => (ieval (fun lm => (NP τ lm).eval G.out) (fun lm => (PP τ lm).eval G.out)
        δ δ ρ (1 - τ) Λ m).2.2.2) h (1 - h) N).best ≤
      (ieval (fun lm => (NP t₀ lm).eval G.out) (fun lm => (PP t₀ lm).eval G.out)
        δ δ ρ (1 - t₀) Λ m).2.2.1 := hval.ge
  obtain ⟨h1, h2, h3⟩ := hmain.2 t₀ harg hval'
  have hvh : vh = fun i => Cs * ((ieval (fun lm => (NP t₀ lm).eval G.out)
      (fun lm => (PP t₀ lm).eval G.out) δ δ ρ (1 - t₀) Λ m).2.1 •
        zlam a κ ρ t₀ (ieval (fun lm => (NP t₀ lm).eval G.out)
          (fun lm => (PP t₀ lm).eval G.out) δ δ ρ (1 - t₀) Λ m).1) i /
        (C * Real.sqrt (w i)) := by
    simp only [vh, hout, hEV]
  refine ⟨by rw [hout]; exact harg, ?_, ?_, ?_, ?_⟩
  · rw [hvh]; exact h1
  · rw [hvh]; exact h2
  · rw [hvh]; exact h3
  · exact DTree.cost_le _ _

end HiddenProgram

end

end ImplicitLP
end CutQueryComplexity
