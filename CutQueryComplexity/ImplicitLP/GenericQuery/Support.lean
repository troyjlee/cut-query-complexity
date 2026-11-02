import CutQueryComplexity.ImplicitLP.GenericQuery.Basic

/-! # Actual public support oracle for arbitrary explicit rows

The original certified support implementation is instantiated through a public
explicit-list sum and pair formulas. Its scalar searches and output do not
receive the graph-dependent row count or row enumeration.
-/

set_option autoImplicit false

namespace CutQueryComplexity.ImplicitLP.GenericQuery

open Matrix Finset Real Set
noncomputable section
variable {n me : ℕ} (G : DiGraph (Fin n))

def explSum (g : ℝ → ℝ → ℝ) (qp wp : Point n me) : ℝ :=
  ∑ j, g (qp.explicit j) (wp.explicit j)

/-- **The explicit-row sum is public.** -/
theorem explSum_eq (g : ℝ → ℝ → ℝ) (qp wp : Point n me) :
    ∑ i ∈ univ.filter (fun i => hidden G me i = none), g (vec G qp i) (vec G wp i) =
      explSum g qp wp := by
  rw [sum_filter, ← (rowEquiv G me).sum_comp]
  simp only [hidden, vec, Equiv.symm_apply_apply]
  rw [Fintype.sum_sum_type]
  simp [hiddenRow, rowIndex, Point.explicit, explSum]

/-- The rounded output as a public point. -/
def roundPt (C Cs ρ : ℝ) (po : ℕ) (s : ℝ × ℝ × ℝ) (qp wp : Point n me) : Point n me :=
  fun i => roundCoord C Cs ρ po s.1 s.2.1 s.2.2 (qp i) (wp i)

theorem vec_roundPt (C Cs ρ : ℝ) (po : ℕ) (s : ℝ × ℝ × ℝ) (qp wp : Point n me)
    (i : Fin (rowCount G me)) :
    vec G (roundPt C Cs ρ po s qp wp) i =
      roundCoord C Cs ρ po s.1 s.2.1 s.2.2 (vec G qp i) (vec G wp i) := rfl

/-- The coordinate formulas `z(λ)ᵢ²` and `aᵢ z(λ)ᵢ` as functions of `(qᵢ, wᵢ)`. -/
def zsqF (C Cs ρ τ lm : ℝ) (qi wi : ℝ) : ℝ :=
  clip (Cs * qi / (C * Real.sqrt wi)) (τ * (C * Real.sqrt wi)) (ρ + lm) ^ 2

def zdotF (C Cs ρ τ lm : ℝ) (qi wi : ℝ) : ℝ :=
  Cs * qi / (C * Real.sqrt wi) * clip (Cs * qi / (C * Real.sqrt wi)) (τ * (C * Real.sqrt wi)) (ρ + lm)

/-- The public evaluator: hidden sums as pair aggregates, explicit sums expanded publicly,
allowance `δ = M̄·2^{−p}`. -/
def evPub (C Cs ρ : ℝ) (qp wp : Point n me) (Mbar Ap h : ℝ) (p B m : ℕ) (τ : ℝ) :
    DTree (Finset (Fin n)) ℕ (ℝ × ℝ × ℝ × ℝ) ((m + 3) * (6 * B * n)) :=
  let ab : Sym2 (Fin n) → ℝ := fun e => Cs * pairOf qp.pair e / (C * Real.sqrt (pairOf wp.pair e))
  let κb : Sym2 (Fin n) → ℝ := fun e => C * Real.sqrt (pairOf wp.pair e)
  ievalProg
    (fun lm => hiddenSumProg (explSum (zsqF C Cs ρ τ lm) qp wp)
      (fun e => clip (ab e) (τ * κb e) (ρ + lm) ^ 2) p B)
    (fun lm => hiddenSumProg (explSum (zdotF C Cs ρ τ lm) qp wp)
      (fun e => ab e * clip (ab e) (τ * κb e) (ρ + lm)) p B)
    (Mbar / 2 ^ p) (Mbar / 2 ^ p) ρ (1 - τ) (Ap / h) m

/-- **The public support program.** Trisection with the public evaluator, then the offline
conservative rounding; output the rounded scalars and a public LP point. -/
def supportPubProg (C Cs ρ : ℝ) (qp wp : Point n me) (Mbar Ap h : ℝ) (p B m N : ℕ)
    (kτ kl kc po : ℕ) :
    DTree (Finset (Fin n)) ℕ ((ℝ × ℝ × ℝ) × Point n me) ((2 * N + 2) * ((m + 3) * (6 * B * n))) :=
  (supportProg (evPub C Cs ρ qp wp Mbar Ap h p B m) h N).map fun out =>
    let s := roundScalars kτ kl kc out
    (s, roundPt C Cs ρ po s qp wp)

/-- **Budget on every execution:** `(2N + 2)(m + 3)·6Bn`. -/
theorem supportPubProg_cost (C Cs ρ : ℝ) (qp wp : Point n me) (Mbar Ap h : ℝ)
    (p B m N kτ kl kc po : ℕ) (read : Finset (Fin n) → ℕ) :
    (supportPubProg C Cs ρ qp wp Mbar Ap h p B m N kτ kl kc po).cost read ≤
      (2 * N + 2) * ((m + 3) * (6 * B * n)) := DTree.cost_le _ _

/-- **The public program computes `supportRoundProg`'s output** with `q = vec qp`,
`w = vec wp`, `δ = M̄·2^{−p}`: same scalars, and the output point's copies are its vector. -/
theorem supportPub_eval (C Cs ρ : ℝ) (qp wp : Point n me) (Mbar Ap h : ℝ)
    (p B m N kτ kl kc po : ℕ) :
    let q := vec G qp
    let w := vec G wp
    let hid := hidden G me
    let κ : Fin (rowCount G me) → ℝ := fun i => C * Real.sqrt (w i)
    let a : Fin (rowCount G me) → ℝ := fun i => Cs * q i / (C * Real.sqrt (w i))
    let ab : Sym2 (Fin n) → ℝ := fun e => Cs * pairOf qp.pair e / (C * Real.sqrt (pairOf wp.pair e))
    let κb : Sym2 (Fin n) → ℝ := fun e => C * Real.sqrt (pairOf wp.pair e)
    let δ : ℝ := Mbar / 2 ^ p
    let NP : ℝ → ℝ → DTree (Finset (Fin n)) ℕ ℝ (6 * B * n) := fun τ lm =>
      hiddenSumProg (∑ i ∈ univ.filter (fun i => hid i = none), zlam a κ ρ τ lm i ^ 2)
        (fun e => clip (ab e) (τ * κb e) (ρ + lm) ^ 2) p B
    let PP : ℝ → ℝ → DTree (Finset (Fin n)) ℕ ℝ (6 * B * n) := fun τ lm =>
      hiddenSumProg (∑ i ∈ univ.filter (fun i => hid i = none), a i * zlam a κ ρ τ lm i)
        (fun e => ab e * clip (ab e) (τ * κb e) (ρ + lm)) p B
    let Λ := Ap / h
    let EV := fun τ => ievalProg (NP τ) (PP τ) δ δ ρ (1 - τ) Λ m
    let res := (supportPubProg C Cs ρ qp wp Mbar Ap h p B m N kτ kl kc po).eval G.out
    let resM := (supportRoundProg EV h N C Cs ρ kτ kl kc po q w).eval G.out
    res.1 = resM.1 ∧ vec G res.2 = resM.2 := by
  intro q w hid κ a ab κb δ NP PP Λ EV res resM
  have hEV : evPub C Cs ρ qp wp Mbar Ap h p B m = EV := by
    funext τ
    simp only [evPub, EV, NP, PP]
    congr 2
    · funext lm
      rw [← explSum_eq G]; rfl
    · funext lm
      rw [← explSum_eq G]; rfl
  have h1 : res = (roundScalars kτ kl kc ((supportProg EV h N).eval G.out),
      roundPt C Cs ρ po (roundScalars kτ kl kc ((supportProg EV h N).eval G.out)) qp wp) := by
    simp only [res, supportPubProg, DTree.eval_map, hEV]
  have h2 : resM = (roundScalars kτ kl kc ((supportProg EV h N).eval G.out),
      fun i => roundCoord C Cs ρ po (roundScalars kτ kl kc ((supportProg EV h N).eval G.out)).1
        (roundScalars kτ kl kc ((supportProg EV h N).eval G.out)).2.1
        (roundScalars kτ kl kc ((supportProg EV h N).eval G.out)).2.2 (q i) (w i)) := by
    simp only [resM, supportRoundProg, DTree.eval_map]
  rw [h1, h2]
  exact ⟨rfl, funext fun i => vec_roundPt G _ _ _ _ _ _ _ i⟩

/-- **The public support oracle's guarantee.** With copy-constant data `q = vec qp`,
`w = vec wp` (`w > 0`), a public row bound `M ≤ M̄`, and the public allowance
`δ = M̄·2^{−p} ≤ 3h²/4`, the output point `v` (copies `vec v`) has dyadic coordinates, lies in
the ball, is sign-aligned with `q`, and satisfies the support inequality with loss
`ρ + Lh + 3ε + L(1 − 2h)(2/3)ᴺ + R`; budget `(2N + 2)(m + 3)·6Bn`. -/
theorem supportPub_hidden (qp wp : Point n me) {C Cs : ℝ}
    (hC : 0 < C) (hCs : 0 < Cs) (hw : ∀ i, 0 < vec G wp i) {ρ h Ap Abar Φ Mbar : ℝ}
    (hρ : 0 < ρ) (hh0 : 0 < h) (hh : h ≤ 1 / 2)
    (hAp : euc (fun i => Cs * vec G qp i / (C * Real.sqrt (vec G wp i))) ≤ Ap)
    (hAbar : ∀ e, |Cs * pairOf qp.pair e / (C * Real.sqrt (pairOf wp.pair e))| ≤ Abar)
    (hΦ1 : Abar ^ 2 / (4 * ρ ^ 2) ≤ Φ) (hΦ2 : Abar ^ 2 / (2 * ρ) ≤ Φ)
    {p B : ℕ} (hB : Φ * 2 ^ p + 1 ≤ 2 ^ B) (hMbar : (rowCount G me : ℝ) ≤ Mbar)
    (hp : Mbar / 2 ^ p ≤ 3 * h ^ 2 / 4) (N m : ℕ) (kτ kl kc po : ℕ) :
    let q := vec G qp
    let w := vec G wp
    let κ : Fin (rowCount G me) → ℝ := fun i => C * Real.sqrt (w i)
    let a : Fin (rowCount G me) → ℝ := fun i => Cs * q i / (C * Real.sqrt (w i))
    let L := max (euc a) (∑ i, |a i| * κ i)
    let δ : ℝ := Mbar / 2 ^ p
    let Λ := Ap / h
    let ε := Λ ^ 2 * euc a / (ρ ^ 2 * 2 ^ m) + (3 * Λ + 4 * ρ + euc a / (2 * h)) * δ + 4 * δ
    let R := (1 / 2) ^ kτ * L + euc a ^ 2 * ((1 / 2) ^ kc / (2 * ρ) + (1 / 2) ^ kl / (2 * ρ ^ 2)) +
      (∑ i, |q i|) * (1 / 2) ^ po
    let res := (supportPubProg C Cs ρ qp wp Mbar Ap h p B m N kτ kl kc po).eval G.out
    let v := vec G res.2
    (∃ m₁ : ℤ, res.1.1 = m₁ / 2 ^ kτ) ∧ (∃ m₂ : ℤ, res.1.2.1 = m₂ / 2 ^ kl) ∧
      (∃ m₃ : ℤ, res.1.2.2 = m₃ / 2 ^ kc) ∧
      0 ≤ res.1.1 ∧ 0 ≤ res.1.2.1 ∧ 0 ≤ res.1.2.2 ∧ res.1.2.2 ≤ 1 ∧
      (∀ i, ∃ m : ℤ, v i = m / 2 ^ po) ∧
      mixed C w v ≤ Cs ∧ (∀ i, 0 ≤ q i * v i) ∧
      (∀ v₀, mixed C w v₀ ≤ Cs →
        q ⬝ᵥ v₀ ≤ q ⬝ᵥ v + (ρ + L * h + 3 * ε + L * ((1 - 2 * h) * (2 / 3) ^ N) + R)) ∧
      (supportPubProg C Cs ρ qp wp Mbar Ap h p B m N kτ kl kc po).cost G.out ≤
        (2 * N + 2) * ((m + 3) * (6 * B * n)) := by
  intro q w κ a L δ Λ ε R res v
  have hδM : ((rowCount G me : ℕ) : ℝ) / 2 ^ p ≤ δ := div_le_div_of_nonneg_right hMbar (by positivity)
  obtain ⟨e1, e2⟩ := supportPub_eval G C Cs ρ qp wp Mbar Ap h p B m N kτ kl kc po
  obtain ⟨-, d1, d2, d3, n1, n2, n3, n4, -, -, hdy, hball, hal, -, hsupp, -⟩ :=
    supportRoundProg_hidden_gen G (hidden G me) (hidden_count G me) (wb := pairOf wp.pair)
      (qb := pairOf qp.pair) (fun i e he => vec_hidden G wp i e he)
      (fun i e he => vec_hidden G qp i e he) hC hCs hw hρ hh0 hh hAp hAbar hΦ1 hΦ2 hB hδM hp N m
      kτ kl kc po
  have hv : v = _ := e2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, DTree.cost_le _ _⟩
  · rw [show res.1 = _ from e1]; exact d1
  · rw [show res.1 = _ from e1]; exact d2
  · rw [show res.1 = _ from e1]; exact d3
  · rw [show res.1 = _ from e1]; exact n1
  · rw [show res.1 = _ from e1]; exact n2
  · rw [show res.1 = _ from e1]; exact n3
  · rw [show res.1 = _ from e1]; exact n4
  · rw [hv]; exact hdy
  · rw [hv]; exact hball
  · rw [hv]; exact hal
  · rw [hv]; exact hsupp


theorem supportPub_public (S : SupPub) (qp wp : Point n me) {C Cs : ℝ}
    (hC : 0 < C) (hCs : 0 < Cs) (hw : ∀ i, 0 < vec G wp i) (hσ : 0 < S.σ)
    (hAp : euc (fun i => Cs * vec G qp i / (C * Real.sqrt (vec G wp i))) ≤ S.Ap)
    (hL : max (euc (fun i => Cs * vec G qp i / (C * Real.sqrt (vec G wp i))))
      (∑ i, |Cs * vec G qp i / (C * Real.sqrt (vec G wp i))| *
        (C * Real.sqrt (vec G wp i))) ≤ S.Lb)
    (hSq : ∑ i, |vec G qp i| ≤ S.Sq)
    (hAbar : ∀ e, |Cs * pairOf qp.pair e / (C * Real.sqrt (pairOf wp.pair e))| ≤ S.Abar)
    (hMbar : (rowCount G me : ℝ) ≤ S.Mbar) :
    let q := vec G qp
    let w := vec G wp
    let res := (supportPubProg C Cs S.ρ qp wp S.Mbar S.Ap S.h S.p S.B S.m S.N
      S.kτ S.kl S.kc S.po).eval G.out
    let v := vec G res.2
    (∀ i, ∃ m : ℤ, v i = m / 2 ^ S.po) ∧ mixed C w v ≤ Cs ∧ (∀ i, 0 ≤ q i * v i) ∧
      (∀ v₀, mixed C w v₀ ≤ Cs → q ⬝ᵥ v₀ ≤ q ⬝ᵥ v + S.σ) ∧
      (supportPubProg C Cs S.ρ qp wp S.Mbar S.Ap S.h S.p S.B S.m S.N
        S.kτ S.kl S.kc S.po).cost G.out ≤ (2 * S.N + 2) * ((S.m + 3) * (6 * S.B * n)) := by
  intro q w res v
  set a : Fin (rowCount G me) → ℝ := fun i => Cs * vec G qp i / (C * Real.sqrt (vec G wp i))
  set κ : Fin (rowCount G me) → ℝ := fun i => C * Real.sqrt (vec G wp i)
  set L := max (euc a) (∑ i, |a i| * κ i)
  have hA0 : 0 ≤ S.Ap := (euc_nonneg _).trans hAp
  have hL0 : 0 ≤ L := (euc_nonneg _).trans (le_max_left _ _)
  have hLb0 : 0 ≤ S.Lb := hL0.trans hL
  have hρ : 0 < S.ρ := by unfold SupPub.ρ; positivity
  have hh0 : 0 < S.h := lt_min (by norm_num) (by positivity)
  have hh4 : S.h ≤ 1 / 4 := min_le_left _ _
  have hhσ : S.h ≤ S.σ / (6 * (S.Lb + 1)) := min_le_right _ _
  have hΛ0 : 0 ≤ S.Λ := by unfold SupPub.Λ; positivity
  have hcδ : 0 < S.cδ := by unfold SupPub.cδ; positivity
  have hδt0 : 0 < S.δt := lt_min (by positivity) (by positivity)
  have hδ : S.Mbar / 2 ^ S.p ≤ S.δt := div_two_pow_bits_le hδt0
  have hδ0 : 0 ≤ S.Mbar / 2 ^ S.p := by
    have : (0 : ℝ) ≤ rowCount G me := Nat.cast_nonneg _
    have : 0 ≤ S.Mbar := by linarith
    positivity
  have hp : S.Mbar / 2 ^ S.p ≤ 3 * S.h ^ 2 / 4 := hδ.trans (min_le_right _ _)
  have hB : S.Φ * 2 ^ S.p + 1 ≤ 2 ^ S.B := by
    exact (lt_two_pow_magBits (S.Φ * 2 ^ S.p + 1)).le
  have hΦ1 : S.Abar ^ 2 / (4 * S.ρ ^ 2) ≤ S.Φ := by
    unfold SupPub.Φ; have : 0 ≤ S.Abar ^ 2 / (2 * S.ρ) := by positivity
    linarith
  have hΦ2 : S.Abar ^ 2 / (2 * S.ρ) ≤ S.Φ := by
    unfold SupPub.Φ; have : 0 ≤ S.Abar ^ 2 / (4 * S.ρ ^ 2) := by positivity
    linarith
  obtain ⟨-, -, -, -, -, -, -, hdy, hball, hal, hsupp, hcost⟩ :=
    supportPub_hidden G qp wp hC hCs hw hρ hh0 (by linarith) hAp hAbar hΦ1 hΦ2 hB hMbar hp
      S.N S.m S.kτ S.kl S.kc S.po
  refine ⟨hdy, hball, hal, fun v₀ hv₀ => (hsupp v₀ hv₀).trans ?_, hcost⟩
  -- the loss is at most `σ`
  have hea : euc a ≤ S.Ap := hAp
  have hea0 : 0 ≤ euc a := euc_nonneg _
  set δ := S.Mbar / 2 ^ S.p
  -- term 2
  have t2 : L * S.h ≤ S.σ / 6 := by
    calc L * S.h ≤ S.Lb * (S.σ / (6 * (S.Lb + 1))) :=
          mul_le_mul hL hhσ hh0.le hLb0
      _ ≤ S.σ / 6 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  -- term 3
  have e1 : S.Λ ^ 2 * euc a / (S.ρ ^ 2 * 2 ^ S.m) ≤ S.σ / 54 := by
    have := div_two_pow_bits_le (c := S.Λ ^ 2 * S.Ap / S.ρ ^ 2) (by positivity : 0 < S.σ / 54)
    calc S.Λ ^ 2 * euc a / (S.ρ ^ 2 * 2 ^ S.m) ≤ S.Λ ^ 2 * S.Ap / (S.ρ ^ 2 * 2 ^ S.m) := by
          gcongr
      _ = S.Λ ^ 2 * S.Ap / S.ρ ^ 2 / 2 ^ S.m := by ring
      _ ≤ S.σ / 54 := this
  have e2 : (3 * S.Λ + 4 * S.ρ + euc a / (2 * S.h)) * δ + 4 * δ ≤ S.σ / 27 := by
    have h1 : (3 * S.Λ + 4 * S.ρ + euc a / (2 * S.h)) * δ + 4 * δ ≤ S.cδ * δ := by
      unfold SupPub.cδ
      have : euc a / (2 * S.h) ≤ S.Ap / (2 * S.h) := by gcongr
      nlinarith
    have h2 : S.cδ * δ ≤ S.cδ * (S.σ / (27 * S.cδ)) :=
      mul_le_mul_of_nonneg_left (hδ.trans (min_le_left _ _)) hcδ.le
    have h3 : S.cδ * (S.σ / (27 * S.cδ)) = S.σ / 27 := by field_simp
    linarith
  -- term 4
  have t4 : L * ((1 - 2 * S.h) * (2 / 3) ^ S.N) ≤ S.σ / 6 := by
    have hk := half_pow_iters_le (by positivity : 0 < S.σ / (6 * (S.Lb + 1)))
    have hN : (2 / 3 : ℝ) ^ S.N ≤ S.σ / (6 * (S.Lb + 1)) := by
      unfold SupPub.N
      rw [pow_mul]
      refine le_trans (pow_le_pow_left₀ (by norm_num) (by norm_num : (2 / 3 : ℝ) ^ 2 ≤ 1 / 2) _) hk
    have h1 : (1 - 2 * S.h) * (2 / 3) ^ S.N ≤ S.σ / (6 * (S.Lb + 1)) := by
      have : (0 : ℝ) ≤ (2 / 3) ^ S.N := by positivity
      nlinarith
    have h10 : 0 ≤ (1 - 2 * S.h) * (2 / 3) ^ S.N := by
      have : (0 : ℝ) ≤ (2 / 3) ^ S.N := by positivity
      have : 0 ≤ 1 - 2 * S.h := by linarith
      positivity
    calc L * ((1 - 2 * S.h) * (2 / 3) ^ S.N) ≤ S.Lb * (S.σ / (6 * (S.Lb + 1))) :=
          mul_le_mul hL h1 h10 hLb0
      _ ≤ S.σ / 6 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  -- term 5
  have r1 : (1 / 2) ^ S.kτ * L ≤ S.σ / 24 := by
    rw [mul_comm]; exact mul_half_pow_bits_le (by positivity) hL
  have r2 : euc a ^ 2 * ((1 / 2) ^ S.kc / (2 * S.ρ)) ≤ S.σ / 24 := by
    have := mul_half_pow_bits_le (x := euc a ^ 2 / (2 * S.ρ)) (by positivity : 0 < S.σ / 24)
      (by gcongr : euc a ^ 2 / (2 * S.ρ) ≤ S.Ap ^ 2 / (2 * S.ρ))
    calc _ = euc a ^ 2 / (2 * S.ρ) * (1 / 2) ^ S.kc := by ring
      _ ≤ _ := this
  have r3 : euc a ^ 2 * ((1 / 2) ^ S.kl / (2 * S.ρ ^ 2)) ≤ S.σ / 24 := by
    have := mul_half_pow_bits_le (x := euc a ^ 2 / (2 * S.ρ ^ 2)) (by positivity : 0 < S.σ / 24)
      (by gcongr : euc a ^ 2 / (2 * S.ρ ^ 2) ≤ S.Ap ^ 2 / (2 * S.ρ ^ 2))
    calc _ = euc a ^ 2 / (2 * S.ρ ^ 2) * (1 / 2) ^ S.kl := by ring
      _ ≤ _ := this
  have r4 : (∑ i, |q i|) * (1 / 2) ^ S.po ≤ S.σ / 24 :=
    mul_half_pow_bits_le (by positivity) hSq
  have hρσ : S.ρ = S.σ / 6 := rfl
  show q ⬝ᵥ v + (S.ρ + L * S.h + 3 * (S.Λ ^ 2 * euc a / (S.ρ ^ 2 * 2 ^ S.m) +
      (3 * S.Λ + 4 * S.ρ + euc a / (2 * S.h)) * δ + 4 * δ) +
      L * ((1 - 2 * S.h) * (2 / 3) ^ S.N) +
      ((1 / 2) ^ S.kτ * L + euc a ^ 2 * ((1 / 2) ^ S.kc / (2 * S.ρ) +
        (1 / 2) ^ S.kl / (2 * S.ρ ^ 2)) + (∑ i, |q i|) * (1 / 2) ^ S.po)) ≤ q ⬝ᵥ v + S.σ
  have : euc a ^ 2 * ((1 / 2) ^ S.kc / (2 * S.ρ) + (1 / 2) ^ S.kl / (2 * S.ρ ^ 2)) =
      euc a ^ 2 * ((1 / 2) ^ S.kc / (2 * S.ρ)) + euc a ^ 2 * ((1 / 2) ^ S.kl / (2 * S.ρ ^ 2)) := by
    ring
  rw [this]
  linarith


#print axioms explSum_eq
#print axioms supportPub_eval
#print axioms supportPub_hidden
#print axioms supportPub_public
#print axioms supportPubProg_cost

end
end CutQueryComplexity.ImplicitLP.GenericQuery
