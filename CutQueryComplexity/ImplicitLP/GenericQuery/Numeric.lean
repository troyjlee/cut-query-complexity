import CutQueryComplexity.ImplicitLP.GenericQuery.Query

/-! # Numeric correctness of the actual general Newton program

The generic analytic perturbation lemmas are connected to the executed RHS,
normal solve and exact repair. This module discharges repair-query precision
from the public frozen-solve envelope; higher-level state bounds are next.
-/

set_option autoImplicit false

namespace CutQueryComplexity.ImplicitLP.GenericQuery

open Matrix Finset Spectral
noncomputable section
variable {n me : ℕ} (G : DiGraph (Fin n))

set_option maxHeartbeats 3200000 in
theorem newtonStep_numeric (ER : ExplicitRows n me)
    (hrowA : ∀ i, ∑ j, matrix G ER i j ^ 2 ≤ 2) {κ m x w c : Fin (rowCount G me) → ℝ} {t U : ℝ}
    (hκ : ∀ i, 0 < κ i) (hx : Interior κ m x) (hU1 : 1 ≤ U)
    (hU : ∀ i, Real.pi / κ i ≤ U) {wmin dp : ℝ} (hwmin : 0 < wmin) (hwlo : ∀ i, wmin ≤ w i)
    (hdp : U ^ 2 / wmin ≤ dp) (hwhi : ∀ i, w i ≤ 4) (hwsum : ∑ i, w i ≤ 4 * n) {sst ε : ℝ}
    (hsst : 0 < sst) (hs : ∀ i, sst ≤ slk κ m x i) (hε : 0 < ε) (ht : |t| ≤ 16 * n / ε)
    (hc : ‖c‖ ≤ 4 * U)
    {wf : Sym2 (Fin n) → ℝ} {de : Fin me → ℝ} {qp : Point n me}
    {p0 : Fin n → ℝ} {β C : ℝ} (hC : 0 ≤ C)
    (hDh : ∀ i, |vec G (weights wf de) i - normD w (barS κ m x) i| ≤
      β * normD w (barS κ m x) i)
    (hqh : ∀ i, |vec G qp i - normQ t c w (barDphi κ m x) i| ≤ β) (hβ0 : 0 ≤ β)
    (hβ : β ≤ 1 / 2)
    (hp : gram (matrix G ER) (normD w (barS κ m x)) *ᵥ p0 =
      (matrix G ER)ᵀ *ᵥ fun i => normD w (barS κ m x) i * normQ t c w (barDphi κ m x) i)
    {dmin : ℝ} (hdmin : 0 < dmin) (hdpv : ∀ j, dmin ≤ de (ER.iota j)) (hwf0 : ∀ e, 0 ≤ wf e)
    {K t' R : ℕ} {δ εs : ℝ} {out : Sym2 (Fin n) → ℝ} (hgood : Sparsify.Good G wf K t' δ R out)
    (hεs0 : 0 < εs) (hεs : εs ≤ 1 / 8) (hδlo : 1 - εs ≤ (1 - δ) ^ R)
    (hδhi : (1 + δ) ^ R ≤ 1 + εs)
    {X Λ W Qz : ℝ}
    (hX : 4 * Real.sqrt (2 * rowCount G me) * Real.sqrt (rowCount G me) * dp * (64 * n * U / ε + 4 / sst + 1) /
      (sst ^ 2 / 16) ≤ X)
    (hΛ : 3 / 2 * dp * (2 * rowCount G me) ≤ Λ) (hW : ∀ e, |wf e| ≤ W) (hQz : ∀ u v, |qp.pair u v| ≤ Qz)
    {ew eq : ℤ} (hwg : ∀ e, ∃ z : ℤ, wf e = z * (2 : ℝ) ^ ew)
    (hqg : ∀ u v, ∃ z : ℤ, qp.pair u v = z * (2 : ℝ) ^ eq) (p Brhs Bmv Brep : ℕ)
    (heq : eq ≤ -(p : ℤ))
    (hB : W * (2 * (X + Real.sqrt (1 / (sst ^ 2 / 16 / 2)) *
      (Real.sqrt Λ * X + 2 * (Real.sqrt Λ * (Real.sqrt n * (1 / 2 ^ p)))))) <
        (2 : ℝ) ^ Bmv * (2 : ℝ) ^ (ew - p))
    (hBrhs : W * Qz < (2 : ℝ) ^ Brhs * (2 : ℝ) ^ (ew + eq))
    (hBrep : W * (Qz + 2 * (X + Real.sqrt (1 / (sst ^ 2 / 16 / 2)) *
      (Real.sqrt Λ * X + 2 * (Real.sqrt Λ * (Real.sqrt n * (1 / 2 ^ p)))))) <
        (2 : ℝ) ^ Brep * (2 : ℝ) ^ (ew + eq))
    (hτβ : 2 * (Real.sqrt Λ * (Real.sqrt n * (1 / 2 ^ p))) ≤ β)
    (k : ℕ) (hk : (1 / 2 : ℝ) ^ k ≤ β) :
    let A := matrix G ER
    let Dh := vec G (weights wf de)
    let D := normD w (barS κ m x)
    let q := normQ t c w (barDphi κ m x)
    let b : Fin n → ℝ := Aᵀ *ᵥ fun i => Dh i * vec G qp i
    let P := lap out univ + explicitGram A Dh (hidden G me)
    let xk := (frozenSolveProg wf ew p Bmv (explicitGram A Dh (hidden G me)) P⁻¹ b k 0).eval G.out
    let h : Fin (rowCount G me) → ℝ := fun i => -D i * (q i - (A *ᵥ p0) i)
    let ht' : Fin (rowCount G me) → ℝ := fun i => -Dh i * (vec G qp i - (A *ᵥ xk) i)
    let d := (newtonStepProg ER wf de qp out ew eq p Brhs Bmv Brep k).eval G.out
    let ℓ := sst ^ 2 / 16
    let a := Real.sqrt (2 * rowCount G me)
    let Q := 64 * n * U / ε + 4 / sst
    let Pπ := 4 * a * Real.sqrt (rowCount G me) * dp * (Q + 1) / ℓ
    let Eπ := 2 / ℓ * (a * Real.sqrt (rowCount G me) * dp * (Q + 2) + a ^ 2 * dp * Pπ) +
      (Real.sqrt (2 / ℓ) * (Real.sqrt (3 / 2 * dp) * a) * Pπ + Real.sqrt (2 / ℓ)) + Real.sqrt n
    let P₁ := dp * (Q + Real.sqrt 2 * Pπ) + 2 * dp * (1 + Real.sqrt 2 * Eπ)
    let T₀ := 1 + 2 * C * (⌈Real.sqrt n⌉₊ : ℝ)
    vec G d = repairDir A (iota G ER) ht' ∧ ‖ht' - h‖ ≤ P₁ * β ∧ Aᵀ *ᵥ vec G d = 0 ∧
      mixed C w (fun i => barS κ m x i * (vec G d - h) i) ≤
        2 * T₀ / sst * (1 + Real.sqrt 2 * rowCount G me) * P₁ * β := by
  intro A Dh D q b P xk h ht' d ℓ a Q Pπ Eπ P₁ T₀
  have hxk : euc xk ≤ _ := query_xk_bound hκ hx hU1 hU hwmin hwlo hdp hwhi hsst hs hε ht hc
    (hrowA) (matrix_idRows G ER) hDh hqh hβ (matrix_hidden G ER)
    (weights_hidden G wf de) (hidden_count G me) (hidden_iota G ER) hdmin
    (fun j => by simpa [vec, iota, weights, rowIndex, Point.mk, Point.explicit] using hdpv j) hwf0 hgood hεs0 hεs hδlo hδhi
    hX hΛ hW hwg p Bmv hB k
  have hrhs : ∀ u v, |wf s(u, v) * qp.pair u v| < (2 : ℝ) ^ Brhs * (2 : ℝ) ^ (ew + eq) :=
    fun u v => by
      have hW0 : 0 ≤ W := (abs_nonneg _).trans (hW s(u, v))
      rw [abs_mul]
      exact lt_of_le_of_lt (mul_le_mul (hW _) (hQz u v) (abs_nonneg _) hW0) hBrhs
  have hd : vec G d = repairDir A (iota G ER) ht' :=
    newtonStepProg_eval G ER wf de qp out ew eq p Brhs Bmv Brep k hwg hqg heq hrhs
      (repair_bit_of_bound hW hQz hxk hBrep)
  obtain ⟨H1, H2, H3⟩ := lem_numeric_query hκ hx hU1 hU hwmin hwlo hdp hwhi hwsum hsst hs hε
    ht hc hrowA (matrix_idRows G ER) hC hDh hqh hβ0 hβ hp (matrix_hidden G ER)
    (weights_hidden G wf de) (hidden_count G me) (hidden_iota G ER) hdmin
    (fun j => by simpa [vec, iota, weights, rowIndex, Point.mk, Point.explicit] using hdpv j)
    hwf0 hgood hεs0 hεs hδlo hδhi hX hΛ hW hwg p Bmv hB hτβ k hk
  refine ⟨hd, H1, ?_, ?_⟩
  · rw [hd]; exact H2
  · rw [hd]; exact H3

open Spectral in
set_option maxHeartbeats 3200000 in
/-- Numeric correctness for the program's output, from the path-following invariants:
`newtonStep_numeric` with the weight and slack hypotheses derived as in
the generic analytic theorem (`d₊ = 4M̄U²`, `s_* = ε/(2¹² n M̄² U³)`). -/
theorem newtonStep_numeric_inv (ER : ExplicitRows n me)
    (hrowne : ∀ i, matrix G ER i ≠ 0) (hrowA : ∀ i, ∑ j, matrix G ER i j ^ 2 ≤ 2) {bc : Fin n → ℝ}
    {κ m w c : Fin (rowCount G me) → ℝ} {t U : ℝ}
    {L₀ : ℝ} (hL : 2 ≤ L₀) (hLM : Real.logb 2 (2 * rowCount G me) ≤ L₀ - 1)
    (hκ : ∀ i, 0 < κ i) {c₀ Mbar ε : ℝ} (hc₀lo : 1 / (2 * Mbar) ≤ c₀)
    (hcM : c₀ ≤ 1 / (2 * rowCount G me)) (hU1 : 1 ≤ U) (hU : ∀ i, Real.pi / κ i ≤ U)
    {x x₀ : Fin (rowCount G me) → ℝ}
    (hx : x ∈ Feasible (matrix G ER) bc κ m) (hx₀ : x₀ ∈ Feasible (matrix G ER) bc κ m)
    (hMbar : (rowCount G me : ℝ) ≤ Mbar) (hr : (1 : ℝ) ≤ n) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hw : ∀ i, 0 < w i) (ht : |t| ≤ 16 * n / ε) (hc : ‖c‖ ≤ 4 * U)
    (hwin : ∀ i, |Real.log (w i) -
      Real.log (gfun κ m (1 - 1 / L₀) c₀ (matrix G ER) x i)| ≤ 1 / 20)
    (hδc : cent (48 * (2 * L₀)) (matrix G ER) (barS κ m x) (barDphi κ m x) c t w ≤ 1 / 1000)
    (hs0 : ∀ i, 1 / U ≤ slk κ m x₀ i)
    {sst dp : ℝ} (hsst : sst = ε / (2 ^ 12 * n * Mbar ^ 2 * U ^ 3)) (hdp : dp = 4 * Mbar * U ^ 2)
    {wf : Sym2 (Fin n) → ℝ} {de : Fin me → ℝ} {qp : Point n me}
    {p0 : Fin n → ℝ} {β C : ℝ} (hC : 0 ≤ C)
    (hDh : ∀ i, |vec G (weights wf de) i - normD w (barS κ m x) i| ≤
      β * normD w (barS κ m x) i)
    (hqh : ∀ i, |vec G qp i - normQ t c w (barDphi κ m x) i| ≤ β) (hβ0 : 0 ≤ β)
    (hβ : β ≤ 1 / 2)
    (hp : gram (matrix G ER) (normD w (barS κ m x)) *ᵥ p0 =
      (matrix G ER)ᵀ *ᵥ fun i => normD w (barS κ m x) i * normQ t c w (barDphi κ m x) i)
    {dmin : ℝ} (hdmin : 0 < dmin) (hdpv : ∀ j, dmin ≤ de (ER.iota j)) (hwf0 : ∀ e, 0 ≤ wf e)
    {K t' R : ℕ} {δ εs : ℝ} {out : Sym2 (Fin n) → ℝ} (hgood : Sparsify.Good G wf K t' δ R out)
    (hεs0 : 0 < εs) (hεs : εs ≤ 1 / 8) (hδlo : 1 - εs ≤ (1 - δ) ^ R)
    (hδhi : (1 + δ) ^ R ≤ 1 + εs)
    {X Λ W Qz : ℝ}
    (hX : 4 * Real.sqrt (2 * rowCount G me) * Real.sqrt (rowCount G me) * dp * (64 * n * U / ε + 4 / sst + 1) /
      (sst ^ 2 / 16) ≤ X)
    (hΛ : 3 / 2 * dp * (2 * rowCount G me) ≤ Λ) (hW : ∀ e, |wf e| ≤ W) (hQz : ∀ u v, |qp.pair u v| ≤ Qz)
    {ew eq : ℤ} (hwg : ∀ e, ∃ z : ℤ, wf e = z * (2 : ℝ) ^ ew)
    (hqg : ∀ u v, ∃ z : ℤ, qp.pair u v = z * (2 : ℝ) ^ eq) (p Brhs Bmv Brep : ℕ)
    (heq : eq ≤ -(p : ℤ))
    (hB : W * (2 * (X + Real.sqrt (1 / (sst ^ 2 / 16 / 2)) *
      (Real.sqrt Λ * X + 2 * (Real.sqrt Λ * (Real.sqrt n * (1 / 2 ^ p)))))) <
        (2 : ℝ) ^ Bmv * (2 : ℝ) ^ (ew - p))
    (hBrhs : W * Qz < (2 : ℝ) ^ Brhs * (2 : ℝ) ^ (ew + eq))
    (hBrep : W * (Qz + 2 * (X + Real.sqrt (1 / (sst ^ 2 / 16 / 2)) *
      (Real.sqrt Λ * X + 2 * (Real.sqrt Λ * (Real.sqrt n * (1 / 2 ^ p)))))) <
        (2 : ℝ) ^ Brep * (2 : ℝ) ^ (ew + eq))
    (hτβ : 2 * (Real.sqrt Λ * (Real.sqrt n * (1 / 2 ^ p))) ≤ β)
    (k : ℕ) (hk : (1 / 2 : ℝ) ^ k ≤ β) :
    let A := matrix G ER
    let Dh := vec G (weights wf de)
    let D := normD w (barS κ m x)
    let q := normQ t c w (barDphi κ m x)
    let b : Fin n → ℝ := Aᵀ *ᵥ fun i => Dh i * vec G qp i
    let P := lap out univ + explicitGram A Dh (hidden G me)
    let xk := (frozenSolveProg wf ew p Bmv (explicitGram A Dh (hidden G me)) P⁻¹ b k 0).eval G.out
    let h : Fin (rowCount G me) → ℝ := fun i => -D i * (q i - (A *ᵥ p0) i)
    let ht' : Fin (rowCount G me) → ℝ := fun i => -Dh i * (vec G qp i - (A *ᵥ xk) i)
    let d := (newtonStepProg ER wf de qp out ew eq p Brhs Bmv Brep k).eval G.out
    let ℓ := sst ^ 2 / 16
    let a := Real.sqrt (2 * rowCount G me)
    let Q := 64 * n * U / ε + 4 / sst
    let Pπ := 4 * a * Real.sqrt (rowCount G me) * dp * (Q + 1) / ℓ
    let Eπ := 2 / ℓ * (a * Real.sqrt (rowCount G me) * dp * (Q + 2) + a ^ 2 * dp * Pπ) +
      (Real.sqrt (2 / ℓ) * (Real.sqrt (3 / 2 * dp) * a) * Pπ + Real.sqrt (2 / ℓ)) + Real.sqrt n
    let P₁ := dp * (Q + Real.sqrt 2 * Pπ) + 2 * dp * (1 + Real.sqrt 2 * Eπ)
    let T₀ := 1 + 2 * C * (⌈Real.sqrt n⌉₊ : ℝ)
    vec G d = repairDir A (iota G ER) ht' ∧ ‖ht' - h‖ ≤ P₁ * β ∧ Aᵀ *ᵥ vec G d = 0 ∧
      mixed C w (fun i => barS κ m x i * (vec G d - h) i) ≤
        2 * T₀ / sst * (1 + Real.sqrt 2 * rowCount G me) * P₁ * β := by
  intro A Dh D q b P xk h ht' d ℓ a Q Pπ Eπ P₁ T₀
  -- the weight and slack windows, as in `lem_numeric_query_inv`
  have hA := det_ne_zero_of_idRows (matrix_idRows G ER)
  have hwin5 : ∀ i, |Real.log (w i) -
      Real.log (gfun κ m (1 - 1 / L₀) c₀ (matrix G ER) x i)| ≤ 1 / 5 :=
    fun i => (hwin i).trans (by norm_num)
  obtain ⟨hwlo, hwhi, hwsum⟩ := weight_invariants hA hrowne hL hc₀lo hcM hMbar hr hw hwin5
  have hM1 : (1 : ℝ) ≤ rowCount G me := by
    have hr0 : 0 < n := by exact_mod_cast (show (0 : ℝ) < n by linarith)
    exact_mod_cast Fin.pos (iota G ER ⟨0, hr0⟩)
  have hMb : 0 < Mbar := by linarith
  have hc₀ : 0 ≤ c₀ := (by positivity : (0 : ℝ) ≤ 1 / (2 * Mbar)).trans hc₀lo
  have hs : ∀ i, sst ≤ slk κ m x i := fun i => by
    rw [hsst]
    exact slack_floor_note hA hrowne hL hLM hκ hc₀ hcM hU1 hU hx hx₀ hMbar hr hε hε1 hwlo hwsum ht
      hc hwin hδc hs0 i
  have hU0 : 0 < U := by linarith
  have hsst0 : 0 < sst := by rw [hsst]; positivity
  have hdp' : U ^ 2 / (1 / (4 * Mbar)) ≤ dp := by rw [hdp]; field_simp; rfl
  exact newtonStep_numeric G ER hrowA (wmin := 1 / (4 * Mbar)) hκ hx.2 hU1 hU (by positivity)
    hwlo hdp' hwhi hwsum hsst0 hs hε ht hc hC hDh hqh hβ0 hβ hp hdmin hdpv hwf0 hgood hεs0 hεs
    hδlo hδhi hX hΛ hW hQz hwg hqg p Brhs Bmv Brep heq hB hBrhs hBrep hτβ k hk


#print axioms newtonStep_numeric
#print axioms newtonStep_numeric_inv

end
end CutQueryComplexity.ImplicitLP.GenericQuery
