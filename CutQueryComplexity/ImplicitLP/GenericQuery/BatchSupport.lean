import CutQueryComplexity.ImplicitLP.GenericQuery.Support
import CutQueryComplexity.ImplicitLP.GenericQuery.PointOps

/-! # Certified support inside a general batch

Public clipping bounds absent pairs and every dishonest branch. On successful
states it preserves the actual row values. The executed certified support call
supplies the analytic batch's ball, sign and optimization conclusions.
-/

set_option autoImplicit false
namespace CutQueryComplexity.ImplicitLP.GenericQuery
open Matrix Finset Real Set
noncomputable section
variable {n me : ℕ} (G : DiGraph (Fin n))

structure PathState (n me : ℕ) where
  x : Point n me
  X : Point n me
  z : Point n me

theorem support_envelopes (qp wp : Point n me) {C Cs Q wmin Mbar σ : ℝ} (hC : 0 < C)
    (hCs : 0 < Cs) (hwmin : 0 < wmin) (hQ : 0 ≤ Q)
    (hq : ∀ i, |vec G qp i| ≤ Q) (hw : ∀ i, wmin ≤ vec G wp i)
    (hqe : ∀ e, |pairOf qp.pair e| ≤ Q) (hwe : ∀ e, wmin ≤ pairOf wp.pair e)
    (hMbar : (rowCount G me : ℝ) ≤ Mbar) :
    let S := envSup Mbar Q wmin C Cs σ
    euc (fun i => Cs * vec G qp i / (C * Real.sqrt (vec G wp i))) ≤ S.Ap ∧
    max (euc (fun i => Cs * vec G qp i / (C * Real.sqrt (vec G wp i))))
      (∑ i, |Cs * vec G qp i / (C * Real.sqrt (vec G wp i))| *
        (C * Real.sqrt (vec G wp i))) ≤ S.Lb ∧
    ∑ i, |vec G qp i| ≤ S.Sq ∧
    (∀ e, |Cs * pairOf qp.pair e / (C * Real.sqrt (pairOf wp.pair e))| ≤ S.Abar) ∧
    (rowCount G me : ℝ) ≤ S.Mbar := by
  intro S
  have hAb0 : 0 ≤ Cs * Q / (C * Real.sqrt wmin) := by positivity
  have hcoef := fun i => abs_coef_le hC hCs hwmin (hq i) (hw i)
  have hA : euc (fun i => Cs * vec G qp i / (C * Real.sqrt (vec G wp i))) ≤ S.Ap :=
    euc_le_of_abs hcoef hAb0 hMbar
  have hM0 : (0 : ℝ) ≤ rowCount G me := Nat.cast_nonneg _
  have hSq : ∑ i, |vec G qp i| ≤ S.Sq := by
    calc ∑ i, |vec G qp i| ≤ ∑ _i : Fin (rowCount G me), Q := sum_le_sum fun i _ => hq i
      _ = (rowCount G me : ℝ) * Q := by simp
      _ ≤ Mbar * Q := mul_le_mul_of_nonneg_right hMbar hQ
  have hκ : ∀ i, |Cs * vec G qp i / (C * Real.sqrt (vec G wp i))| *
      (C * Real.sqrt (vec G wp i)) = Cs * |vec G qp i| := fun i => by
    have hpos : 0 < C * Real.sqrt (vec G wp i) :=
      mul_pos hC (Real.sqrt_pos.mpr (hwmin.trans_le (hw i)))
    rw [abs_div, abs_mul, abs_of_pos hCs, abs_of_pos hpos, div_mul_cancel₀ _ hpos.ne']
  refine ⟨hA, max_le (hA.trans (le_max_left _ _)) ?_, hSq, fun e => ?_, hMbar⟩
  · simp_rw [hκ]
    rw [← mul_sum]
    exact (mul_le_mul_of_nonneg_left hSq hCs.le).trans (le_max_right _ _)
  · exact abs_coef_le hC hCs hwmin (hqe e) (hwe e)

/-- **The public support step at the envelopes.** Run the public support oracle on the clipped
points `q° = clip_{[−Q,Q]} q`, `w° = max(w_min, w)`. If the actual rows obey `|qᵢ| ≤ Q` and
`wᵢ ≥ w_min`, then on the actual rows the data are the original `q`, `w` and the output point `v`
is dyadic, in the ball `{N_w ≤ C_*}`, sign-aligned with `q`, `σ`-optimal; budget
`(2N + 2)(m + 3)·6Bn` with the public parameters of `envSup`. -/
theorem supportPub_env (qp wp : Point n me) {C Cs Q wmin Mbar σ : ℝ} (hC : 0 < C)
    (hCs : 0 < Cs) (hwmin : 0 < wmin) (hQ : 0 ≤ Q) (hσ : 0 < σ)
    (hq : ∀ i, |vec G qp i| ≤ Q) (hw : ∀ i, wmin ≤ vec G wp i)
    (hMbar : (rowCount G me : ℝ) ≤ Mbar) :
    let S := envSup Mbar Q wmin C Cs σ
    let q := vec G qp
    let w := vec G wp
    let prog := supportPubProg C Cs S.ρ (clipQPt Q qp) (clipWPt wmin wp) S.Mbar S.Ap S.h S.p
      S.B S.m S.N S.kτ S.kl S.kc S.po
    let v := vec G (prog.eval G.out).2
    (∀ i, ∃ m : ℤ, v i = m / 2 ^ S.po) ∧ mixed C w v ≤ Cs ∧ (∀ i, 0 ≤ q i * v i) ∧
      (∀ v₀, mixed C w v₀ ≤ Cs → q ⬝ᵥ v₀ ≤ q ⬝ᵥ v + σ) ∧
      prog.cost G.out ≤ (2 * S.N + 2) * ((S.m + 3) * (6 * S.B * n)) := by
  intro S q w prog v
  have eq := vec_clipQPt G qp hq
  have ew := vec_clipWPt G wp hw
  have hq' : ∀ i, |vec G (clipQPt Q qp) i| ≤ Q := by rw [eq]; exact hq
  have hw' : ∀ i, wmin ≤ vec G (clipWPt wmin wp) i := by rw [ew]; exact hw
  have hqe : ∀ e, |pairOf (clipQPt Q qp).pair e| ≤ Q := fun e => by
    rw [clipQPt, pairOf_mapPt]; exact abs_clipTo_le hQ _
  have hwe : ∀ e, wmin ≤ pairOf (clipWPt wmin wp).pair e := fun e => by
    rw [clipWPt, pairOf_mapPt]; exact le_max_left _ _
  obtain ⟨hA, hL, hSq, hAb, hMb⟩ := support_envelopes (σ := σ) G (clipQPt Q qp) (clipWPt wmin wp)
    hC hCs hwmin hQ hq' hw' hqe hwe hMbar
  have hwpos : ∀ i, 0 < vec G (clipWPt wmin wp) i := fun i => hwmin.trans_le (hw' i)
  have h := supportPub_public G S (clipQPt Q qp) (clipWPt wmin wp) hC hCs hwpos hσ hA hL hSq hAb
    hMb
  simp only [eq, ew] at h
  exact h

theorem batch_support_public {r : ℕ}
    {A : Matrix (Fin (rowCount G me)) (Fin r) ℝ} {b : Fin r → ℝ} {κ m c : Fin (rowCount G me) → ℝ} {t : ℝ}
    (st : PathState n me) {x X z : Fin (rowCount G me) → ℝ}
    (hXst : vec G st.X = X) (hzst : vec G st.z = z)
    (hA : (Aᵀ * A).det ≠ 0) (hrow : ∀ i, A i ≠ 0) {L₀ : ℝ} (hL : 2 ≤ L₀)
    (hLM : Real.logb 2 (2 * rowCount G me) ≤ L₀ - 1) (hκ : ∀ i, 0 < κ i) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hcM : c₀ ≤ 1 / (2 * rowCount G me)) (hM : 1 ≤ rowCount G me) (hx : x ∈ Feasible A b κ m)
    {Δ K η T₀ Mbar : ℝ} (hΔ0 : 0 < Δ) (hΔ : Δ ≤ (1 / (2 * L₀)) ^ 2 / 2 ^ 16)
    (hK0 : 0 ≤ K) (hK : K ≤ 1 / (2 * L₀) / 2 ^ 20) (hη0 : 0 ≤ η)
    (hη : η ≤ 1 / (2 * L₀) * Δ / 2 ^ 16) (hT₀ : 1 ≤ T₀)
    (hT : ∀ v, mixed (48 * (2 * L₀)) (fun i => exp (X i)) v ≤ T₀ * ‖v‖)
    (hKμ : Real.log (12 * rowCount G me * T₀ / (1 / (2 * L₀) / 8)) /
      ((1 / (2 * L₀) / 8) / (12 * Δ)) ≤ K)
    (hpot : pot ((1 / (2 * L₀) / 8) / (12 * Δ))
      (X - fun i => Real.log (gfun κ m (1 - 1 / L₀) c₀ A x i)) ≤
        12 * rowCount G me * T₀ / (1 / (2 * L₀) / 8))
    (hδ : cent (48 * (2 * L₀)) A (barS κ m x) (barDphi κ m x) c t (fun i => exp (X i)) ≤ Δ)
    {e : Fin (rowCount G me) → ℝ} (hAe : Aᵀ *ᵥ e = 0)
    (he : mixed (48 * (2 * L₀)) (fun i => exp (X i)) (fun i => barS κ m x i * e i) ≤ η)
    (hz : ∀ i, |z i - Real.log (gfun κ m (1 - 1 / L₀) c₀ A
      (x + (newtonDir A (fun i => exp (X i)) (barS κ m x)
        (fun i => t * c i + exp (X i) * barDphi κ m x i) + e)) i)| ≤ Δ)
    (hMbar : (rowCount G me : ℝ) ≤ Mbar) :
    let ξ : ℝ := 1 / (2 * L₀) / 8
    let μ : ℝ := ξ / (12 * Δ)
    let C : ℝ := 48 * (2 * L₀)
    let Cs : ℝ := (1 - 3 * (1 / (2 * L₀)) / 4) * Δ
    let σ : ℝ := ξ / 1000
    let Q : ℝ := 2 * μ * (12 * Mbar * T₀ / ξ)
    let wmin : ℝ := 4 / 5 * c₀
    let S := envSup Mbar Q wmin C Cs σ
    let prog := supportPubProg C Cs S.ρ (clipQPt Q (gradPt μ st.X st.z))
      (clipWPt wmin (wPt st.X)) S.Mbar S.Ap S.h S.p S.B S.m S.N S.kτ S.kl S.kc S.po
    let v := vec G (prog.eval G.out).2
    let w : Fin (rowCount G me) → ℝ := fun i => exp (X i)
    let x' := x + (newtonDir A w (barS κ m x) (fun i => t * c i + w i * barDphi κ m x i) + e)
    let X' := X - (1 + ξ) • v
    (∀ i, ∃ k : ℤ, v i = k / 2 ^ S.po) ∧
      prog.cost G.out ≤ (2 * S.N + 2) * ((S.m + 3) * (6 * S.B * n)) ∧
      x' ∈ Feasible A b κ m ∧
      pot μ (X' - fun i => Real.log (gfun κ m (1 - 1 / L₀) c₀ A x' i)) ≤
        12 * rowCount G me * T₀ / ξ ∧
      cent C A (barS κ m x') (barDphi κ m x') c t (fun i => exp (X' i)) ≤
        (1 - 1 / (2 * L₀) / 2) * Δ := by
  intro ξ μ C Cs σ Q wmin S prog v w x' X'
  have hL0 : 0 < L₀ := by linarith
  have ha0 : 0 < 1 / (2 * L₀) := by positivity
  have ha4 : 1 / (2 * L₀) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hξ0 : 0 < ξ := by positivity
  have hμ0 : 0 < μ := by positivity
  have hC : 0 < C := by positivity
  have hCs : 0 < Cs := by
    have : 0 < 1 - 3 * (1 / (2 * L₀)) / 4 := by linarith
    positivity
  have hσ0 : 0 < σ := by positivity
  have hwmin : 0 < wmin := by positivity
  have hM0 : (0 : ℝ) ≤ rowCount G me := Nat.cast_nonneg _
  have hQ : 0 ≤ Q := by
    have : 0 ≤ Mbar := hM0.trans hMbar
    have : 0 ≤ T₀ := by linarith
    positivity
  obtain ⟨hqb, hwb⟩ := batch_support_inputs hA hrow hL hLM hκ hc₀.le hcM hx hΔ0 hΔ hK0 hK hη0
    hη hKμ hpot hδ hAe he hz
  have hq : ∀ i, |vec G (gradPt μ st.X st.z) i| ≤ Q := fun i => by
    rw [vec_gradPt, hXst, hzst]
    refine (hqb i).trans ?_
    have : 12 * (rowCount G me : ℝ) * T₀ / ξ ≤ 12 * Mbar * T₀ / ξ := by
      gcongr
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hw : ∀ i, wmin ≤ vec G (wPt st.X) i := fun i => by
    rw [vec_wPt, hXst]; exact hwb i
  obtain ⟨hdy, hball, hal, hopt, hcost⟩ :=
    supportPub_env G (gradPt μ st.X st.z) (wPt st.X) hC hCs hwmin hQ hσ0 hq hw hMbar
  rw [vec_gradPt, hXst, hzst] at hal hopt
  rw [vec_wPt, hXst] at hball hopt
  obtain ⟨hv, hal', hopt'⟩ := support_batch_form (C := C) hCs.le hμ0 hball hal hopt
  refine ⟨hdy, hcost, ?_⟩
  exact prop_batch hA hrow hL hLM hκ hc₀.le hcM hM hx hΔ0 hΔ hK0 hK hη0 hη hT₀ hT hKμ hpot hδ
    hAe he hz hv hal' hσ0.le le_rfl hopt'

#print axioms support_envelopes
#print axioms supportPub_env
#print axioms batch_support_public

end
end CutQueryComplexity.ImplicitLP.GenericQuery
