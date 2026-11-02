import CutQueryComplexity.TreeCutSparsifier.Phase
import CutQueryComplexity.Hierarchy.RackeShah.Existence
import CutQueryComplexity.DetMinCut.ParametersLogLog

/-! # A discovery phase with the Räcke–Shah hierarchy (log-log plan, M5)

The learning program of Theorem 5 (`phase`) calls the offline hierarchy selector
`hbPkg hierarchyBound` on explicit graphs, with the quadratic distortion
`distortion n = 1690 L(n)²`. This module re-instantiates it with the Räcke–Shah
hierarchy bound, distortion `distortionLL n = 268 L(n) K(n)` where `K = L ∘ L`
(`Hierarchy.RackeShah.KK`). The program `phaseLL`, the certificate `certifyLL`, the
quality `qualityLL` and the specification `phaseLL_spec` are the originals with the
hierarchy bound substituted; `phaseBudget`, `TreeData.Good` and `Correct` are reused.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CutQueryComplexity.TreeCutSparsifier

open TwoRespecting WeightedGraph Search Search.Comp Discovery Hierarchy DetMinCut Finset
open Hierarchy.RackeShah (KK rsConstant)

/-- The Räcke–Shah offline hierarchy distortion `268 L(n) L(L(n))`. -/
noncomputable def distortionLL (n : ℕ) : ℝ := rsConstant * (logL n : ℝ) * (KK n : ℝ)

theorem distortionLL_one (n : ℕ) : 1 ≤ distortionLL n := by
  have hL : (1 : ℝ) ≤ logL n := by exact_mod_cast one_le_logL' n
  have hK : (1 : ℝ) ≤ KK n := by exact_mod_cast one_le_KK' n
  have hc : (1 : ℝ) ≤ rsConstant := by norm_num [rsConstant]
  unfold distortionLL
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hc hL) hK

theorem hierarchyBoundLL : HierarchyBound distortionLL (fun n => 2 * logL n) :=
  Hierarchy.RackeShah.rackeShah_hierarchyBound

theorem distortionLL_mono : Monotone distortionLL := by
  intro m n hmn
  have hL : (logL m : ℝ) ≤ logL n := by exact_mod_cast logL_mono hmn
  have hK : (KK m : ℝ) ≤ KK n := by exact_mod_cast KK_mono hmn
  have hc : (0 : ℝ) ≤ rsConstant := by norm_num [rsConstant]
  unfold distortionLL
  gcongr

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A successful auxiliary cut test certifies all terminal cuts (Räcke–Shah hierarchy). -/
theorem certifyLL (G K : WeightedGraph V) (hN : 2 ≤ Fintype.card V)
    (hKG : ∀ u v, K.w u v ≤ G.w u v) {m k : ℕ} (π : V → Fin m)
    (hm : m ≤ 2 * Fintype.card V + 1) {e : ℝ}
    (hup : ∀ S, psi G K π S ≤
      (1 + distortionLL (Fintype.card V)) * (2 * k + 1) * G.cut S + e)
    (hμ : 2 * e ≤ psiOf (auxGraph G K π) (bestShore (auxGraph G K π))) :
    let PJ := hbPkg hierarchyBoundLL (auxGraph G K π)
    (canonicalTree ⟨PJ.m, PJ.H.restrictInl⟩ G).Good G
      (promiseB distortionLL (Fintype.card V) m k) := by
  intro PJ
  have hne : (properShores V).Nonempty := by
    obtain ⟨S, hS⟩ := exists_isMinCut_of_two_le_card G hN
    exact ⟨S, (mem_properShores S).mpr hS.1⟩
  obtain ⟨_, hbest⟩ := bestShore_spec (auxGraph G K π) hne
  obtain ⟨hsize, hl, _, hd⟩ := hbPkg_spec hierarchyBoundLL (auxGraph G K π)
  simp only [Fintype.card_sum, Fintype.card_fin] at hsize hd
  refine canonicalTree_good _ G (by dsimp [PJ]; omega)
    (Hier.restrictInl_leafChildless hl) ?_
  intro S
  exact restrictInl_all_cuts G K hKG π PJ.H (by linarith [distortionLL_one (Fintype.card V + m)])
    hd hup (fun S hS => by
      rw [← psiOf_auxGraph]
      exact hμ.trans (hbest S hS)) S

variable {W : Type} [Fintype W] [DecidableEq W]

noncomputable def qualityLL (N k : ℕ) : ℝ :=
  promiseB distortionLL N (2 * N + 1) k

def PhaseOKLL (G : WeightedGraph W) (U : ℝ) (k : ℕ) : PhaseOut W → Prop
  | .tree data => data.Good G (qualityLL (Fintype.card W) k)
  | .halve S val => ProperShore S ∧ val = G.cut S ∧ val < U / (4 * Fintype.card W)

noncomputable def phaseLL (d : W → ℝ) (U : ℝ) (k : ℕ) (v0 : W) :
    Comp (Finset W) ℝ (PhaseOut W) :=
  (residualPrep d (floorT (Fintype.card W) U) k (prepS (Fintype.card W))).bind fun K =>
  (centerSelection d K (floorT (Fintype.card W) U) k).bind fun cs =>
  let Hx := K.add (centerOf cs.C cs.rows)
  let P := hbPkg hierarchyBoundLL Hx
  let πp := P.H.part (P.H.canon Hx) (fun _ => Hx.cut_nonneg _) (cs.C ∪ {v0})
  (learnContract πp (univ.image πp)).bind fun Q =>
  let J := auxOf Q K (fun x => d x - K.degree x) πp
  if 4 * Fintype.card W * floorT (Fintype.card W) U ≤ psiOf J (bestShore J) then
    let PJ := hbPkg hierarchyBoundLL J
    (learnTree ⟨PJ.m, PJ.H.restrictInl⟩).map PhaseOut.tree
  else (ask (bestShore J)).map (PhaseOut.halve (bestShore J))

theorem phaseLL_spec (G : WeightedGraph W) (hN : 3 ≤ Fintype.card W) {U : ℝ} (hU : 0 < U)
    (hdeg : ∀ v, G.degree v ≤ ((Fintype.card W : ℝ) - 1) * U) {k : ℕ} (hk2 : 2 ≤ k)
    (hkN : k ≤ 8 * Fintype.card W) (v0 : W) :
    PhaseOKLL G U k ((phaseLL G.degree U k v0).eval G.cut) ∧
      (phaseLL G.degree U k v0).cost G.cut ≤ phaseBudget (Fintype.card W) k := by
  have : Nonempty W := ⟨v0⟩
  have hk0 : 0 < k := by omega
  obtain ⟨hKex, hlight, hKcost⟩ := residualPrep_normalized G hU hk0 hdeg
  simp only [phaseLL, floorT, prepS, eval_bind, cost_bind]
  set N := Fintype.card W with hNdef
  set t := U / (16 * (N : ℝ) ^ 2) with htdef
  set K := (residualPrep G.degree t k (4 + 3 * Nat.clog 2 N)).eval G.cut with hKdef
  have hKG : ∀ u v, K.w u v ≤ G.w u v := fun u v => by
    rcases hKex u v with h0 | h0 <;> rw [h0]; exact G.nonneg u v
  obtain ⟨hCcard, hrows, hcov, hCcost⟩ := centerSelection_normalized G K hKG hU hk2 hkN hdeg hlight
  simp only [← hNdef] at hCcard hrows hcov hCcost
  simp only [← htdef] at hCcard hrows hcov hCcost
  set cs := (centerSelection G.degree K t k).eval G.cut with hcsdef
  set Hx := K.add (centerOf cs.C cs.rows) with hHxdef
  have hHx : Hx = K.add (centerGraph (G.subtract K) cs.C) := by rw [hHxdef, centerOf_eq _ hrows]
  obtain ⟨hPm, -, -, hPdist⟩ := hbPkg_spec hierarchyBoundLL Hx
  simp only [← hNdef] at hPm hPdist
  set P := hbPkg hierarchyBoundLL Hx with hPdef
  set C0 := cs.C ∪ {v0} with hC0
  set πp := P.H.part (P.H.canon Hx) (fun _ => Hx.cut_nonneg _) C0 with hπp
  have hQ := learnContract_eval G πp (img := univ.image πp)
    (fun v => mem_image_of_mem _ (mem_univ v))
  set Q := (learnContract πp (univ.image πp)).eval G.cut with hQdef
  have hJ : auxOf Q K (fun x => G.degree x - K.degree x) πp = auxGraph G K πp := by
    rw [hQ]; exact auxOf_eq G K hKG πp
  have ht0 : 0 ≤ t := by positivity
  have hup : ∀ S, psi G K πp S ≤ (1 + distortionLL N) * (2 * k + 1) * G.cut S + 2 * N * t := by
    intro S
    obtain ⟨T, hagree, hround0⟩ := Hier.exists_rounding P.H Hx hPdist C0 S
    have hround1 : Hx.cut (pull πp T) ≤ distortionLL N * Hx.cut S := hround0
    have hround : (K.add (centerGraph (G.subtract K) cs.C)).cut (pull πp T) ≤
        distortionLL N * (K.add (centerGraph (G.subtract K) cs.C)).cut S := by
      rw [← hHx]; exact hround1
    have hagree' : pull πp T ∩ cs.C = S ∩ cs.C := by
      have hsub : cs.C ⊆ C0 := subset_union_left
      calc pull πp T ∩ cs.C = (pull πp T ∩ C0) ∩ cs.C := by rw [inter_assoc, inter_eq_right.mpr hsub]
        _ = (S ∩ C0) ∩ cs.C := by rw [hagree]
        _ = S ∩ cs.C := by rw [inter_assoc, inter_eq_right.mpr hsub]
    have hα : 0 ≤ distortionLL N := by linarith [distortionLL_one N]
    have hcov' : ∀ v ∉ cs.C, (G.subtract K).degree v ≤ t ∨
        (G.subtract K).degree v / k ≤ ∑ c ∈ cs.C, (G.subtract K).w v c := hcov
    have := psi_upper (ι := Fin P.m) G K hKG πp (C := cs.C) (S := S) (T := T) hagree' (t := t)
      ht0 (k := k) hk0 hcov' (α := distortionLL N) hα hround
    exact this
  rw [hJ]
  simp only [← htdef]
  -- the query cost before the test
  have hne : (properShores W).Nonempty := by
    exact ⟨{v0}, (mem_properShores _).mpr (properShore_singleton v0 (by omega))⟩
  have himg : (univ.image πp).card ≤ 2 * (selectionBudget N k + 1) := by
    have h1 := Hier.card_image_part_le P.H (P.H.canon Hx) (fun _ => Hx.cut_nonneg _) C0
    have h2 : C0.card ≤ cs.C.card + 1 := (card_union_le _ _).trans (by simp)
    have h3 : max 1 (2 * C0.card - 2) ≤ 2 * (selectionBudget N k + 1) :=
      max_le (by omega) (by omega)
    exact h1.trans h3
  have hlearn := learnContract_cost G πp (univ.image πp)
  have himgN : (univ.image πp).card ≤ N := by
    exact card_image_le.trans (by simp [N])
  have hlearn' : (learnContract πp (univ.image πp)).cost G.cut ≤
      (N + 1) * (2 * (selectionBudget N k + 1)) := by
    have hp := Nat.mul_le_mul_right (univ.image πp).card himgN
    have hs := Nat.mul_le_mul_left (N + 1) himg
    nlinarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h4Nt : 4 * (N : ℝ) * t = U / (4 * N) := by
    simp only [htdef]; field_simp; ring
  by_cases hc : 4 * (N : ℝ) * t ≤ psiOf (auxGraph G K πp) (bestShore (auxGraph G K πp))
  · rw [ite_eq_left hc]
    simp only [eval_map, cost_map, PhaseOKLL, learnTree_eval, learnTree_cost]
    have hgood := certifyLL G K (by omega) hKG πp hPm (k := k) hup (by linarith)
    have hqual : promiseB distortionLL N P.m k ≤ qualityLL N k := by
      have hm' : N + P.m ≤ N + (2 * N + 1) := by omega
      have hm'' := distortionLL_mono hm'
      have hA : 0 ≤ (1 + distortionLL N) * (2 * k + 1) := by
        have := distortionLL_one N
        positivity
      simp only [qualityLL, promiseB]
      nlinarith
    refine ⟨hgood.mono hqual, ?_⟩
    have hmJ := (hbPkg_spec hierarchyBoundLL (auxGraph G K πp)).1
    simp only [Fintype.card_sum, Fintype.card_fin, ← hNdef] at hmJ
    have hmJ' : (hbPkg hierarchyBoundLL (auxGraph G K πp)).m ≤ 8 * N := by omega
    unfold phaseBudget
    simp only [prepS]
    omega
  · rw [ite_eq_right hc]
    simp only [eval_map, cost_map, eval_ask, cost_ask, PhaseOKLL]
    obtain ⟨hprop, _⟩ := bestShore_spec (auxGraph G K πp) hne
    refine ⟨⟨hprop, by trivial, ?_⟩, ?_⟩
    · push Not at hc
      have h1 := psi_lower G K hKG πp (bestShore (auxGraph G K πp))
      rw [← psiOf_auxGraph] at h1
      rw [← h4Nt]
      exact lt_of_le_of_lt h1 hc
    · unfold phaseBudget
      simp only [prepS]
      omega

end CutQueryComplexity.TreeCutSparsifier
