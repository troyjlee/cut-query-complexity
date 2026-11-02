import CutQueryComplexity.TreeCutSparsifier.Certification

/-! # A discovery phase returning an explicit tree -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CutQueryComplexity.TreeCutSparsifier

open TwoRespecting WeightedGraph Search Search.Comp Discovery Hierarchy DetMinCut Finset

variable {W : Type} [Fintype W] [DecidableEq W]

inductive PhaseOut (W : Type)
  | tree (data : TreeData W)
  | halve (S : Finset W) (val : ℝ)

noncomputable def quality (N k : ℕ) : ℝ :=
  promiseB distortion N (2 * N + 1) k

def PhaseOK (G : WeightedGraph W) (U : ℝ) (k : ℕ) : PhaseOut W → Prop
  | .tree data => data.Good G (quality (Fintype.card W) k)
  | .halve S val => ProperShore S ∧ val = G.cut S ∧ val < U / (4 * Fintype.card W)

noncomputable def phase (d : W → ℝ) (U : ℝ) (k : ℕ) (v0 : W) :
    Comp (Finset W) ℝ (PhaseOut W) :=
  (residualPrep d (floorT (Fintype.card W) U) k (prepS (Fintype.card W))).bind fun K =>
  (centerSelection d K (floorT (Fintype.card W) U) k).bind fun cs =>
  let Hx := K.add (centerOf cs.C cs.rows)
  let P := hbPkg hierarchyBound Hx
  let πp := P.H.part (P.H.canon Hx) (fun _ => Hx.cut_nonneg _) (cs.C ∪ {v0})
  (learnContract πp (univ.image πp)).bind fun Q =>
  let J := auxOf Q K (fun x => d x - K.degree x) πp
  if 4 * Fintype.card W * floorT (Fintype.card W) U ≤ psiOf J (bestShore J) then
    let PJ := hbPkg hierarchyBound J
    (learnTree ⟨PJ.m, PJ.H.restrictInl⟩).map PhaseOut.tree
  else (ask (bestShore J)).map (PhaseOut.halve (bestShore J))

/-- The quotient-learning term uses both bounds on the number of parts. -/
noncomputable def phaseBudget (N k : ℕ) : ℕ :=
  N * prepS N * (4 * k * Nat.clog 2 (N - 1)) +
    selectionBudget N k * (6 * (6 + 3 * Nat.clog 2 N) * (Nat.clog 2 N + 1) + (N - 1)) +
    (N + 1) * (2 * (selectionBudget N k + 1)) + 8 * N + 1

theorem phase_spec (G : WeightedGraph W) (hN : 3 ≤ Fintype.card W) {U : ℝ} (hU : 0 < U)
    (hdeg : ∀ v, G.degree v ≤ ((Fintype.card W : ℝ) - 1) * U) {k : ℕ} (hk2 : 2 ≤ k)
    (hkN : k ≤ 8 * Fintype.card W) (v0 : W) :
    PhaseOK G U k ((phase G.degree U k v0).eval G.cut) ∧
      (phase G.degree U k v0).cost G.cut ≤ phaseBudget (Fintype.card W) k := by
  have : Nonempty W := ⟨v0⟩
  have hk0 : 0 < k := by omega
  obtain ⟨hKex, hlight, hKcost⟩ := residualPrep_normalized G hU hk0 hdeg
  simp only [phase, floorT, prepS, eval_bind, cost_bind]
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
  obtain ⟨hPm, -, -, hPdist⟩ := hbPkg_spec hierarchyBound Hx
  simp only [← hNdef] at hPm hPdist
  set P := hbPkg hierarchyBound Hx with hPdef
  set C0 := cs.C ∪ {v0} with hC0
  set πp := P.H.part (P.H.canon Hx) (fun _ => Hx.cut_nonneg _) C0 with hπp
  have hQ := learnContract_eval G πp (img := univ.image πp)
    (fun v => mem_image_of_mem _ (mem_univ v))
  set Q := (learnContract πp (univ.image πp)).eval G.cut with hQdef
  have hJ : auxOf Q K (fun x => G.degree x - K.degree x) πp = auxGraph G K πp := by
    rw [hQ]; exact auxOf_eq G K hKG πp
  have ht0 : 0 ≤ t := by positivity
  have hup : ∀ S, psi G K πp S ≤ (1 + distortion N) * (2 * k + 1) * G.cut S + 2 * N * t := by
    intro S
    obtain ⟨T, hagree, hround0⟩ := Hier.exists_rounding P.H Hx hPdist C0 S
    have hround1 : Hx.cut (pull πp T) ≤ distortion N * Hx.cut S := hround0
    have hround : (K.add (centerGraph (G.subtract K) cs.C)).cut (pull πp T) ≤
        distortion N * (K.add (centerGraph (G.subtract K) cs.C)).cut S := by
      rw [← hHx]; exact hround1
    have hagree' : pull πp T ∩ cs.C = S ∩ cs.C := by
      have hsub : cs.C ⊆ C0 := subset_union_left
      calc pull πp T ∩ cs.C = (pull πp T ∩ C0) ∩ cs.C := by rw [inter_assoc, inter_eq_right.mpr hsub]
        _ = (S ∩ C0) ∩ cs.C := by rw [hagree]
        _ = S ∩ cs.C := by rw [inter_assoc, inter_eq_right.mpr hsub]
    have hα : 0 ≤ distortion N := by linarith [distortion_one N]
    have hcov' : ∀ v ∉ cs.C, (G.subtract K).degree v ≤ t ∨
        (G.subtract K).degree v / k ≤ ∑ c ∈ cs.C, (G.subtract K).w v c := hcov
    have := psi_upper (ι := Fin P.m) G K hKG πp (C := cs.C) (S := S) (T := T) hagree' (t := t)
      ht0 (k := k) hk0 hcov' (α := distortion N) hα hround
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
    simp only [eval_map, cost_map, PhaseOK, learnTree_eval, learnTree_cost]
    have hgood := certify G K (by omega) hKG πp hPm (k := k) hup (by linarith)
    have hqual : promiseB distortion N P.m k ≤ quality N k := by
      have hm' : N + P.m ≤ N + (2 * N + 1) := by omega
      have hm'' := distortion_mono hm'
      have hA : 0 ≤ (1 + distortion N) * (2 * k + 1) := by
        have := distortion_one N
        positivity
      simp only [quality, promiseB]
      nlinarith
    refine ⟨hgood.mono hqual, ?_⟩
    have hmJ := (hbPkg_spec hierarchyBound (auxGraph G K πp)).1
    simp only [Fintype.card_sum, Fintype.card_fin, ← hNdef] at hmJ
    have hmJ' : (hbPkg hierarchyBound (auxGraph G K πp)).m ≤ 8 * N := by omega
    unfold phaseBudget
    simp only [prepS]
    omega
  · rw [ite_eq_right hc]
    simp only [eval_map, cost_map, eval_ask, cost_ask, PhaseOK]
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
