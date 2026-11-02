import CutQueryComplexity.TreeCutSparsifier.Basic

/-! # The discovery certificate holds for every cut -/

set_option autoImplicit false

namespace CutQueryComplexity.TreeCutSparsifier

open WeightedGraph Hierarchy Discovery DetMinCut Finset

variable {V N ι : Type} [Fintype V] [DecidableEq V]
  [Fintype N] [DecidableEq N] [Fintype ι] [DecidableEq ι]

theorem rep_empty_le_zero (H : Hier V N) (cap : N → ℝ) : H.rep cap ∅ ≤ 0 := by
  have h := H.rep_le cap (S := ∅) (ℓ := fun _ => false) (by intro v; simp)
  simpa [Hier.labelCost, Hier.toReal] using h

theorem rep_univ_le_zero (H : Hier V N) (cap : N → ℝ) : H.rep cap univ ≤ 0 := by
  have h := H.rep_le cap (S := univ) (ℓ := fun _ => true) (by intro v; simp)
  simpa [Hier.labelCost, Hier.toReal] using h

theorem restrictInl_all_cuts (G K : WeightedGraph V)
    (hKG : ∀ u v, K.w u v ≤ G.w u v) (π : V → ι) (H : Hier (V ⊕ ι) N)
    {β A e : ℝ} (hβ : 0 ≤ β)
    (hdist : ∀ S, H.rep (H.canon (auxGraph G K π)) S ≤ β * (auxGraph G K π).cut S)
    (hup : ∀ S, psi G K π S ≤ A * G.cut S + e)
    (hμ : ∀ S, ProperShore S → 2 * e ≤ psi G K π S) (S : Finset V) :
    H.restrictInl.rep (H.restrictInl.canon G) S ≤ 2 * β * A * G.cut S := by
  classical
  by_cases h0 : S = ∅
  · subst S
    simpa using rep_empty_le_zero H.restrictInl (H.restrictInl.canon G)
  by_cases h1 : S = univ
  · subst S
    simpa using rep_univ_le_zero H.restrictInl (H.restrictInl.canon G)
  have hproper : ProperShore S := ⟨Finset.nonempty_iff_ne_empty.mpr h0, h1⟩
  have hpsi : psi G K π S ≤ 2 * A * G.cut S := by
    have := hup S
    have := hμ S hproper
    linarith
  calc _ ≤ β * psi G K π S := Hier.rep_restrictInl_le G K hKG π H hdist S
    _ ≤ β * (2 * A * G.cut S) := mul_le_mul_of_nonneg_left hpsi hβ
    _ = _ := by ring

/-- A successful auxiliary cut test certifies all terminal cuts. -/
theorem certify (G K : WeightedGraph V) (hN : 2 ≤ Fintype.card V)
    (hKG : ∀ u v, K.w u v ≤ G.w u v) {m k : ℕ} (π : V → Fin m)
    (hm : m ≤ 2 * Fintype.card V + 1) {e : ℝ}
    (hup : ∀ S, psi G K π S ≤
      (1 + distortion (Fintype.card V)) * (2 * k + 1) * G.cut S + e)
    (hμ : 2 * e ≤ psiOf (auxGraph G K π) (bestShore (auxGraph G K π))) :
    let PJ := hbPkg hierarchyBound (auxGraph G K π)
    (canonicalTree ⟨PJ.m, PJ.H.restrictInl⟩ G).Good G
      (promiseB distortion (Fintype.card V) m k) := by
  intro PJ
  have hne : (properShores V).Nonempty := by
    obtain ⟨S, hS⟩ := exists_isMinCut_of_two_le_card G hN
    exact ⟨S, (mem_properShores S).mpr hS.1⟩
  obtain ⟨_, hbest⟩ := bestShore_spec (auxGraph G K π) hne
  obtain ⟨hsize, hl, _, hd⟩ := hbPkg_spec hierarchyBound (auxGraph G K π)
  simp only [Fintype.card_sum, Fintype.card_fin] at hsize hd
  refine canonicalTree_good _ G (by dsimp [PJ]; omega)
    (Hier.restrictInl_leafChildless hl) ?_
  intro S
  exact restrictInl_all_cuts G K hKG π PJ.H (by linarith [distortion_one (Fintype.card V + m)])
    hd hup (fun S hS => by
      rw [← psiOf_auxGraph]
      exact hμ.trans (hbest S hS)) S

end CutQueryComplexity.TreeCutSparsifier
