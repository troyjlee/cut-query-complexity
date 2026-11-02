import CutQueryComplexity.DirectedCertificate.Completion.Corollaries
import CutQueryComplexityChecks.AxiomAudit

/-! # Paper 3: checking the headline theorem statements

Each `check_…` theorem below restates a headline theorem of the paper word for word and
proves it by citing the library. If this file compiles, the library proves exactly these
statements. `#audit_cut_decl` and `#print axioms` then confirm that the proofs use only
Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`): no `sorry`
and no extra assumption.

Run from the root of the repository, after building the imports (see `README.md` in this
folder):

    lake env lean --trust=0 papers/P3/VerifyHeadlineTheorems.lean
-/

set_option autoImplicit false

namespace Paper3HeadlineVerification

open CutQueryComplexity Finset
open CutQueryComplexity.DirectedCertificate
open CutQueryComplexity.DirectedCertificate.Completion

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## Theorem 2: arbitrary-weight global certificates -/

theorem check_exists_uniform_certificate (G : WeightedDiGraph V) (r : V)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k < Fintype.card V) :
    ∃ Q S, Q.card ≤ budget 512 (Fintype.card V) k ∧ IsMinCutWitnessCertificate G Q S :=
  CutQueryComplexity.DirectedCertificate.Completion.exists_uniform_certificate G r hk hkn

#audit_cut_decl Paper3HeadlineVerification.check_exists_uniform_certificate
#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_uniform_certificate

theorem check_exists_weighted_global_witnessCertificate (G : WeightedDiGraph V)
    (hn : 2 ≤ Fintype.card V) :
    ∃ Q S, (Q.card : ℝ) ≤ weightedHeadlineConstant *
        (Fintype.card V : ℝ) ^ ((5 : ℝ) / 3) ∧ IsMinCutWitnessCertificate G Q S :=
  CutQueryComplexity.DirectedCertificate.Completion.exists_weighted_global_witnessCertificate G hn

#audit_cut_decl Paper3HeadlineVerification.check_exists_weighted_global_witnessCertificate
#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_weighted_global_witnessCertificate

theorem check_exists_zero_witnessCertificate (G : WeightedDiGraph V)
    (hn : 2 ≤ Fintype.card V) (h0 : G.minValue = 0) :
    ∃ S, (({S} : Finset (Finset V)).card ≤ 1) ∧ IsMinCutWitnessCertificate G {S} S :=
  CutQueryComplexity.DirectedCertificate.exists_zero_witnessCertificate G hn h0

#audit_cut_decl Paper3HeadlineVerification.check_exists_zero_witnessCertificate
#print axioms CutQueryComplexity.DirectedCertificate.exists_zero_witnessCertificate

/-! ## Theorem 3: terminal certificates -/

theorem check_exists_exact_terminal_certificate (G : WeightedDiGraph V) {s t : V}
    (hst : s ≠ t) :
    ∃ Q : Finset (Finset V), ∃ S : Finset V, ∃ lam : ℝ,
      Q.card ≤ 18 * Fintype.card V + 1 ∧ S ∈ Q ∧
      lam = terminalValue G s t ∧ 0 ≤ lam ∧
      ∀ G' : WeightedDiGraph V, Consistent G G' Q →
        s ∈ S ∧ t ∉ S ∧ G'.out S = lam ∧ terminalValue G' s t = lam ∧
        ∀ T : Finset V, s ∈ T → t ∉ T → lam ≤ G'.out T :=
  CutQueryComplexity.DirectedCertificate.Completion.exists_exact_terminal_certificate G hst

#audit_cut_decl Paper3HeadlineVerification.check_exists_exact_terminal_certificate
#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_exact_terminal_certificate

theorem check_exists_zero_terminal_certificate (G : WeightedDiGraph V) {s t : V}
    (hst : s ≠ t) (hzero : terminalValue G s t = 0) :
    ∃ S : Finset V, IsTerminalWitnessCertificate G s t {S} S ∧
      ∀ G' : WeightedDiGraph V, Consistent G G' {S} →
        G'.out S = 0 ∧ terminalValue G' s t = 0 :=
  CutQueryComplexity.DirectedCertificate.Completion.exists_zero_terminal_certificate G hst hzero

#audit_cut_decl Paper3HeadlineVerification.check_exists_zero_terminal_certificate
#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_zero_terminal_certificate

/-! ## Theorem 4: spread-sensitive refinement -/

theorem check_exists_intrinsic_paper_certificate (G : WeightedDiGraph V)
    (hn : 2 ≤ Fintype.card V) (hlam : 0 < G.minValue) :
    ∃ Q S, IsMinCutWitnessCertificate G Q S ∧
      (Q.card : ℝ) ≤ min (weightedHeadlineConstant * (Fintype.card V : ℝ) ^ ((5 : ℝ) / 3))
        (sInf {b : ℝ | ∃ t : ℝ, 0 < t ∧ t ≤ symMaximum G ∧
          b = 1000 * ((PruningData.q G t : ℝ) + (Fintype.card V : ℝ) ^ ((3 : ℝ) / 2) *
            Real.sqrt ((symMaximum G / t) * Real.log (2 * (Fintype.card V : ℝ))))}) :=
  CutQueryComplexity.DirectedCertificate.Completion.exists_intrinsic_paper_certificate G hn hlam

#audit_cut_decl Paper3HeadlineVerification.check_exists_intrinsic_paper_certificate
#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_intrinsic_paper_certificate

theorem check_exists_intrinsic_ratio_paper_certificate (G : WeightedDiGraph V)
    (hn : 2 ≤ Fintype.card V) (hlam : 0 < G.minValue) :
    ∃ Q S, IsMinCutWitnessCertificate G Q S ∧
      (Q.card : ℝ) ≤ min (weightedHeadlineConstant * (Fintype.card V : ℝ) ^ ((5 : ℝ) / 3))
        (1000 * (Fintype.card V : ℝ) ^ ((3 : ℝ) / 2) *
          Real.sqrt (symSpread G * Real.log (2 * (Fintype.card V : ℝ)))) :=
  CutQueryComplexity.DirectedCertificate.Completion.exists_intrinsic_ratio_paper_certificate G hn hlam

#audit_cut_decl Paper3HeadlineVerification.check_exists_intrinsic_ratio_paper_certificate
#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_intrinsic_ratio_paper_certificate

-- The stronger versions without `log (2n)` under the square root.
theorem check_exists_intrinsic_inf_certificate (G : WeightedDiGraph V)
    (hn : 2 ≤ Fintype.card V) (hlam : 0 < G.minValue) :
    ∃ Q S, IsMinCutWitnessCertificate G Q S ∧
      (Q.card : ℝ) ≤ min (weightedHeadlineConstant * (Fintype.card V : ℝ) ^ ((5 : ℝ) / 3))
        (sInf {b : ℝ | ∃ t : ℝ, 0 < t ∧ t ≤ symMaximum G ∧
          b = 1000 * ((PruningData.q G t : ℝ) + (Fintype.card V : ℝ) ^ ((3 : ℝ) / 2) *
            Real.sqrt (symMaximum G / t))}) :=
  CutQueryComplexity.DirectedCertificate.Completion.exists_intrinsic_inf_certificate G hn hlam

#audit_cut_decl Paper3HeadlineVerification.check_exists_intrinsic_inf_certificate
#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_intrinsic_inf_certificate

theorem check_exists_intrinsic_ratio_certificate (G : WeightedDiGraph V)
    (hn : 2 ≤ Fintype.card V) (hlam : 0 < G.minValue) :
    ∃ Q S, IsMinCutWitnessCertificate G Q S ∧
      (Q.card : ℝ) ≤ min (weightedHeadlineConstant * (Fintype.card V : ℝ) ^ ((5 : ℝ) / 3))
        (1000 * (Fintype.card V : ℝ) ^ ((3 : ℝ) / 2) * Real.sqrt (symSpread G)) :=
  CutQueryComplexity.DirectedCertificate.Completion.exists_intrinsic_ratio_certificate G hn hlam

#audit_cut_decl Paper3HeadlineVerification.check_exists_intrinsic_ratio_certificate
#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_intrinsic_ratio_certificate

/-! ## Corollary 5: unit-capacity global certificates -/

theorem check_exists_unit_paper_certificate (G : WeightedDiGraph V)
    (hn : 2 ≤ Fintype.card V) (hunit : ∀ u v, G.c u v = 0 ∨ G.c u v = 1) :
    ∃ Q S, (Q.card : ℝ) ≤ 600 * (Fintype.card V : ℝ) ^ ((3 : ℝ) / 2) *
        Real.sqrt (Real.log (2 * (Fintype.card V : ℝ))) ∧ IsMinCutWitnessCertificate G Q S :=
  CutQueryComplexity.DirectedCertificate.Completion.exists_unit_paper_certificate G hn hunit

#audit_cut_decl Paper3HeadlineVerification.check_exists_unit_paper_certificate
#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_unit_paper_certificate

-- The stronger version without `√(log (2n))`.
theorem check_exists_unit_global_certificate (G : WeightedDiGraph V)
    (hn : 2 ≤ Fintype.card V) (hunit : ∀ u v, G.c u v = 0 ∨ G.c u v = 1) :
    ∃ Q S, (Q.card : ℝ) ≤ 600 * (Fintype.card V : ℝ) ^ ((3 : ℝ) / 2) ∧
      IsMinCutWitnessCertificate G Q S :=
  CutQueryComplexity.DirectedCertificate.Completion.exists_unit_global_certificate G hn hunit

#audit_cut_decl Paper3HeadlineVerification.check_exists_unit_global_certificate
#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_unit_global_certificate

-- Library lemmas quoted in the reading guide.
#audit_cut_decl CutQueryComplexity.DirectedCertificate.IsMinCutWitnessCertificate.isGlobalMinCut
#audit_cut_decl CutQueryComplexity.DirectedCertificate.IsMinCutWitnessCertificate.isValueCertificate
#audit_cut_decl CutQueryComplexity.DirectedCertificate.Completion.IsTerminalWitnessCertificate.values
#audit_cut_decl CutQueryComplexity.DirectedCertificate.Completion.intrinsic_parameters
#print axioms CutQueryComplexity.DirectedCertificate.IsMinCutWitnessCertificate.isGlobalMinCut
#print axioms CutQueryComplexity.DirectedCertificate.IsMinCutWitnessCertificate.isValueCertificate
#print axioms CutQueryComplexity.DirectedCertificate.Completion.IsTerminalWitnessCertificate.values
#print axioms CutQueryComplexity.DirectedCertificate.Completion.intrinsic_parameters

/-! ## Small facts used in the reader

These short proofs back remarks in `README.md`. The first two show that the global and
terminal witness predicates say exactly what Definition 1 of the paper says, with the
definitions written out. The third bounds the ceiling term of Theorem 2's budget by
`3 n² / k`. The next two restate Theorem 2 (without the vertex argument `r`) and
Corollary 5 with the certificate written out, so that the unrestricted competitor `G'` is
visible. The last shows that the set under the infimum in Theorem 4 is nonempty and
bounded below, so `sInf` is the ordinary infimum. -/

theorem global_certificate_iff_paper_contract (G : WeightedDiGraph V)
    (Q : Finset (Finset V)) (S : Finset V) :
    IsMinCutWitnessCertificate G Q S ↔
      S ∈ Q ∧ S.Nonempty ∧ S ≠ univ ∧ G.out S = G.minValue ∧
      ∀ G' : WeightedDiGraph V,
        (∀ A ∈ Q, G'.out A = G.out A) →
        G'.out S = G'.minValue ∧ G'.minValue = G.minValue ∧
        ∀ T : Finset V, T.Nonempty → T ≠ univ → G'.out S ≤ G'.out T := by
  constructor
  · intro h
    have hself := h.isGlobalMinCut
    refine ⟨h.1, hself.1.1, hself.1.2, hself.out_eq_minValue, ?_⟩
    intro G' hG'
    have hother := h.2 G' hG'
    exact ⟨hother.out_eq_minValue, h.isValueCertificate G' hG',
      fun T hne hproper => hother.2 T ⟨hne, hproper⟩⟩
  · rintro ⟨hSQ, hne, hproper, _, h⟩
    exact ⟨hSQ, fun G' hG' =>
      ⟨⟨hne, hproper⟩, fun T hT => (h G' hG').2.2 T hT.1 hT.2⟩⟩

theorem terminal_certificate_iff_paper_contract (G : WeightedDiGraph V)
    (s t : V) (Q : Finset (Finset V)) (S : Finset V) :
    IsTerminalWitnessCertificate G s t Q S ↔
      S ∈ Q ∧ s ∈ S ∧ t ∉ S ∧ G.out S = terminalValue G s t ∧
      ∀ G' : WeightedDiGraph V,
        (∀ A ∈ Q, G'.out A = G.out A) →
        G'.out S = terminalValue G s t ∧
        terminalValue G' s t = terminalValue G s t ∧
        ∀ T : Finset V, s ∈ T → t ∉ T → G'.out S ≤ G'.out T := by
  constructor
  · intro h
    have hself := h.2 G (Consistent.refl G Q)
    refine ⟨h.1, hself.1, hself.2.1, hself.out_eq_terminalValue, ?_⟩
    intro G' hG'
    obtain ⟨hval, hmin⟩ := h.values G' hG'
    exact ⟨hval, hmin, (h.2 G' hG').2.2⟩
  · rintro ⟨hSQ, hs, ht, _, h⟩
    exact ⟨hSQ, fun G' hG' => ⟨hs, ht, (h G' hG').2.2⟩⟩

/-- In the range `1 ≤ k < n`, the ceiling term `n (⌈n/k⌉ + 1)` of Theorem 2's budget is at
most `3 n² / k`. -/
theorem ceiling_term_matches_paper (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n) :
    (n : ℝ) * ((ceilDiv n k : ℝ) + 1) ≤ 3 * (n : ℝ) ^ 2 / k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hknR : (k : ℝ) ≤ n := by exact_mod_cast hkn.le
  have hquotN : ceilDiv n k * k ≤ n + k :=
    (Nat.div_mul_le_self (n + k - 1) k).trans (Nat.sub_le _ _)
  have hquot : (ceilDiv n k : ℝ) * (k : ℝ) ≤ n + k := by exact_mod_cast hquotN
  apply (le_div_iff₀ hkR).mpr
  nlinarith [mul_le_mul_of_nonneg_left hquot (Nat.cast_nonneg n),
    mul_le_mul_of_nonneg_left hknR (Nat.cast_nonneg n)]

/-- Theorem 2 without the vertex argument `r` (the range `1 ≤ k < n` supplies a vertex),
with the certificate written out. -/
theorem theorem2_expanded (G : WeightedDiGraph V) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k < Fintype.card V) :
    ∃ Q : Finset (Finset V), ∃ S : Finset V,
      Q.card ≤ budget 512 (Fintype.card V) k ∧ S ∈ Q ∧
      S.Nonempty ∧ S ≠ univ ∧ G.out S = G.minValue ∧
      ∀ G' : WeightedDiGraph V,
        (∀ A ∈ Q, G'.out A = G.out A) →
        G'.out S = G'.minValue ∧ G'.minValue = G.minValue ∧
        ∀ T : Finset V, T.Nonempty → T ≠ univ → G'.out S ≤ G'.out T := by
  obtain ⟨r⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
  obtain ⟨Q, S, hQ, hcert⟩ := exists_uniform_certificate G r hk hkn
  exact ⟨Q, S, hQ, (global_certificate_iff_paper_contract G Q S).mp hcert⟩

/-- Corollary 5 with the certificate written out: the input is binary, but the competitor
`G'` is any nonnegative real-weighted graph. -/
theorem corollary5_expanded (G : WeightedDiGraph V) (hn : 2 ≤ Fintype.card V)
    (hunit : ∀ u v, G.c u v = 0 ∨ G.c u v = 1) :
    ∃ Q : Finset (Finset V), ∃ S : Finset V,
      (Q.card : ℝ) ≤ 600 * (Fintype.card V : ℝ) ^ ((3 : ℝ) / 2) *
        Real.sqrt (Real.log (2 * (Fintype.card V : ℝ))) ∧
      S ∈ Q ∧ S.Nonempty ∧ S ≠ univ ∧ G.out S = G.minValue ∧
      ∀ G' : WeightedDiGraph V,
        (∀ A ∈ Q, G'.out A = G.out A) →
        G'.out S = G'.minValue ∧ G'.minValue = G.minValue ∧
        ∀ T : Finset V, T.Nonempty → T ≠ univ → G'.out S ≤ G'.out T := by
  obtain ⟨Q, S, hQ, hcert⟩ := exists_unit_paper_certificate G hn hunit
  exact ⟨Q, S, hQ, (global_certificate_iff_paper_contract G Q S).mp hcert⟩

/-- When `λ(G) > 0`, the set under the infimum in Theorem 4 is nonempty and bounded below,
so `sInf` is the ordinary infimum. -/
theorem intrinsic_bound_set_nonempty_bddBelow (G : WeightedDiGraph V)
    (hn : 2 ≤ Fintype.card V) (hlam : 0 < G.minValue) :
    let A := {b : ℝ | ∃ t : ℝ, 0 < t ∧ t ≤ symMaximum G ∧
      b = 1000 * ((PruningData.q G t : ℝ) + (Fintype.card V : ℝ) ^ ((3 : ℝ) / 2) *
        Real.sqrt ((symMaximum G / t) * Real.log (2 * (Fintype.card V : ℝ))))}
    A.Nonempty ∧ BddBelow A := by
  dsimp only
  obtain ⟨hnu, hnuU, _, _⟩ := intrinsic_parameters G hn hlam
  constructor
  · exact ⟨_, symMaximum G, hnu.trans_le hnuU, le_rfl, rfl⟩
  · refine ⟨0, ?_⟩
    rintro _ ⟨t, _, _, rfl⟩
    positivity

#audit_cut_decl Paper3HeadlineVerification.global_certificate_iff_paper_contract
#print axioms Paper3HeadlineVerification.global_certificate_iff_paper_contract
#audit_cut_decl Paper3HeadlineVerification.terminal_certificate_iff_paper_contract
#print axioms Paper3HeadlineVerification.terminal_certificate_iff_paper_contract
#audit_cut_decl Paper3HeadlineVerification.ceiling_term_matches_paper
#print axioms Paper3HeadlineVerification.ceiling_term_matches_paper
#audit_cut_decl Paper3HeadlineVerification.theorem2_expanded
#print axioms Paper3HeadlineVerification.theorem2_expanded
#audit_cut_decl Paper3HeadlineVerification.corollary5_expanded
#print axioms Paper3HeadlineVerification.corollary5_expanded
#audit_cut_decl Paper3HeadlineVerification.intrinsic_bound_set_nonempty_bddBelow
#print axioms Paper3HeadlineVerification.intrinsic_bound_set_nonempty_bddBelow

end Paper3HeadlineVerification
