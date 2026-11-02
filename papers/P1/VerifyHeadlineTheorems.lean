import CutQueryComplexity.AllMinCuts.Endpoint
import CutQueryComplexity.AllMinCuts.Conversion
import CutQueryComplexity.Certificate.Main
import CutQueryComplexity.Certificate.TreePattern.Main
import CutQueryComplexityChecks.AxiomAudit

/-! # Paper 1: checking the headline theorem statements

Each `check_…` theorem below restates a headline theorem of the paper word for word and
proves it by citing the library. If this file compiles, the library proves exactly these
statements. `#audit_cut_decl` and `#print axioms` then confirm that the proofs use only
Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`): no `sorry`
and no extra assumption.

Run from the root of the repository, after building the imports (see `README.md` in this
folder):

    lake env lean --trust=0 papers/P1/VerifyHeadlineTheorems.lean
-/

set_option autoImplicit false
namespace Paper1HeadlineVerification
open CutQueryComplexity

namespace CertificateChecks
open CutQueryComplexity.Certificate
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem check_exists_minCut_witnessCertificate (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V) :
    ∃ Q S, Q.card ≤ 18 * Fintype.card V * (Nat.clog 2 (2 * Fintype.card V)) ^ 2 ∧
      IsMinCutWitnessCertificate G Q S :=
  CutQueryComplexity.Certificate.exists_minCut_witnessCertificate G hn

#audit_cut_decl Paper1HeadlineVerification.CertificateChecks.check_exists_minCut_witnessCertificate
#print axioms CutQueryComplexity.Certificate.exists_minCut_witnessCertificate

theorem check_exists_minCut_value_certificate :
    ∃ C : ℕ, ∀ n (G : WeightedGraph (Fin n)), 2 ≤ n →
      ∃ Q, Q.card ≤ C * n * (Nat.clog 2 (2 * n)) ^ 2 ∧ IsMinCutCertificate G Q :=
  CutQueryComplexity.Certificate.exists_minCut_value_certificate

#audit_cut_decl Paper1HeadlineVerification.CertificateChecks.check_exists_minCut_value_certificate
#print axioms CutQueryComplexity.Certificate.exists_minCut_value_certificate

theorem check_certificateComplexity_le_bound (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V) :
    certificateComplexity G ≤ 18 * Fintype.card V * (Nat.clog 2 (2 * Fintype.card V)) ^ 2 :=
  CutQueryComplexity.Certificate.certificateComplexity_le_bound G hn

#audit_cut_decl Paper1HeadlineVerification.CertificateChecks.check_certificateComplexity_le_bound
#print axioms CutQueryComplexity.Certificate.certificateComplexity_le_bound

theorem check_certificateComplexity_eq_one (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V)
    (h0 : mincutValue G = 0) : certificateComplexity G = 1 :=
  CutQueryComplexity.Certificate.certificateComplexity_eq_one G hn h0

#audit_cut_decl Paper1HeadlineVerification.CertificateChecks.check_certificateComplexity_eq_one
#print axioms CutQueryComplexity.Certificate.certificateComplexity_eq_one

end CertificateChecks

namespace AllCutChecks
open CutQueryComplexity.AllMinCuts

theorem check_deterministic_all_mincuts_log3loglog2 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ q : ℕ, (q : ℝ) ≤ C * (n : ℝ) * (Nat.sqrt n + 1) *
          ((DetMinCut.logL n : ℝ) ^ 3 *
            (DetMinCut.logL (DetMinCut.logL n) : ℝ) ^ 2) ∧
        ∃ D : DTree (Finset (Fin n)) ℝ (Option (Output (Fin n))) q,
          (∀ read, D.cost read ≤ q) ∧
          ∀ G : WeightedGraph (Fin n), ∃ out,
            D.eval G.cut = some out ∧ Correct G out :=
  CutQueryComplexity.AllMinCuts.deterministic_all_mincuts_log3loglog2

#audit_cut_decl Paper1HeadlineVerification.AllCutChecks.check_deterministic_all_mincuts_log3loglog2
#print axioms CutQueryComplexity.AllMinCuts.deterministic_all_mincuts_log3loglog2

theorem check_deterministic_all_mincuts_log3loglog2_real_log :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ q : ℕ, (q : ℝ) ≤ C * (n : ℝ) * (Nat.sqrt n + 1) *
          (Real.log (2 * (n : ℝ)) ^ 3 * Real.log (6 * Real.log (2 * (n : ℝ))) ^ 2) ∧
        ∃ D : DTree (Finset (Fin n)) ℝ (Option (Output (Fin n))) q,
          (∀ read, D.cost read ≤ q) ∧
          ∀ G : WeightedGraph (Fin n), ∃ out,
            D.eval G.cut = some out ∧ Correct G out :=
  CutQueryComplexity.AllMinCuts.deterministic_all_mincuts_log3loglog2_real_log

#audit_cut_decl Paper1HeadlineVerification.AllCutChecks.check_deterministic_all_mincuts_log3loglog2_real_log
#print axioms CutQueryComplexity.AllMinCuts.deterministic_all_mincuts_log3loglog2_real_log

end AllCutChecks

namespace ConversionChecks
open CutQueryComplexity.AllMinCuts
open CutQueryComplexity.DetMinCut CutQueryComplexity.TreeCutSparsifier

theorem check_exists_conversion_allMinCuts :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (input : TreeData (Fin n)) (B : ℝ), 2 ≤ n → 1 ≤ B →
      ∃ q : ℕ, (q : ℝ) ≤ C * n * B * ((logL n : ℝ) ^ 3 * (logL (logL n) : ℝ) ^ 2) ∧
        ∃ D : DTree (Finset (Fin n)) ℝ (Option (WeightedGraph (Fin n))) q,
          (∀ read, D.cost read ≤ q) ∧
          ∀ G : WeightedGraph (Fin n), 0 < mincutValue G → input.Approximates G B →
            ∃ F, D.eval G.cut = some F ∧ AllMinCutSkeleton G F :=
  CutQueryComplexity.AllMinCuts.exists_conversion_allMinCuts

#audit_cut_decl Paper1HeadlineVerification.ConversionChecks.check_exists_conversion_allMinCuts
#print axioms CutQueryComplexity.AllMinCuts.exists_conversion_allMinCuts

end ConversionChecks

namespace DiscoveryChecks
open CutQueryComplexity.TreeCutSparsifier

theorem check_theorem5LL :
    ∃ C Cq : ℝ, 0 < C ∧ 0 < Cq ∧
      ∀ n : ℕ, 2 ≤ n → ∀ α : ℝ,
        C * ((Real.log (2 * (n : ℝ)))^2 * (Real.log (6 * Real.log (2 * (n : ℝ))))^2) ≤ α →
        α ≤ Real.sqrt n →
      ∃ q : ℕ, (q : ℝ) ≤ Cq * ((n : ℝ)^2 / α) *
          ((Real.log (2 * (n : ℝ)))^3 * (Real.log (6 * Real.log (2 * (n : ℝ))))^2) ∧
      ∃ D : DTree (Finset (Fin n)) ℝ (Option (Output (Fin n))) q,
        (∀ read, D.cost read ≤ q) ∧
        ∀ G : WeightedGraph (Fin n), 0 < mincutValue G →
          ∃ out, D.eval G.cut = some out ∧ Correct G α out :=
  CutQueryComplexity.TreeCutSparsifier.theorem5LL

#audit_cut_decl Paper1HeadlineVerification.DiscoveryChecks.check_theorem5LL
#print axioms CutQueryComplexity.TreeCutSparsifier.theorem5LL

end DiscoveryChecks

-- Lemma 2 companions: public patterns, terminal shore/value, and terminal sets.
#audit_cut_decl CutQueryComplexity.Certificate.TreePattern.public_flow_patterns
#audit_cut_decl CutQueryComplexity.Certificate.TreePattern.exists_terminal_tree_certificate
#audit_cut_decl CutQueryComplexity.Certificate.exists_cutCert
#print axioms CutQueryComplexity.Certificate.TreePattern.public_flow_patterns
#print axioms CutQueryComplexity.Certificate.TreePattern.exists_terminal_tree_certificate
#print axioms CutQueryComplexity.Certificate.exists_cutCert

-- The log-log hierarchy declarations cited for Lemma 40 in the paper's Lean appendix.
#audit_cut_decl CutQueryComplexity.TreeCutSparsifier.certifyLL
#audit_cut_decl CutQueryComplexity.TreeCutSparsifier.phaseLL_spec
#audit_cut_decl CutQueryComplexity.TreeCutSparsifier.qualityLL_le
#print axioms CutQueryComplexity.TreeCutSparsifier.certifyLL
#print axioms CutQueryComplexity.TreeCutSparsifier.phaseLL_spec
#print axioms CutQueryComplexity.TreeCutSparsifier.qualityLL_le

/-! ## Small facts used in the reader

These short proofs back two remarks in `README.md`: the zero case of Theorem 1, and the
zero-case output of Theorem 4 (from which the paper's component partition is recovered
without further queries). The last theorem shows that the skeleton constant `111/100`
implies the paper's `5/4`. -/
namespace SupplementaryFacts
open CutQueryComplexity Finset
open CutQueryComplexity.Certificate
open CutQueryComplexity.AllMinCuts

variable {V : Type} [Fintype V] [DecidableEq V]

theorem zero_single_shore (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V)
    (h0 : mincutValue G = 0) :
    ∃ S : Finset V, IsMinCut G S ∧ IsMinCutWitnessCertificate G {S} S := by
  obtain ⟨S, hS⟩ := exists_isMinCut_of_two_le_card G hn
  have hcut : G.cut S = 0 := ((isMinCut_iff G S).mp hS).2.trans h0
  refine ⟨S, hS, mem_singleton_self S, fun H hH => ?_⟩
  exact (SupportForest.isMinCut_of_cut_eq_zero H hS.1
    ((hH S (mem_singleton_self S)).trans hcut)).1

/- The zero-case partition is computable from membership in the returned
finite cut family alone. No graph, oracle or forest is an input to recovery. -/
open Classical in
noncomputable def recoveredPart (out : Output V) (u : V) : Finset V :=
  univ.filter fun v => ∀ S ∈ out.cuts, u ∈ S ↔ v ∈ S

open Classical in
noncomputable def recoveredPartition (out : Output V) : Finset (Finset V) :=
  univ.image (recoveredPart out)

theorem recoveredPart_eq_component (G : WeightedGraph V) (out : Output V)
    (h : Correct G out) (h0 : mincutValue G = 0) (u : V) :
    recoveredPart out u = SupportForest.reachClass G u := by
  classical
  ext v
  simp only [recoveredPart, mem_filter, mem_univ, true_and, SupportForest.mem_reachClass]
  constructor
  · intro hsig
    by_contra hnot
    have hu : u ∈ SupportForest.reachClass G u := by simp
    have hproper : ProperShore (SupportForest.reachClass G u) := by
      refine ⟨⟨u, hu⟩, fun heq => ?_⟩
      have hv : v ∈ SupportForest.reachClass G u := heq ▸ mem_univ v
      exact hnot ((SupportForest.mem_reachClass G u v).mp hv)
    have hcut := (SupportForest.isMinCut_of_cut_eq_zero G hproper
      (SupportForest.cut_reachClass G u)).1
    have hv := (hsig _ ((h.2 _).mpr hcut)).mp hu
    exact hnot ((SupportForest.mem_reachClass G u v).mp hv)
  · intro hreach S hS
    have hz : G.cut S = 0 := ((isMinCut_iff G S).mp ((h.2 S).mp hS)).2.trans h0
    exact ⟨fun hu => reachable_mem_of_cut_zero G S hz hu hreach,
      fun hv => reachable_mem_of_cut_zero G S hz hv hreach.symm⟩

theorem recoveredPartition_eq_components (G : WeightedGraph V) (out : Output V)
    (h : Correct G out) (h0 : mincutValue G = 0) :
    recoveredPartition out = univ.image (SupportForest.reachClass G) := by
  classical
  unfold recoveredPartition
  congr 1
  funext u
  exact recoveredPart_eq_component G out h h0 u

-- `map` performs the partition recovery without another oracle call.
theorem partition_recovery_preserves_cost {n q : ℕ}
    (D : DTree (Finset (Fin n)) ℝ (Option (Output (Fin n))) q)
    (read : Finset (Fin n) → ℝ) :
    (D.map (Option.map (fun out => (out, recoveredPartition out)))).cost read = D.cost read := by
  simp [DTree.cost, DTree.run_map]

theorem skeleton_implies_paper_definition (G H : WeightedGraph V)
    (h : AllMinCutSkeleton G H) :
    mincutValue G ≤ mincutValue H ∧
      ∀ S, IsMinCut G S → H.cut S ≤ (5 / 4 : ℝ) * mincutValue G := by
  refine ⟨h.1, fun S hS => ?_⟩
  have hupper := h.2 S hS
  have hnonneg := mincutValue_nonneg G
  linarith

/-- The two-query example program from the reading guide in `README.md`. -/
example : DTree (Finset (Fin 3)) ℝ ℝ 2 :=
  DTree.query {0} fun a => DTree.query {0, 1} fun b => DTree.pure (a + b)

end SupplementaryFacts

end Paper1HeadlineVerification
