import CutQueryComplexity.DirectedCertificate.Basic
import CutQueryComplexity.Certificate.Main
import Mathlib.Tactic

/-!
# Eulerian directed weighted minimum-cut certificates

Singleton and complementary-singleton measurements force zero imbalance in
every consistent nonnegative real-weighted competitor. Two outgoing shores
simulate each cut of the symmetrization. Applying the existing undirected
witness theorem therefore gives an original outgoing-cut certificate with
at most `2n + 36n * clog₂(2n)^2` shores, chosen before every competitor.

This is a verification certificate. The query family may depend on the input
graph; no graph-discovery algorithm or public tree-pattern claim is made.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DirectedCertificate.Completion

open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Both original outgoing shores used to simulate an undirected cut. -/
def symLiftQueries (Q : Finset (Finset V)) : Finset (Finset V) :=
  Q ∪ Q.image compl

theorem symLiftQueries_card_le (Q : Finset (Finset V)) :
    (symLiftQueries Q).card ≤ 2 * Q.card := by
  have h₁ := card_union_le Q (Q.image compl)
  have h₂ := card_image_le (s := Q) (f := compl)
  unfold symLiftQueries
  omega

/-- Fixed degree measurements plus the two-shore simulation family. -/
def eulerianQueries (Q : Finset (Finset V)) : Finset (Finset V) :=
  degreeQueries V ∪ symLiftQueries Q

theorem eulerianQueries_card_le (Q : Finset (Finset V)) :
    (eulerianQueries Q).card ≤ 2 * Fintype.card V + 2 * Q.card := by
  exact (card_union_le _ _).trans
    (Nat.add_le_add degreeQueries_card (symLiftQueries_card_le Q))

/-- Eulerianity of a competitor is forced by measured degrees, not promised. -/
theorem eulerian_of_consistent_degrees {G H : WeightedDiGraph V}
    (hEuler : ∀ v, G.imbalance v = 0)
    (h : Consistent G H (degreeQueries V)) : ∀ v, H.imbalance v = 0 := by
  intro v
  exact ((degrees_eq_of_consistent h v).2.2).trans (hEuler v)

/-- Agreement on both outgoing shores fixes the symmetrized cut. -/
theorem consistent_sym_of_symLiftQueries {G H : WeightedDiGraph V}
    {Q : Finset (Finset V)} (h : Consistent G H (symLiftQueries Q)) :
    Certificate.Consistent G.sym H.sym Q := by
  intro S hS
  have h₁ : S ∈ symLiftQueries Q := mem_union_left _ hS
  have h₂ : Sᶜ ∈ symLiftQueries Q :=
    mem_union_right _ (mem_image_of_mem compl hS)
  rw [H.sym_cut, G.sym_cut, h S h₁, h Sᶜ h₂]

theorem sym_cut_eq_two_out_of_eulerian (G : WeightedDiGraph V)
    (hEuler : ∀ v, G.imbalance v = 0) (S : Finset V) :
    G.sym.cut S = 2 * G.out S := by
  simpa only [hEuler, sum_const_zero, add_zero] using (G.two_mul_out S).symm

theorem isGlobalMinCut_of_sym_eulerian (G : WeightedDiGraph V)
    (hEuler : ∀ v, G.imbalance v = 0) {S : Finset V}
    (hS : IsMinCut G.sym S) : IsGlobalMinCut G S := by
  refine ⟨hS.1, fun T hT => ?_⟩
  have h := hS.2 T hT
  rw [sym_cut_eq_two_out_of_eulerian G hEuler S,
    sym_cut_eq_two_out_of_eulerian G hEuler T] at h
  linarith

/-- Lift an actual undirected witness while certifying the competitor's
Eulerianity with original outgoing-cut measurements. -/
theorem eulerian_witnessCertificate_of_sym {G : WeightedDiGraph V}
    (hEuler : ∀ v, G.imbalance v = 0) {Q : Finset (Finset V)} {S : Finset V}
    (hcert : Certificate.IsMinCutWitnessCertificate G.sym Q S) :
    IsMinCutWitnessCertificate G (eulerianQueries Q) S := by
  refine ⟨mem_union_right _ (mem_union_left _ hcert.1), fun H hH => ?_⟩
  have hdeg : Consistent G H (degreeQueries V) := hH.mono subset_union_left
  have hboth : Consistent G H (symLiftQueries Q) := hH.mono subset_union_right
  have hEulerH := eulerian_of_consistent_degrees hEuler hdeg
  exact isGlobalMinCut_of_sym_eulerian H hEulerH
    (hcert.2 H.sym (consistent_sym_of_symLiftQueries hboth))

/-- The inventory's Eulerian refinement. The certificate includes all degree
measurements and is sound against unrestricted nonnegative competitors. The
undirected theorem covers zero minimum as well as positive minimum. -/
theorem exists_eulerian_witnessCertificate (G : WeightedDiGraph V)
    (hn : 2 ≤ Fintype.card V) (hEuler : ∀ v, G.imbalance v = 0) :
    ∃ Q : Finset (Finset V), ∃ S : Finset V,
      Q.card ≤ 2 * Fintype.card V +
        36 * Fintype.card V * (Nat.clog 2 (2 * Fintype.card V)) ^ 2 ∧
      degreeQueries V ⊆ Q ∧ IsMinCutWitnessCertificate G Q S := by
  obtain ⟨Q, S, hQ, hcert⟩ := Certificate.exists_minCut_witnessCertificate G.sym hn
  refine ⟨eulerianQueries Q, S, ?_, subset_union_left,
    eulerian_witnessCertificate_of_sym hEuler hcert⟩
  calc
    (eulerianQueries Q).card ≤ 2 * Fintype.card V + 2 * Q.card :=
      eulerianQueries_card_le Q
    _ ≤ 2 * Fintype.card V +
        2 * (18 * Fintype.card V * (Nat.clog 2 (2 * Fintype.card V)) ^ 2) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left 2 hQ) _
    _ = _ := by ring

/-- Original queried optimum shore, exact value, and minimum preservation.
The family and shore are chosen before every weighted competitor H. H has
no Eulerianity, support, capacity upper bound, or integrality assumption. -/
theorem exists_exact_eulerian_certificate (G : WeightedDiGraph V)
    (hn : 2 ≤ Fintype.card V) (hEuler : ∀ v, G.imbalance v = 0) :
    ∃ Q : Finset (Finset V), ∃ S : Finset V,
      Q.card ≤ 2 * Fintype.card V +
        36 * Fintype.card V * (Nat.clog 2 (2 * Fintype.card V)) ^ 2 ∧
      S ∈ Q ∧ ProperShore S ∧ G.out S = G.minValue ∧
      ∀ H : WeightedDiGraph V, Consistent G H Q →
        (∀ v, H.imbalance v = 0) ∧ IsGlobalMinCut H S ∧
        H.out S = G.out S ∧ H.minValue = G.minValue := by
  obtain ⟨Q, S, hQ, hdeg, hcert⟩ := exists_eulerian_witnessCertificate G hn hEuler
  refine ⟨Q, S, hQ, hcert.1, hcert.isGlobalMinCut.1,
    hcert.isGlobalMinCut.out_eq_minValue, fun H hH => ?_⟩
  exact ⟨eulerian_of_consistent_degrees hEuler (hH.mono hdeg), hcert.2 H hH,
    hH S hcert.1, hcert.isValueCertificate H hH⟩

end
end CutQueryComplexity.DirectedCertificate.Completion

#print axioms CutQueryComplexity.DirectedCertificate.Completion.eulerianQueries_card_le
#print axioms CutQueryComplexity.DirectedCertificate.Completion.eulerian_of_consistent_degrees
#print axioms CutQueryComplexity.DirectedCertificate.Completion.consistent_sym_of_symLiftQueries
#print axioms CutQueryComplexity.DirectedCertificate.Completion.sym_cut_eq_two_out_of_eulerian
#print axioms CutQueryComplexity.DirectedCertificate.Completion.isGlobalMinCut_of_sym_eulerian
#print axioms CutQueryComplexity.DirectedCertificate.Completion.eulerian_witnessCertificate_of_sym
#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_eulerian_witnessCertificate
#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_exact_eulerian_certificate
