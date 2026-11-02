import CutQueryComplexity.DirectedCertificate.FlowCert
import CutQueryComplexity.DirectedCertificate.Completion.SourceRoute

set_option autoImplicit false

/-! # Exact directed terminal certificates

The terminal value is the actual minimum over `s`--`t` shores. Real-capacity
max-flow/min-cut supplies a flow of that value, and the directed flow compiler
certifies its divergence using at most `18 n` original outgoing-cut queries.
One queried optimum shore fixes the matching upper bound. All competitors are
nonnegative real weighted digraphs, with arbitrary support and capacities.
-/

namespace CutQueryComplexity.DirectedCertificate.Completion

open Finset WeightedDiGraph Certificate

variable {V : Type*} [Fintype V] [DecidableEq V]

def terminalShores (s t : V) : Finset (Finset V) :=
  univ.filter fun S => s ∈ S ∧ t ∉ S

@[simp] theorem mem_terminalShores (s t : V) (S : Finset V) :
    S ∈ terminalShores s t ↔ s ∈ S ∧ t ∉ S := by
  simp [terminalShores]

theorem terminalShores_nonempty {s t : V} (hst : s ≠ t) :
    (terminalShores s t).Nonempty :=
  ⟨{s}, (mem_terminalShores _ _ _).mpr ⟨mem_singleton_self _, by simpa using hst.symm⟩⟩

/-- The exact directed terminal minimum; zero when the terminals coincide. -/
noncomputable def terminalValue (G : WeightedDiGraph V) (s t : V) : ℝ :=
  if h : (terminalShores s t).Nonempty then (terminalShores s t).inf' h G.out else 0

theorem terminalValue_le (G : WeightedDiGraph V) {s t : V} {S : Finset V}
    (hs : s ∈ S) (ht : t ∉ S) : terminalValue G s t ≤ G.out S := by
  have hm := (mem_terminalShores s t S).mpr ⟨hs, ht⟩
  rw [terminalValue, dite_eq_left ⟨S, hm⟩]
  exact inf'_le _ hm

def IsTerminalMinCut (G : WeightedDiGraph V) (s t : V) (S : Finset V) : Prop :=
  s ∈ S ∧ t ∉ S ∧ ∀ T : Finset V, s ∈ T → t ∉ T → G.out S ≤ G.out T

theorem IsTerminalMinCut.out_eq_terminalValue {G : WeightedDiGraph V} {s t : V}
    {S : Finset V} (h : IsTerminalMinCut G s t S) : G.out S = terminalValue G s t := by
  refine le_antisymm ?_ (terminalValue_le G h.1 h.2.1)
  have hne : (terminalShores s t).Nonempty :=
    ⟨S, (mem_terminalShores _ _ _).mpr ⟨h.1, h.2.1⟩⟩
  obtain ⟨T, hT, hTv⟩ := exists_mem_eq_inf' hne G.out
  rw [terminalValue, dite_eq_left hne, hTv]
  exact h.2.2 T ((mem_terminalShores _ _ _).mp hT).1
    ((mem_terminalShores _ _ _).mp hT).2

/-- Both primal and dual witnesses are obtained from actual real-capacity
max-flow/min-cut, with no lower bound on unrelated cuts. -/
theorem exists_optimal_terminal_flow (G : WeightedDiGraph V) {s t : V} (hst : s ≠ t) :
    ∃ f : V → V → ℝ, ∃ S : Finset V,
      G.STFlow s t f ∧ IsTerminalMinCut G s t S ∧
      netOut f s = terminalValue G s t ∧ G.out S = terminalValue G s t := by
  obtain ⟨f, S, hf, hs, ht, hval, -, hmin⟩ := G.maxFlow_minCut hst
  have hS : IsTerminalMinCut G s t S := ⟨hs, ht, hmin⟩
  exact ⟨f, S, hf, hS, hval.trans hS.out_eq_terminalValue, hS.out_eq_terminalValue⟩

theorem terminalValue_nonneg (G : WeightedDiGraph V) {s t : V} (hst : s ≠ t) :
    0 ≤ terminalValue G s t := by
  obtain ⟨_, S, _, _, _, hS⟩ := exists_optimal_terminal_flow G hst
  exact (G.out_nonneg S).trans_eq hS

/-- A queried terminal shore that is optimal for every consistent competitor. -/
def IsTerminalWitnessCertificate (G : WeightedDiGraph V) (s t : V)
    (Q : Finset (Finset V)) (S : Finset V) : Prop :=
  S ∈ Q ∧ ∀ G' : WeightedDiGraph V, Consistent G G' Q → IsTerminalMinCut G' s t S

theorem IsTerminalWitnessCertificate.values {G : WeightedDiGraph V} {s t : V}
    {Q : Finset (Finset V)} {S : Finset V} (h : IsTerminalWitnessCertificate G s t Q S)
    (G' : WeightedDiGraph V) (hG' : Consistent G G' Q) :
    G'.out S = terminalValue G s t ∧ terminalValue G' s t = terminalValue G s t := by
  have hactual := (h.2 G (Consistent.refl G Q)).out_eq_terminalValue
  have hother := (h.2 G' hG').out_eq_terminalValue
  exact ⟨(hG' S h.1).trans hactual, hother.symm.trans ((hG' S h.1).trans hactual)⟩

/-- Exact terminal witness certificate: at most `18 n + 1` original queries,
chosen before all arbitrary nonnegative competitors. -/
theorem exists_terminal_witnessCertificate (G : WeightedDiGraph V) {s t : V}
    (hst : s ≠ t) :
    ∃ Q : Finset (Finset V), ∃ S : Finset V,
      Q.card ≤ 18 * Fintype.card V + 1 ∧ IsTerminalWitnessCertificate G s t Q S := by
  classical
  obtain ⟨f, S, hf, hS, hflow, hvalue⟩ := exists_optimal_terminal_flow G hst
  obtain ⟨Q, hQ, hcert⟩ := exists_flowCert_directed G hf.1
  refine ⟨insert S Q, S, (card_insert_le S Q).trans (Nat.add_le_add_right hQ 1),
    mem_insert_self _ _, fun G' hG' => ⟨hS.1, hS.2.1, fun T hs ht => ?_⟩⟩
  rw [hG' S (mem_insert_self _ _), hvalue]
  have h := hcert G' (hG'.mono (subset_insert S Q)) T
  rw [sum_netOut_st hf hs ht, hflow] at h
  exact h

/-- **Paper 3, exact terminal endpoint.** The returned value is the actual
terminal minimum. Agreement on the fixed outgoing-cut family determines both
that value and an optimum shore for every unrestricted competitor. -/
theorem exists_exact_terminal_certificate (G : WeightedDiGraph V) {s t : V}
    (hst : s ≠ t) :
    ∃ Q : Finset (Finset V), ∃ S : Finset V, ∃ lam : ℝ,
      Q.card ≤ 18 * Fintype.card V + 1 ∧ S ∈ Q ∧
      lam = terminalValue G s t ∧ 0 ≤ lam ∧
      ∀ G' : WeightedDiGraph V, Consistent G G' Q →
        s ∈ S ∧ t ∉ S ∧ G'.out S = lam ∧ terminalValue G' s t = lam ∧
        ∀ T : Finset V, s ∈ T → t ∉ T → lam ≤ G'.out T := by
  obtain ⟨Q, S, hQ, hcert⟩ := exists_terminal_witnessCertificate G hst
  refine ⟨Q, S, terminalValue G s t, hQ, hcert.1, rfl,
    terminalValue_nonneg G hst, fun G' hG' => ?_⟩
  have hS := hcert.2 G' hG'
  obtain ⟨hvalue, hmin⟩ := hcert.values G' hG'
  refine ⟨hS.1, hS.2.1, hvalue, hmin, fun T hs ht => ?_⟩
  rw [← hvalue]
  exact hS.2.2 T hs ht

/-- A zero terminal optimum needs only its optimum-shore query. -/
theorem exists_zero_terminal_certificate (G : WeightedDiGraph V) {s t : V}
    (hst : s ≠ t) (hzero : terminalValue G s t = 0) :
    ∃ S : Finset V, IsTerminalWitnessCertificate G s t {S} S ∧
      ∀ G' : WeightedDiGraph V, Consistent G G' {S} →
        G'.out S = 0 ∧ terminalValue G' s t = 0 := by
  obtain ⟨_, S, _, hS, _, hvalue⟩ := exists_optimal_terminal_flow G hst
  have hcert : IsTerminalWitnessCertificate G s t {S} S := by
    refine ⟨mem_singleton_self _, fun G' hG' => ⟨hS.1, hS.2.1, fun T _ _ => ?_⟩⟩
    rw [hG' S (mem_singleton_self _), hvalue, hzero]
    exact G'.out_nonneg T
  refine ⟨S, hcert, fun G' hG' => ?_⟩
  simpa only [hzero] using hcert.values G' hG'

end CutQueryComplexity.DirectedCertificate.Completion

#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_optimal_terminal_flow
#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_terminal_witnessCertificate
#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_exact_terminal_certificate
#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_zero_terminal_certificate
