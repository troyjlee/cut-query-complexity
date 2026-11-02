import CutQueryComplexity.DirectedUnitST.Endpoint.Representation
import CutQueryComplexity.ImplicitLP.PathFollowing.GlobalValidity
import CutQueryComplexityChecks.AxiomAudit

/-! # Paper 4: checking the headline theorem statements

Each `check_…` theorem below restates a headline theorem of the paper word for word and
proves it by citing the library. If this file compiles, the library proves exactly these
statements. `#audit_cut_decl` and `#print axioms` then confirm that the proofs use only
Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`): no `sorry`
and no extra assumption.

Run from the root of the repository, after building the imports (see `README.md` in this
folder):

    lake env lean --trust=0 papers/P4/VerifyHeadlineTheorems.lean
-/

set_option autoImplicit false
set_option exponentiation.threshold 512

namespace Paper4HeadlineVerification

open CutQueryComplexity Finset
open CutQueryComplexity.DirectedCertificate
open CutQueryComplexity.DirectedUnitST
open CutQueryComplexity.DirectedUnitST.Endpoint
open CutQueryComplexity.ImplicitLP.PathFollowing

theorem check_exists_unitST_query_program {n : ℕ} (hn : 2 ≤ n) (s t : Fin n) (hst : s ≠ t) :
    ∃ T : DTree (Finset (Fin n)) ℕ (Option (Finset (Fin n) × ℕ)) (headlineQueries n),
      (∀ read : Finset (Fin n) → ℕ, T.cost read ≤ headlineQueries n ∧
        (T.cost read : ℝ) ≤ 2049 * (n : ℝ) ^ (5 / 3 : ℝ) * (logScale n : ℝ) ^ 2) ∧
      ∀ G : DiGraph (Fin n), G.Simple →
        ∃ S : Finset (Fin n), T.eval G.out = some (S, G.out S) ∧
          s ∈ S ∧ t ∉ S ∧ ∀ W : Finset (Fin n), s ∈ W → t ∉ W → G.out S ≤ G.out W :=
  CutQueryComplexity.DirectedUnitST.Endpoint.exists_unitST_query_program hn s t hst

theorem check_exists_unitST_representation {n : ℕ} (hn : 2 ≤ n) :
    ∃ P : DTree (Finset (Fin n)) ℕ (Option (Blocking.SolveResult (Fin n)))
        (representationBudget n),
      (∀ read : Finset (Fin n) → ℕ, P.cost read ≤ headlineQueries n ∧
        (P.cost read : ℝ) ≤ 2049 * (n : ℝ) ^ (5 / 3 : ℝ) * (logScale n : ℝ) ^ 2) ∧
      (∀ G : DiGraph (Fin n), G.Simple →
        ∃ result, P.eval G.out = some result ∧
          ∃ K : WeightedDiGraph (Fin n),
            result.network.internal.Realizes (Preparation.realGraph G) K ∧
            (∀ u v, ∃ m : ℕ, K.c u v = m) ∧
            ∀ S : Finset (Fin n), K.out S = (G.out S : ℝ)) ∧
      ∀ (s t : Fin n) (read : Finset (Fin n) → ℕ),
        (unitSTNatTree n s t).eval read =
          ((terminalAfterRepair n s t (P.eval read)).eval read).map
            fun result => (result.shore, ⌊result.value⌋₊) :=
  CutQueryComplexity.DirectedUnitST.Endpoint.exists_unitST_representation hn

theorem check_directed_terminal_query_theorem {n : ℕ} (hn : 2 ≤ n) (s t : Fin n) (hst : s ≠ t)
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    (∀ (read : Finset (Fin n) → ℕ) (out : (Finset (Fin n) × ℕ) × ℕ),
      out ∈ (RTree.run read (calibratedTerminalSolver n s t ζ)).support →
      (out.2 : ℝ) ≤ 2 ^ 310 * (n : ℝ) ^ (3 / 2 : ℝ) * failureLog n ζ ^ 21) ∧
    (∀ G : DiGraph (Fin n), G.Simple →
      1 - ζ ≤ (calibratedTerminalSolver n s t ζ).successProb G.out (DirectedMincut.STGood s t G)) :=
  CutQueryComplexity.ImplicitLP.PathFollowing.directed_terminal_query_theorem hn s t hst hζ hζ1

theorem check_directed_global_query_theorem {n : ℕ} (hn : 2 ≤ n)
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    (∀ (read : Finset (Fin n) → ℕ) (out : (Finset (Fin n) × ℕ) × ℕ),
      out ∈ (RTree.run read (balancedGlobalMinCut n hn ζ)).support →
      (out.2 : ℝ) ≤ 2 ^ 340 * (n : ℝ) ^ (7 / 4 : ℝ) * failureLog n ζ ^ 22) ∧
    (∀ G : DiGraph (Fin n), G.Simple →
      1 - ζ ≤ (balancedGlobalMinCut n hn ζ).successProb G.out (DirectedMincut.Opt G)) :=
  CutQueryComplexity.ImplicitLP.PathFollowing.directed_global_query_theorem hn hζ hζ1

theorem check_calibratedTerminalSolver_valid {n : ℕ} (hn : 2 ≤ n) (s t : Fin n) (hst : s ≠ t)
    (ζ : ℝ) (G : DiGraph (Fin n)) {out : Finset (Fin n) × ℕ}
    (ho : out ∈ ((calibratedTerminalSolver n s t ζ).eval G.out).support) :
    s ∈ out.1 ∧ t ∉ out.1 ∧ out.2 = G.out out.1 :=
  CutQueryComplexity.ImplicitLP.PathFollowing.calibratedTerminalSolver_valid hn s t hst ζ G ho

theorem check_balancedGlobalMinCut_valid {n : ℕ} (hn : 2 ≤ n) (ζ : ℝ) (G : DiGraph (Fin n))
    (hG : G.Simple) {out : Finset (Fin n) × ℕ}
    (ho : out ∈ ((balancedGlobalMinCut n hn ζ).eval G.out).support) :
    DirectedMincut.Valid G out :=
  CutQueryComplexity.ImplicitLP.PathFollowing.balancedGlobalMinCut_valid hn ζ G hG ho

#audit_cut_decl Paper4HeadlineVerification.check_exists_unitST_query_program
#print axioms CutQueryComplexity.DirectedUnitST.Endpoint.exists_unitST_query_program
#audit_cut_decl Paper4HeadlineVerification.check_exists_unitST_representation
#print axioms CutQueryComplexity.DirectedUnitST.Endpoint.exists_unitST_representation
#audit_cut_decl Paper4HeadlineVerification.check_directed_terminal_query_theorem
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.directed_terminal_query_theorem
#audit_cut_decl Paper4HeadlineVerification.check_directed_global_query_theorem
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.directed_global_query_theorem
#audit_cut_decl Paper4HeadlineVerification.check_calibratedTerminalSolver_valid
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.calibratedTerminalSolver_valid
#audit_cut_decl Paper4HeadlineVerification.check_balancedGlobalMinCut_valid
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.balancedGlobalMinCut_valid

/-! ## Small facts used in the reader

These short proofs back remarks in `README.md`. The first two spell out the success
predicates `STGood` and `Opt` as inequalities against every legal shore. The third shows that a
digraph with the cut function of `G` has the pair totals of `G`. The rest show that the
failure parameter `ζ = n^(-c)` is allowed, compute the logarithm in the query caps at that
value, and state the randomized theorems in the paper's form "with probability at least
`1 - n^(-c)`". The two examples are the programs from the reading guide. -/
namespace SupplementaryFacts

theorem stGood_iff_inequalities {n : ℕ} (G : DiGraph (Fin n)) (s t : Fin n) (hst : s ≠ t)
    (r : Finset (Fin n) × ℕ) :
    DirectedMincut.STGood s t G r ↔
      s ∈ r.1 ∧ t ∉ r.1 ∧ r.2 = G.out r.1 ∧
        ∀ S : Finset (Fin n), s ∈ S → t ∉ S → r.2 ≤ G.out S := by
  constructor
  · rintro ⟨hs, ht, hmin, hvalue⟩
    refine ⟨hs, ht, hvalue, fun S hS hT => ?_⟩
    rw [hvalue, hmin]
    exact DirectedMincut.stMin_le G hS hT
  · rintro ⟨hs, ht, hvalue, hmin⟩
    obtain ⟨S, hS, hT, he⟩ := DirectedMincut.exists_stMin G hst
    refine ⟨hs, ht, le_antisymm ?_ (DirectedMincut.stMin_le G hs ht), hvalue⟩
    rw [← hvalue, ← he]
    exact hmin S hS hT

theorem opt_iff_inequalities {n : ℕ} (hn : 2 ≤ n) (G : DiGraph (Fin n))
    (r : Finset (Fin n) × ℕ) :
    DirectedMincut.Opt G r ↔
      r.1.Nonempty ∧ r.1 ≠ univ ∧ r.2 = G.out r.1 ∧
        ∀ S : Finset (Fin n), S.Nonempty → S ≠ univ → r.2 ≤ G.out S := by
  constructor
  · rintro ⟨⟨hne, hproper, hvalue⟩, hmin⟩
    refine ⟨hne, hproper, hvalue, fun S hS hT => ?_⟩
    rw [hvalue, hmin]
    exact DirectedMincut.globalMin_le G hS hT
  · rintro ⟨hne, hproper, hvalue, hmin⟩
    obtain ⟨S, hS, hT, he⟩ := DirectedMincut.exists_globalMin G
      (by simpa only [Fintype.card_fin] using hn)
    refine ⟨⟨hne, hproper, hvalue⟩,
      le_antisymm ?_ (DirectedMincut.globalMin_le G hne hproper)⟩
    rw [← hvalue, ← he]
    exact hmin S hS hT

/- Equal outgoing cuts give equal pair totals, by
`c(u,v) + c(v,u) = F({u}) + F({v}) - F({u,v})` for `u ≠ v`. -/
theorem pair_totals_of_cut_equivalence {n : ℕ} (G : DiGraph (Fin n))
    (K : WeightedDiGraph (Fin n))
    (hcuts : ∀ S : Finset (Fin n), K.out S = (G.out S : ℝ)) (u v : Fin n) :
    K.c u v + K.c v u = (G.c u v : ℝ) + (G.c v u : ℝ) := by
  by_cases huv : u = v
  · subst v
    simp [K.diag, G.diag]
  · change K.sym.w u v = (Preparation.realGraph G).sym.w u v
    rw [K.sym_w_eq_three_outs huv, (Preparation.realGraph G).sym_w_eq_three_outs huv]
    simp only [hcuts, Preparation.realGraph_out]

theorem high_probability_parameter {n : ℕ} (hn : 2 ≤ n) {c : ℝ} (hc : 0 < c) :
    0 < (n : ℝ) ^ (-c) ∧ (n : ℝ) ^ (-c) ≤ 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  constructor
  · exact Real.rpow_pos_of_pos hn0 _
  · rw [Real.rpow_neg hn0.le]
    exact inv_le_one_of_one_le₀ (Real.one_le_rpow hn1 hc.le)

/- At `ζ = n^(-c)`, the logarithm `log₂(2n/ζ)` in the caps is `1 + (1 + c) log₂ n`. -/
theorem failureLog_rpow_neg {n : ℕ} (hn : 2 ≤ n) (c : ℝ) :
    failureLog n ((n : ℝ) ^ (-c)) = 1 + (1 + c) * Real.logb 2 n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h : queryHeight n / (n : ℝ) ^ (-c) = 2 * (n : ℝ) ^ (1 + c) := by
    unfold queryHeight
    rw [Real.rpow_neg hn0.le, div_inv_eq_mul, Real.rpow_add hn0, Real.rpow_one]
    ring
  unfold failureLog
  rw [h, Real.logb_mul (by norm_num) (Real.rpow_pos_of_pos hn0 _).ne',
    Real.logb_self_eq_one (by norm_num), Real.logb_rpow_eq_mul_logb_of_pos hn0]

theorem terminal_with_high_probability {n : ℕ} (hn : 2 ≤ n) (s t : Fin n) (hst : s ≠ t)
    {c : ℝ} (hc : 0 < c) :
    (∀ (read : Finset (Fin n) → ℕ) (out : (Finset (Fin n) × ℕ) × ℕ),
      out ∈ (RTree.run read (calibratedTerminalSolver n s t ((n : ℝ) ^ (-c)))).support →
      (out.2 : ℝ) ≤ 2 ^ 310 * (n : ℝ) ^ (3 / 2 : ℝ) * (1 + (1 + c) * Real.logb 2 n) ^ 21) ∧
    (∀ G : DiGraph (Fin n), G.Simple →
      1 - (n : ℝ) ^ (-c) ≤ (calibratedTerminalSolver n s t ((n : ℝ) ^ (-c))).successProb
        G.out (DirectedMincut.STGood s t G)) := by
  obtain ⟨h0, h1⟩ := high_probability_parameter hn hc
  have h := directed_terminal_query_theorem hn s t hst h0 h1
  rw [failureLog_rpow_neg hn c] at h
  exact h

theorem global_with_high_probability {n : ℕ} (hn : 2 ≤ n) {c : ℝ} (hc : 0 < c) :
    (∀ (read : Finset (Fin n) → ℕ) (out : (Finset (Fin n) × ℕ) × ℕ),
      out ∈ (RTree.run read (balancedGlobalMinCut n hn ((n : ℝ) ^ (-c)))).support →
      (out.2 : ℝ) ≤ 2 ^ 340 * (n : ℝ) ^ (7 / 4 : ℝ) * (1 + (1 + c) * Real.logb 2 n) ^ 22) ∧
    (∀ G : DiGraph (Fin n), G.Simple →
      1 - (n : ℝ) ^ (-c) ≤ (balancedGlobalMinCut n hn ((n : ℝ) ^ (-c))).successProb
        G.out (DirectedMincut.Opt G)) := by
  obtain ⟨h0, h1⟩ := high_probability_parameter hn hc
  have h := directed_global_query_theorem hn h0 h1
  rw [failureLog_rpow_neg hn c] at h
  exact h

/-- The two-query deterministic example program from the reading guide in `README.md`. -/
example : DTree (Finset (Fin 3)) ℕ ℕ 2 :=
  DTree.query {0} fun a => DTree.query {0, 1} fun b => DTree.pure (a + b)

noncomputable section

/-- The one-query randomized example program from the reading guide in `README.md`. -/
example : RTree (Finset (Fin 3)) ℕ ℕ 1 :=
  RTree.mix ((PMF.uniformOfFintype (Fin 3)).map fun v =>
    RTree.query {v} fun a => RTree.pure (PMF.pure a))

end

end SupplementaryFacts

end Paper4HeadlineVerification
