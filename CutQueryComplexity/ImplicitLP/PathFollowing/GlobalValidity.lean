import CutQueryComplexity.ImplicitLP.PathFollowing.QueryEndpoint

/-! # Every candidate of the randomized programs is legal

`DirectedMincut.global_valid`: on a simple input, every execution of the global reduction
returns a nonempty proper shore with its true outgoing-cut value, provided every terminal
call does so for its own terminals. No success probability is used.

`balancedGlobalMinCut_valid` instantiates this with the actual balanced global program of
`directed_global_query_theorem`, for every failure allowance. `calibratedTerminalSolver_valid`
is the corresponding statement for the terminal program of `directed_terminal_query_theorem`.
-/

set_option autoImplicit false

namespace CutQueryComplexity

namespace DirectedMincut

open Finset Probability

variable {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]

theorem global_valid [Nonempty V] {G : DiGraph V} (hG : G.Simple)
    (hn : 2 ≤ Fintype.card V) {k : ℕ} (hk : Fintype.card V ≤ 2 ^ k) (h K : ℕ) (a : V)
    {qst : ℕ} {T : V → V → RTree (Finset V) ℕ (Finset V × ℕ) qst}
    (hT : ∀ a b, a ≠ b → ∀ r ∈ ((T a b).eval G.out).support,
      a ∈ r.1 ∧ b ∉ r.1 ∧ r.2 = G.out r.1)
    {r : Finset V × ℕ} (hr : r ∈ ((global k h K a T).eval G.out).support) : Valid G r := by
  -- With failure allowance one, the exactness clause of the terminal contract is vacuous.
  have hspec : TermSpec G T 1 :=
    ⟨hT, fun _ _ _ => by rw [ENNReal.ofReal_one]; exact mass_le_one _ _⟩
  have hr0 : Valid G ((smallShore k h).eval G.out) := by
    obtain ⟨h1, h2, h3, -, -⟩ := smallShore_correct hG hn hk h
    exact ⟨h1, h2, h3⟩
  have hdet : (RTree.ofDeterministic (smallShore k h)).eval G.out =
      PMF.pure ((smallShore k h).eval G.out) := by
    rw [RTree.eval, RTree.run_ofDeterministic, PMF.pure_map]; rfl
  rw [global, RTree.eval_bind, hdet, PMF.pure_bind] at hr
  simp only [samplePhase, RTree.eval_mix, PMF.bind_map, Function.comp_def, RTree.eval_weaken,
    PMF.mem_support_bind_iff] at hr
  obtain ⟨σ, -, hr⟩ := hr
  have hzero := chain_valid hspec (pairsOf a σ) (pairsOf_ne a σ) _ hr0
  rw [mass, PMF.toOuterMeasure_apply_eq_zero_iff] at hzero
  by_contra hbad
  exact Set.disjoint_left.mp hzero hr hbad

end DirectedMincut

namespace ImplicitLP.PathFollowing

variable {E : NewtonPub}

theorem publicTerminalSolver_valid (G : DiGraph (Fin E.n)) (P : Params E)
    (hst : P.s ≠ P.terminal) (k : ℕ) (hk : E.n ≤ 2 ^ k) (θ : ℝ)
    {out : Finset (Fin E.n) × ℕ}
    (ho : out ∈ ((publicTerminalSolver P k θ).eval G.out).support) :
    P.s ∈ out.1 ∧ P.terminal ∉ out.1 ∧ out.2 = G.out out.1 :=
  terminalSolver_valid G P hst _ _ _ _ _ k hk θ ho

/-- Every output of the actual calibrated terminal program, on every execution and for every
failure allowance, is an `s`–`t` shore with its true outgoing-cut value. -/
theorem calibratedTerminalSolver_valid {n : ℕ} (hn : 2 ≤ n) (s t : Fin n) (hst : s ≠ t)
    (ζ : ℝ) (G : DiGraph (Fin n)) {out : Finset (Fin n) × ℕ}
    (ho : out ∈ ((calibratedTerminalSolver n s t ζ).eval G.out).support) :
    s ∈ out.1 ∧ t ∉ out.1 ∧ out.2 = G.out out.1 :=
  publicTerminalSolver_valid G (calibratedParams n s t ζ) hst (Sparsify.pK n)
    (Sparsify.params_ok (C := 1) (ε := 1 / 2) (ζ := 1 / 2) hn le_rfl (by norm_num)
      le_rfl (by norm_num) le_rfl).1
    (publicExtractionScale n) ho

/-- Kept generic in the parameters, so that no calibrated budget is unfolded. -/
theorem publicGlobalSolver_valid (G : DiGraph (Fin E.n)) (hG : G.Simple) (P : Params E)
    (hn : 2 ≤ E.n) (k : ℕ) (hk : E.n ≤ 2 ^ k) (h K : ℕ) (θ : ℝ)
    {out : Finset (Fin E.n) × ℕ}
    (ho : out ∈ ((publicGlobalSolver P k h K θ).eval G.out).support) :
    DirectedMincut.Valid G out := by
  let _ : Nonempty (Fin E.n) := ⟨P.s⟩
  exact DirectedMincut.global_valid hG (by simpa only [Fintype.card_fin] using hn)
    (by simpa only [Fintype.card_fin] using hk) h K P.s
    (fun s t hst r hr => terminalSolver_valid G {P with s := s, terminal := t} hst _ _ _ _ _
      k hk θ hr) ho

/-- Every output of the actual balanced global program, on every execution and for every
failure allowance, is a nonempty proper shore with its true outgoing-cut value. -/
theorem balancedGlobalMinCut_valid {n : ℕ} (hn : 2 ≤ n) (ζ : ℝ) (G : DiGraph (Fin n))
    (hG : G.Simple) {out : Finset (Fin n) × ℕ}
    (ho : out ∈ ((balancedGlobalMinCut n hn ζ).eval G.out).support) :
    DirectedMincut.Valid G out :=
  publicGlobalSolver_valid G hG (calibratedGlobalParams n hn (ζ / 2)) hn (Sparsify.pK n)
    (Sparsify.params_ok (C := 1) (ε := 1 / 2) (ζ := 1 / 2) hn le_rfl (by norm_num)
      le_rfl (by norm_num) le_rfl).1
    (publicShoreSize n) (publicRootCount n (publicShoreSize n) ζ) (publicExtractionScale n) ho

end ImplicitLP.PathFollowing

end CutQueryComplexity

#print axioms CutQueryComplexity.DirectedMincut.global_valid
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.publicTerminalSolver_valid
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.calibratedTerminalSolver_valid
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.publicGlobalSolver_valid
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.balancedGlobalMinCut_valid
