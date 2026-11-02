import CutQueryComplexity.CanonicalST.Budget
import CutQueryComplexity.DeterministicAPMCExpansion.Pruning.Endpoint
import CutQueryComplexityChecks.AxiomAudit

/-! # Paper 2: checking the headline theorem statements

Each `check_…` theorem below restates a headline theorem of the paper, or one of its
companion statements, word for word and proves it by citing the library. If this file
compiles, the library proves exactly these statements. `#audit_cut_decl` and
`#print axioms` then confirm that the proofs use only Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`): no `sorry` and no extra assumption.

The last section proves the small facts that `README.md` in this folder relies on: the
returned values are natural numbers, the returned flow is maximum, the returned shore
complements to the paper's shore, and both theorems with every definition unfolded.

Run from the root of the repository, after building the imports (see `README.md` in this
folder):

    lake env lean --trust=0 papers/P2/VerifyHeadlineTheorems.lean
-/

set_option autoImplicit false

namespace Paper2HeadlineVerification

open CutQueryComplexity Finset Filter Asymptotics
open CutQueryComplexity.CanonicalST
open CutQueryComplexity.AllPairs
open CutQueryComplexity.DeterministicAPMCExpansion.Pruning

variable {V : Type} [Fintype V] [DecidableEq V]

theorem check_exists_terminal_sqrt_program (hn : 2 ≤ Fintype.card V) (s t : V) (hst : s ≠ t) :
    ∃ T : DTree (Finset V) ℝ (Option (Output V)) (headlineBudget (Fintype.card V)),
      (∀ read : Finset V → ℝ, T.cost read ≤ headlineBudget (Fintype.card V)) ∧
      ∀ G : WeightedGraph V, AllPairsAudit.Unweighted G →
        ∃ out, T.eval G.cut = some out ∧ OutputSpec G s t out :=
  CutQueryComplexity.CanonicalST.exists_terminal_sqrt_program hn s t hst

#audit_cut_decl Paper2HeadlineVerification.check_exists_terminal_sqrt_program
#print axioms CutQueryComplexity.CanonicalST.exists_terminal_sqrt_program

theorem check_deterministic_allPairs :
    ∃ (q : ℕ → ℕ)
      (P : (n : ℕ) → DTree (Finset (Fin n)) ℝ (Answers (Fin n)) (q n)),
      (∀ (n : ℕ) (G : WeightedGraph (Fin n)), AllPairsAudit.Unweighted G →
        allPairsGood G ((P n).eval G.cut)) ∧
      (∀ (n : ℕ) (read : Finset (Fin n) → ℝ), (P n).cost read ≤ q n) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
        (q n : ℝ) ≤ C * (n : ℝ) ^ (5 / 3 : ℝ) *
          ((Nat.clog 2 (2 * n + 2) + 1 : ℕ) : ℝ) ^ 5) ∧
      ((fun n : ℕ => (q n : ℝ)) =o[atTop] fun n => (n : ℝ) ^ 2) :=
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.deterministic_allPairs

#audit_cut_decl Paper2HeadlineVerification.check_deterministic_allPairs
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.deterministic_allPairs

theorem check_program_exact (n : ℕ) (G : WeightedGraph (Fin n))
    (hG : AllPairsAudit.Unweighted G) (s t : Fin n) (hst : s ≠ t) :
    IsSTMinCut G s t (((program n).eval G.cut) s t).shore ∧
      (((program n).eval G.cut) s t).value =
        G.cut (((program n).eval G.cut) s t).shore :=
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.program_exact n G hG s t hst

#audit_cut_decl Paper2HeadlineVerification.check_program_exact
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.program_exact

theorem check_program_cost_bound (n : ℕ) (hn : 2 ≤ n) (read : Finset (Fin n) → ℝ) :
    ((program n).cost read : ℝ) ≤ headlineConstant * (n : ℝ) ^ (5 / 3 : ℝ) *
      ((Nat.clog 2 (2 * n + 2) + 1 : ℕ) : ℝ) ^ 5 :=
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.program_cost_bound n hn read

#audit_cut_decl Paper2HeadlineVerification.check_program_cost_bound
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.program_cost_bound

/-! ## Small facts used in the reader

These short proofs back remarks in `README.md`. On an unweighted graph every cut value is a
natural number, so the real `value` fields are natural numbers. The flow returned by
Theorem 1 is maximum among all feasible real flows, by weak duality. The complement of
the returned shore is a minimum shore in the paper's orientation (containing `t`). The
two `_expanded` theorems restate Theorems 1 and 2 with `Unweighted`, `OutputSpec`,
`FlowSpec` and `allPairsGood` unfolded. The last two declarations check the example
program from the reading guide. -/

theorem honest_cut_is_natural (G : WeightedGraph V) (hG : AllPairsAudit.Unweighted G)
    (S : Finset V) : ∃ k : ℕ, G.cut S = k :=
  ⟨Augmentation.capacityCut (Augmentation.unitCapacity G) S,
    (Augmentation.unitCapacity_cut hG S).symm⟩

#audit_cut_decl Paper2HeadlineVerification.honest_cut_is_natural

/-- Maximum means at least the value of every feasible real terminal flow. -/
theorem output_flow_is_maximum {G : WeightedGraph V} {s t : V} {out : Output V}
    (hout : OutputSpec G s t out) (r : ℝ) (f : V → V → ℝ)
    (hanti : ∀ u v, f v u = -f u v)
    (hcap : ∀ u v, |f u v| ≤ G.w u v)
    (hdiv : ∀ x, (∑ u, f x u) =
      (if x = s then r else 0) - (if x = t then r else 0)) :
    r ≤ out.value := by
  have hf : Certificate.Feasible G f := ⟨hanti, hcap⟩
  have hd : ∀ x, Certificate.netOut f x =
      (if x = s then r else 0) - (if x = t then r else 0) := hdiv
  have hsum : (∑ x ∈ out.shore, Certificate.netOut f x) = r := by
    simp [hd, sum_sub_distrib, hout.1, hout.2.1]
  have hw := Certificate.sum_netOut_le_cut hf out.shore
  rw [hsum, ← hout.2.2.1] at hw
  exact hw

#audit_cut_decl Paper2HeadlineVerification.output_flow_is_maximum

/-- The `t`-oriented convention in the single-pair proof is equivalent. -/
theorem output_complement_is_paper_shore {G : WeightedGraph V} {s t : V} {out : Output V}
    (hout : OutputSpec G s t out) :
    t ∈ out.shoreᶜ ∧ s ∉ out.shoreᶜ ∧ out.value = G.cut out.shoreᶜ ∧
      ∀ S : Finset V, t ∈ S → s ∉ S → G.cut out.shoreᶜ ≤ G.cut S := by
  refine ⟨by simpa using hout.2.1, by simpa using hout.1,
    by simpa using hout.2.2.1, ?_⟩
  intro S ht hs
  have hm := hout.2.2.2.1 Sᶜ (by simpa using hs) (by simpa using ht)
  simpa using hm

#audit_cut_decl Paper2HeadlineVerification.output_complement_is_paper_shore

/-- Theorem 1 with every clause of its output unfolded. -/
theorem terminal_expanded (hn : 2 ≤ Fintype.card V) (s t : V) (hst : s ≠ t) :
    ∃ T : DTree (Finset V) ℝ (Option (Output V)) (headlineBudget (Fintype.card V)),
      (∀ read : Finset V → ℝ, T.cost read ≤ headlineBudget (Fintype.card V)) ∧
      ∀ G : WeightedGraph V, (∀ u v, G.w u v = 0 ∨ G.w u v = 1) →
        ∃ out, T.eval G.cut = some out ∧
          s ∈ out.shore ∧ t ∉ out.shore ∧ out.value = G.cut out.shore ∧
          (∃ k : ℕ, out.value = k) ∧
          (∀ S : Finset V, s ∈ S → t ∉ S → G.cut out.shore ≤ G.cut S) ∧
          (∀ u v, out.flow v u = -out.flow u v) ∧
          (∀ u v, |out.flow u v| ≤ G.w u v) ∧
          (∀ x, (∑ u, out.flow x u) =
            (if x = s then out.value else 0) - (if x = t then out.value else 0)) ∧
          (∀ u v, ∃ z : ℤ, out.flow u v = z) ∧
          (∀ (r : ℝ) (f : V → V → ℝ),
            (∀ u v, f v u = -f u v) →
            (∀ u v, |f u v| ≤ G.w u v) →
            (∀ x, (∑ u, f x u) =
              (if x = s then r else 0) - (if x = t then r else 0)) →
            r ≤ out.value) := by
  obtain ⟨T, hcap, hcorrect⟩ := exists_terminal_sqrt_program hn s t hst
  refine ⟨T, hcap, ?_⟩
  intro G hG
  obtain ⟨out, heval, hout⟩ := hcorrect G hG
  obtain ⟨k, hk⟩ := honest_cut_is_natural G hG out.shore
  have hflow := hout.2.2.2.2
  exact ⟨out, heval, hout.1, hout.2.1, hout.2.2.1,
    ⟨k, hout.2.2.1.trans hk⟩, hout.2.2.2.1,
    hflow.1.1, hflow.1.2, hflow.2.1, hflow.2.2, output_flow_is_maximum hout⟩

#audit_cut_decl Paper2HeadlineVerification.terminal_expanded
#print axioms Paper2HeadlineVerification.terminal_expanded

/-- Theorem 2 with ordered-pair correctness unfolded, including the paper's integer values. -/
theorem allPairs_expanded :
    ∃ (q : ℕ → ℕ)
      (P : (n : ℕ) → DTree (Finset (Fin n)) ℝ (Answers (Fin n)) (q n)),
      (∀ (n : ℕ) (G : WeightedGraph (Fin n)),
        (∀ u v, G.w u v = 0 ∨ G.w u v = 1) →
        ∀ s t : Fin n, s ≠ t →
          s ∈ (((P n).eval G.cut) s t).shore ∧
          t ∉ (((P n).eval G.cut) s t).shore ∧
          (((P n).eval G.cut) s t).value = G.cut (((P n).eval G.cut) s t).shore ∧
          (∃ k : ℕ, (((P n).eval G.cut) s t).value = k) ∧
          (∀ S : Finset (Fin n), s ∈ S → t ∉ S →
            G.cut (((P n).eval G.cut) s t).shore ≤ G.cut S)) ∧
      (∀ (n : ℕ) (read : Finset (Fin n) → ℝ), (P n).cost read ≤ q n) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
        (q n : ℝ) ≤ C * (n : ℝ) ^ (5 / 3 : ℝ) *
          ((Nat.clog 2 (2 * n + 2) + 1 : ℕ) : ℝ) ^ 5) ∧
      ((fun n : ℕ => (q n : ℝ)) =o[atTop] fun n => (n : ℝ) ^ 2) := by
  obtain ⟨q, P, hcorrect, hcap, hbound, hlittle⟩ := deterministic_allPairs
  refine ⟨q, P, ?_, hcap, hbound, hlittle⟩
  intro n G hG s t hst
  obtain ⟨hmin, hval⟩ := hcorrect n G hG s t hst
  obtain ⟨k, hk⟩ := honest_cut_is_natural G hG (((P n).eval G.cut) s t).shore
  exact ⟨hmin.1, hmin.2.1, hval, ⟨k, hval.trans hk⟩, hmin.2.2⟩

#audit_cut_decl Paper2HeadlineVerification.allPairs_expanded
#print axioms Paper2HeadlineVerification.allPairs_expanded

/-- The three-query example program from the reading guide in `README.md`. -/
example : DTree (Finset (Fin 3)) ℝ ℝ 3 :=
  DTree.query {0} fun a => DTree.query {1} fun b => DTree.query {0, 1} fun c =>
    DTree.pure (a + b - c)

/-- On every graph, the example program returns twice the weight of the edge `{0, 1}`. -/
theorem three_query_example_eval (G : WeightedGraph (Fin 3)) :
    (DTree.query {0} fun a => DTree.query {1} fun b => DTree.query {0, 1} fun c =>
      DTree.pure (a + b - c) : DTree (Finset (Fin 3)) ℝ ℝ 3).eval G.cut = 2 * G.w 0 1 := by
  have h0 : ({0} : Finset (Fin 3))ᶜ = {1, 2} := by decide
  have h1 : ({1} : Finset (Fin 3))ᶜ = {0, 2} := by decide
  have h01 : ({0, 1} : Finset (Fin 3))ᶜ = {2} := by decide
  simp only [DTree.eval_query, DTree.eval_pure, WeightedGraph.cut, h0, h1, h01]
  simp [G.symm 1 0]
  ring

#audit_cut_decl Paper2HeadlineVerification.three_query_example_eval

end Paper2HeadlineVerification
