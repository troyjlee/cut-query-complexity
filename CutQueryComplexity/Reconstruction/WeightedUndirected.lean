import CutQueryComplexity.Primitive.Learn
import CutQueryComplexity.AllPairs.Representation
import CutQueryComplexity.Certificate.Flow
import CutQueryComplexity.Model.RandomizedComposition
import CutQueryComplexity.Probability.Events

/-! Exact quadratic exports for arbitrary nonnegative real undirected weights.
The public schedule of singletons and pairs recovers the whole graph, after
which terminal and all-pairs minima are selected offline. Randomized exports use
the actual point-mass embedding, and the same schedule is a certificate against
every nonnegative real competitor. -/
namespace CutQueryComplexity.Reconstruction.WeightedUndirected

open Finset Probability
open scoped Classical
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

abbrev queryBudget (V : Type) [Fintype V] : ℕ := Fintype.card V + (Fintype.card V).choose 2

omit [DecidableEq V] in
theorem queryBudget_le : queryBudget V ≤ Fintype.card V ^ 2 := by
  unfold queryBudget
  generalize Fintype.card V = n
  rw [Nat.choose_two_right]
  cases n with
  | zero => simp
  | succ m =>
    rw [Nat.add_sub_cancel]
    have hd := Nat.div_le_self ((m + 1) * m) 2
    nlinarith

/-- Exact original shore and value contract for one terminal pair. -/
def TerminalGood (G : WeightedGraph V) (s t : V) (a : AllPairs.STAnswer V) : Prop :=
  IsSTMinCut G s t a.shore ∧ a.value = G.cut a.shore

/-- Offline selection from an explicit graph; uncharged. -/
def terminalAnswer (H : WeightedGraph V) (s t : V) : AllPairs.STAnswer V :=
  ⟨AllPairs.offlineST H s t, H.cut (AllPairs.offlineST H s t)⟩

def allPairsAnswers (H : WeightedGraph V) : AllPairs.Answers V :=
  fun s t => terminalAnswer H s t

theorem terminalAnswer_correct (H : WeightedGraph V) {s t : V} (hst : s ≠ t) :
    TerminalGood H s t (terminalAnswer H s t) :=
  ⟨AllPairs.offlineST_correct H hst, rfl⟩

theorem allPairsAnswers_correct (H : WeightedGraph V) :
    AllPairs.allPairsGood H (allPairsAnswers H) :=
  fun _ _ hst => terminalAnswer_correct H hst

def terminalProgram (s t : V) :
    DTree (Finset V) ℝ (AllPairs.STAnswer V) (queryBudget V) :=
  reconstruct.map fun H => terminalAnswer H s t

def allPairsProgram : DTree (Finset V) ℝ (AllPairs.Answers V) (queryBudget V) :=
  reconstruct.map allPairsAnswers

def randomizedTerminal (s t : V) :
    RTree (Finset V) ℝ (AllPairs.STAnswer V) (queryBudget V) :=
  RTree.ofDeterministic (terminalProgram s t)

def randomizedAllPairs : RTree (Finset V) ℝ (AllPairs.Answers V) (queryBudget V) :=
  RTree.ofDeterministic allPairsProgram

theorem reconstruct_eval (G : WeightedGraph V) :
    (reconstruct (V := V)).eval G.cut = G := by
  simp [DTree.eval, reconstruct_run]

theorem terminal_correct (G : WeightedGraph V) {s t : V} (hst : s ≠ t) :
    TerminalGood G s t ((terminalProgram s t).eval G.cut) := by
  simpa [terminalProgram, reconstruct_eval] using terminalAnswer_correct G hst

theorem allPairs_correct (G : WeightedGraph V) :
    AllPairs.allPairsGood G ((allPairsProgram (V := V)).eval G.cut) := by
  simpa [allPairsProgram, reconstruct_eval] using allPairsAnswers_correct G

theorem deterministic_terminal (s t : V) (hst : s ≠ t) :
    ∃ P : DTree (Finset V) ℝ (AllPairs.STAnswer V) (queryBudget V),
      P = terminalProgram s t ∧
      (∀ read : Finset V → ℝ, P.cost read ≤ Fintype.card V ^ 2) ∧
      ∀ G : WeightedGraph V, TerminalGood G s t (P.eval G.cut) :=
  ⟨terminalProgram s t, rfl, fun read => (DTree.cost_le _ read).trans queryBudget_le,
    fun G => terminal_correct G hst⟩

theorem deterministic_allPairs :
    ∃ P : DTree (Finset V) ℝ (AllPairs.Answers V) (queryBudget V),
      P = allPairsProgram ∧
      (∀ read : Finset V → ℝ, P.cost read ≤ Fintype.card V ^ 2) ∧
      ∀ G : WeightedGraph V, AllPairs.allPairsGood G (P.eval G.cut) :=
  ⟨allPairsProgram, rfl, fun read => (DTree.cost_le _ read).trans queryBudget_le,
    allPairs_correct⟩

theorem randomized_terminal (s t : V) (hst : s ≠ t) :
    ∃ P : RTree (Finset V) ℝ (AllPairs.STAnswer V) (queryBudget V),
      P = randomizedTerminal s t ∧
      (∀ read : Finset V → ℝ, ∀ r ∈ (RTree.run read P).support,
        r.2 ≤ Fintype.card V ^ 2) ∧
      ∀ G : WeightedGraph V,
        RTree.run G.cut P = PMF.pure ((terminalProgram s t).eval G.cut, queryBudget V) ∧
        mass (P.eval G.cut) (fun a => ¬ TerminalGood G s t a) = 0 := by
  refine ⟨randomizedTerminal s t, rfl, fun read r hr =>
    (RTree.cost_le _ read hr).trans queryBudget_le, fun G => ?_⟩
  have he : RTree.run G.cut (randomizedTerminal s t) =
      PMF.pure ((terminalProgram s t).eval G.cut, queryBudget V) := by
    rw [randomizedTerminal, RTree.run_ofDeterministic, terminalProgram, DTree.run_map,
      reconstruct_run, DTree.eval_map, reconstruct_eval]
  refine ⟨he, ?_⟩
  simp [RTree.eval, he, terminal_correct G hst]

theorem randomized_allPairs :
    ∃ P : RTree (Finset V) ℝ (AllPairs.Answers V) (queryBudget V),
      P = randomizedAllPairs ∧
      (∀ read : Finset V → ℝ, ∀ r ∈ (RTree.run read P).support,
        r.2 ≤ Fintype.card V ^ 2) ∧
      ∀ G : WeightedGraph V,
        RTree.run G.cut P = PMF.pure (allPairsProgram.eval G.cut, queryBudget V) ∧
        mass (P.eval G.cut) (fun a => ¬ AllPairs.allPairsGood G a) = 0 := by
  refine ⟨randomizedAllPairs, rfl, fun read r hr =>
    (RTree.cost_le _ read hr).trans queryBudget_le, fun G => ?_⟩
  have he : RTree.run G.cut (randomizedAllPairs (V := V)) =
      PMF.pure (allPairsProgram.eval G.cut, queryBudget V) := by
    rw [randomizedAllPairs, RTree.run_ofDeterministic, allPairsProgram, DTree.run_map,
      reconstruct_run, DTree.eval_map, reconstruct_eval]
  refine ⟨he, ?_⟩
  simp [RTree.eval, he, allPairs_correct G]

/-- The certificate consists of the same public singleton and pair shores. -/
def queries (V : Type) [Fintype V] [DecidableEq V] : Finset (Finset V) :=
  univ.image (reconstructionShore (V := V))

theorem queries_card : (queries V).card ≤ queryBudget V := by
  exact card_image_le.trans (by rw [card_univ, card_reconstructionIndex])

/-- A competitor with arbitrary nonnegative real weights that agrees on the
schedule is the original graph. -/
theorem eq_of_consistent {G H : WeightedGraph V}
    (h : Certificate.Consistent G H (queries V)) : H = G := by
  have ht : (fun j => H.cut (reconstructionShore j)) =
      fun j => G.cut (reconstructionShore j) := by
    funext j
    exact h _ (mem_image_of_mem _ (mem_univ j))
  rw [← reconstructionDecode_correct H, ← reconstructionDecode_correct G, ht]

/-- One quadratic certificate fixes all original optimum shores and values
against every nonnegative real competitor. -/
theorem allPairs_certificate (G : WeightedGraph V) :
    ∃ Q : Finset (Finset V), Q.card ≤ Fintype.card V ^ 2 ∧
      ∃ out : AllPairs.Answers V, AllPairs.allPairsGood G out ∧
        ∀ H : WeightedGraph V, Certificate.Consistent G H Q →
          H = G ∧ AllPairs.allPairsGood H out := by
  refine ⟨queries V, queries_card.trans queryBudget_le, allPairsAnswers G,
    allPairsAnswers_correct G, fun H h => ?_⟩
  have he := eq_of_consistent h
  exact ⟨he, he ▸ allPairsAnswers_correct G⟩

end
end CutQueryComplexity.Reconstruction.WeightedUndirected
