import CutQueryComplexity.Reconstruction.WeightedDirected.Program
import CutQueryComplexity.Probability.Events

/-! Six exact classical exports for arbitrary nonnegative real directed capacities.
The public program is chosen before the graph. Randomized exports use the actual
point-mass embedding and retain both the output and the executed query counter. -/
namespace CutQueryComplexity.Reconstruction.WeightedDirected
open DirectedCertificate Probability
open scoped Classical
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Exact original outgoing-cut shore and value contract. -/
def TerminalGood (G : WeightedDiGraph V) (s t : V) (a : AllPairs.STAnswer V) : Prop :=
  s ∈ a.shore ∧ t ∉ a.shore ∧ a.value = G.out a.shore ∧
    ∀ T, s ∈ T → t ∉ T → G.out a.shore ≤ G.out T

def AllPairsGood (G : WeightedDiGraph V) (a : AllPairs.Answers V) : Prop :=
  ∀ s t, s ≠ t → TerminalGood G s t (a s t)

def GlobalGood (G : WeightedDiGraph V) (a : AllPairs.STAnswer V) : Prop :=
  IsGlobalMinCut G a.shore ∧ a.value = G.out a.shore ∧ a.value = G.minValue

def terminalProgram (s t : V) :
    DTree (Finset V) ℝ (AllPairs.STAnswer V) (queryBudget V) :=
  reconstruct.map fun D => D.terminalAnswer s t

def allPairsProgram : DTree (Finset V) ℝ (AllPairs.Answers V) (queryBudget V) :=
  reconstruct.map DirectedData.allPairsAnswers

def globalProgram : DTree (Finset V) ℝ (AllPairs.STAnswer V) (queryBudget V) :=
  reconstruct.map DirectedData.globalAnswer

def randomizedTerminal (s t : V) :
    RTree (Finset V) ℝ (AllPairs.STAnswer V) (queryBudget V) :=
  RTree.ofDeterministic (terminalProgram s t)

def randomizedAllPairs : RTree (Finset V) ℝ (AllPairs.Answers V) (queryBudget V) :=
  RTree.ofDeterministic allPairsProgram

def randomizedGlobal : RTree (Finset V) ℝ (AllPairs.STAnswer V) (queryBudget V) :=
  RTree.ofDeterministic globalProgram

omit [DecidableEq V] in
theorem quadratic_all_sizes : queryBudget V ≤ 3 * Fintype.card V ^ 2 := by
  by_cases h : Fintype.card V = 0
  · simp [queryBudget_eq, h]
  · exact queryBudget_quadratic (by omega)

theorem terminal_correct (G : WeightedDiGraph V) {s t : V} (hst : s ≠ t) :
    TerminalGood G s t ((terminalProgram s t).eval G.out) := by
  simpa [terminalProgram, reconstruct_correct, TerminalGood] using
    (DirectedData.terminalAnswer_correct (⟨G.sym, G.imbalance⟩ : DirectedData V) G rfl rfl hst)

theorem allPairs_correct (G : WeightedDiGraph V) :
    AllPairsGood G ((allPairsProgram (V := V)).eval G.out) := by
  simpa [allPairsProgram, reconstruct_correct, AllPairsGood, TerminalGood] using
    (DirectedData.allPairsAnswers_correct (⟨G.sym, G.imbalance⟩ : DirectedData V) G rfl rfl)

theorem global_correct (G : WeightedDiGraph V) (hn : 2 ≤ Fintype.card V) :
    GlobalGood G ((globalProgram (V := V)).eval G.out) := by
  simpa [globalProgram, reconstruct_correct, GlobalGood] using
    (DirectedData.globalAnswer_correct (⟨G.sym, G.imbalance⟩ : DirectedData V) G rfl rfl hn)

/-- The exact reconstruction count survives arbitrary free offline optimization. -/
theorem mapped_run {O : Type} (f : DirectedData V → O) (read : Finset V → ℝ) :
    DTree.run read (reconstruct.map f) =
      (f (publicData fun i => read (schedule i)), queryBudget V) := by
  simp [DTree.run_map, reconstruct_run]

/-- Actual stochastic law, including the charged schedule on every reply oracle. -/
theorem randomized_mapped_run {O : Type} (f : DirectedData V → O)
    (read : Finset V → ℝ) :
    RTree.run read (RTree.ofDeterministic (reconstruct.map f)) =
      PMF.pure (f (publicData fun i => read (schedule i)), queryBudget V) := by
  rw [RTree.run_ofDeterministic, mapped_run]

theorem deterministic_terminal (s t : V) (hst : s ≠ t) :
    ∃ P : DTree (Finset V) ℝ (AllPairs.STAnswer V) (queryBudget V),
      P = terminalProgram s t ∧
      (∀ read : Finset V → ℝ, P.cost read ≤ 3 * Fintype.card V ^ 2) ∧
      ∀ G : WeightedDiGraph V, TerminalGood G s t (P.eval G.out) := by
  exact ⟨terminalProgram s t, rfl,
    fun read => (DTree.cost_le _ read).trans quadratic_all_sizes,
    fun G => terminal_correct G hst⟩

theorem deterministic_allPairs :
    ∃ P : DTree (Finset V) ℝ (AllPairs.Answers V) (queryBudget V),
      P = allPairsProgram ∧
      (∀ read : Finset V → ℝ, P.cost read ≤ 3 * Fintype.card V ^ 2) ∧
      ∀ G : WeightedDiGraph V, AllPairsGood G (P.eval G.out) := by
  exact ⟨allPairsProgram, rfl,
    fun read => (DTree.cost_le _ read).trans quadratic_all_sizes, allPairs_correct⟩

theorem deterministic_global (hn : 2 ≤ Fintype.card V) :
    ∃ P : DTree (Finset V) ℝ (AllPairs.STAnswer V) (queryBudget V),
      P = globalProgram ∧
      (∀ read : Finset V → ℝ, P.cost read ≤ 3 * Fintype.card V ^ 2) ∧
      ∀ G : WeightedDiGraph V, GlobalGood G (P.eval G.out) := by
  exact ⟨globalProgram, rfl,
    fun read => (DTree.cost_le _ read).trans quadratic_all_sizes, fun G => global_correct G hn⟩

theorem randomized_terminal (s t : V) (hst : s ≠ t) :
    ∃ P : RTree (Finset V) ℝ (AllPairs.STAnswer V) (queryBudget V),
      P = randomizedTerminal s t ∧
      (∀ read : Finset V → ℝ, ∀ r ∈ (RTree.run read P).support,
        r.2 ≤ 3 * Fintype.card V ^ 2) ∧
      ∀ G : WeightedDiGraph V,
        RTree.run G.out P = PMF.pure ((terminalProgram s t).eval G.out, queryBudget V) ∧
        mass (P.eval G.out) (fun a => ¬ TerminalGood G s t a) = 0 := by
  refine ⟨randomizedTerminal s t, rfl, fun read r hr =>
    (RTree.cost_le _ read hr).trans quadratic_all_sizes, fun G => ?_⟩
  have he : RTree.run G.out (randomizedTerminal s t) =
      PMF.pure ((terminalProgram s t).eval G.out, queryBudget V) := by
    simp only [randomizedTerminal, terminalProgram, randomized_mapped_run,
      DTree.eval_map, reconstruct_correct, publicData_correct]
  refine ⟨he, ?_⟩
  simp [RTree.eval, he, terminal_correct G hst]

theorem randomized_allPairs :
    ∃ P : RTree (Finset V) ℝ (AllPairs.Answers V) (queryBudget V),
      P = randomizedAllPairs ∧
      (∀ read : Finset V → ℝ, ∀ r ∈ (RTree.run read P).support,
        r.2 ≤ 3 * Fintype.card V ^ 2) ∧
      ∀ G : WeightedDiGraph V,
        RTree.run G.out P = PMF.pure (allPairsProgram.eval G.out, queryBudget V) ∧
        mass (P.eval G.out) (fun a => ¬ AllPairsGood G a) = 0 := by
  refine ⟨randomizedAllPairs, rfl, fun read r hr =>
    (RTree.cost_le _ read hr).trans quadratic_all_sizes, fun G => ?_⟩
  have he : RTree.run G.out (randomizedAllPairs (V := V)) =
      PMF.pure (allPairsProgram.eval G.out, queryBudget V) := by
    simp only [randomizedAllPairs, allPairsProgram, randomized_mapped_run,
      DTree.eval_map, reconstruct_correct, publicData_correct]
  refine ⟨he, ?_⟩
  simp [RTree.eval, he, allPairs_correct G]

theorem randomized_global (hn : 2 ≤ Fintype.card V) :
    ∃ P : RTree (Finset V) ℝ (AllPairs.STAnswer V) (queryBudget V),
      P = randomizedGlobal ∧
      (∀ read : Finset V → ℝ, ∀ r ∈ (RTree.run read P).support,
        r.2 ≤ 3 * Fintype.card V ^ 2) ∧
      ∀ G : WeightedDiGraph V,
        RTree.run G.out P = PMF.pure (globalProgram.eval G.out, queryBudget V) ∧
        mass (P.eval G.out) (fun a => ¬ GlobalGood G a) = 0 := by
  refine ⟨randomizedGlobal, rfl, fun read r hr =>
    (RTree.cost_le _ read hr).trans quadratic_all_sizes, fun G => ?_⟩
  have he : RTree.run G.out (randomizedGlobal (V := V)) =
      PMF.pure (globalProgram.eval G.out, queryBudget V) := by
    simp only [randomizedGlobal, globalProgram, randomized_mapped_run,
      DTree.eval_map, reconstruct_correct, publicData_correct]
  refine ⟨he, ?_⟩
  simp [RTree.eval, he, global_correct G hn]

/-- The certificate consists of the same public measured shores. -/
def queries (V : Type) [Fintype V] [DecidableEq V] : Finset (Finset V) :=
  Finset.univ.image (schedule (V := V))

theorem queries_card : (queries V).card ≤ queryBudget V :=
  Finset.card_image_le.trans (by rw [Finset.card_univ]; rfl)

/-- Competitors with arbitrary nonnegative real capacities agreeing on this
family have the entire same outgoing-cut function, though their individual arc
orientations may differ. -/
theorem queries_cut_equivalent (G H : WeightedDiGraph V)
    (h : Consistent G H (queries V)) (S : Finset V) : H.out S = G.out S := by
  have ht : (fun i : QueryIndex V => H.out (schedule i)) =
      fun i => G.out (schedule i) := by
    funext i
    exact h _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have he : (reconstruct (V := V)).eval H.out = (reconstruct (V := V)).eval G.out := by
    simp only [DTree.eval, reconstruct_run, ht]
  rw [← reconstruct_cut_correct H S, he, reconstruct_cut_correct G S]

/-- The same original optimum answers remain valid in every nonnegative real
competitor. -/
theorem allPairs_certificate (G : WeightedDiGraph V) :
    ∃ Q : Finset (Finset V), Q.card ≤ 3 * Fintype.card V ^ 2 ∧
      ∃ out : AllPairs.Answers V, AllPairsGood G out ∧
        ∀ H : WeightedDiGraph V, Consistent G H Q →
          (∀ S, H.out S = G.out S) ∧ AllPairsGood H out := by
  refine ⟨queries V, queries_card.trans quadratic_all_sizes,
    (allPairsProgram (V := V)).eval G.out, allPairs_correct G, fun H h => ?_⟩
  have he := queries_cut_equivalent G H h
  refine ⟨he, fun s t hst => ?_⟩
  simpa only [TerminalGood, he] using allPairs_correct G s t hst

end
end CutQueryComplexity.Reconstruction.WeightedDirected
