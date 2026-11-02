import CutQueryComplexity.CanonicalST.Core
import CutQueryComplexity.CanonicalST.Decision
import CutQueryComplexity.CanonicalST.Reachability

/-!
# Public canonical terminal cut, value, and integral flow program

Preprocessing is performed once. Binary target decisions retain their learned
edges. A maximum flow is selected only in the explicit final learned graph;
the proved target search identifies its value with the original optimum.
Original residual reachability then supplies the actual minimizing shore, and
one final original cut query reports its value. No hidden graph is an input to
any executable selector or continuation.
-/

set_option autoImplicit false

namespace CutQueryComplexity.CanonicalST

open Finset WeightedGraph Certificate
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

def degreeThreshold (n : ℕ) : ℕ := max 2 ⌈Real.sqrt (n : ℝ)⌉₊

theorem degreeThreshold_two_le (n : ℕ) : 2 ≤ degreeThreshold n := le_max_left _ _

/-- The original singleton cut strictly bounds the terminal optimum. -/
theorem terminalValue_lt_card {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G)
    {s t : V} (hst : s ≠ t) : Augmentation.terminalValue G s t < Fintype.card V := by
  have hsum : (∑ v, G.w s v) < ∑ _v : V, (1 : ℝ) :=
    sum_lt_sum (fun v _ => AllPairsAudit.unweighted_edge_le_one hG s v)
      ⟨s, mem_univ s, by simp [G.diag]⟩
  have hcut : G.cut {s} < Fintype.card V := by
    simpa only [WeightedGraph.cut_singleton, WeightedGraph.degree, sum_const,
      card_univ, nsmul_eq_mul, mul_one] using hsum
  exact (Augmentation.terminalValue_le_cut G hst (mem_singleton_self s)
    (by simpa only [mem_singleton] using Ne.symm hst)).trans_lt hcut

structure Output (V : Type) where
  shore : Finset V
  value : ℝ
  flow : V → V → ℝ

def OutputSpec (G : WeightedGraph V) (s t : V) (out : Output V) : Prop :=
  s ∈ out.shore ∧ t ∉ out.shore ∧ out.value = G.cut out.shore ∧
    (∀ S : Finset V, s ∈ S → t ∉ S → G.cut out.shore ≤ G.cut S) ∧
    Augmentation.FlowSpec G s t out.value out.flow

def valueQuery (S : Finset V) (g : V → V → ℝ) :
    DTree (Finset V) ℝ (Output V) 1 :=
  DTree.query S fun value => DTree.pure ⟨S, value, g⟩

theorem valueQuery_eval (read : Finset V → ℝ) (S : Finset V) (g : V → V → ℝ) :
    (valueQuery S g).eval read = ⟨S, read S, g⟩ := rfl

def finishBudget (V : Type) [Fintype V] : ℕ := Reachability.queryBudget V + 1

def finish (A : CoreData V) (s t : V) (r : Decision.SearchResult V) :
    DTree (Finset V) ℝ (Output V) (finishBudget V) :=
  let g := Augmentation.maximumFlow (r.state.graph A) s t
  (Reachability.program g s).bind fun S => valueQuery S g

theorem finish_correct {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G)
    {A : CoreData V} {s t : V} (hst : s ≠ t) {P : Phase.State V}
    {r : Decision.SearchResult V} (hr : Decision.SearchSpec G A s t P r) :
    OutputSpec G s t ((finish A s t r).eval G.cut) := by
  let g := Augmentation.maximumFlow (r.state.graph A) s t
  have hlearned : Augmentation.FlowSpec (r.state.graph A) s t
      (Augmentation.terminalValue (r.state.graph A) s t) g :=
    Augmentation.maximumFlow_spec _ hr.invariant.unit hst
  have hg := hlearned.mono hr.invariant.subgraph
  obtain ⟨hs, ht, hcut, hmin, _⟩ := Reachability.program_correct hG hst hg hr.learned_eq
  have heval : (finish A s t r).eval G.cut =
      ⟨(Reachability.program g s).eval G.cut,
        G.cut ((Reachability.program g s).eval G.cut), g⟩ :=
    (DTree.eval_bind (Reachability.program g s) (fun S => valueQuery S g) G.cut).trans
      (valueQuery_eval G.cut ((Reachability.program g s).eval G.cut) g)
  rw [heval]
  refine ⟨hs, ht, rfl, hmin, ?_⟩
  change Augmentation.FlowSpec G s t (G.cut ((Reachability.program g s).eval G.cut)) g
  rw [hcut]
  exact hg

def continuationBudget (V : Type) [Fintype V] (D : ℕ) : ℕ :=
  Decision.searchBudget V D + finishBudget V

def continuation (A : CoreData V) (s t : V) (D : ℕ) :
    DTree (Finset V) ℝ (Option (Output V)) (continuationBudget V D) :=
  (Decision.searchProgram A s t D (Phase.State.initial A)).bind fun answer =>
    match answer with
    | none => DTree.pure none
    | some r => (finish A s t r).map some

def queryBudget (V : Type) [Fintype V] : ℕ :=
  coreBudget V (degreeThreshold (Fintype.card V)) +
    continuationBudget V (degreeThreshold (Fintype.card V))

/-- One graph-independent query tree, fixed by its labeled terminals. -/
def terminalProgram (s t : V) : DTree (Finset V) ℝ (Option (Output V)) (queryBudget V) :=
  (coreProgram (degreeThreshold (Fintype.card V))).bind fun A =>
    continuation A s t (degreeThreshold (Fintype.card V))

theorem terminalProgram_cost (s t : V) (read : Finset V → ℝ) :
    (terminalProgram s t).cost read ≤ queryBudget V := DTree.cost_le _ _

theorem continuation_correct {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G)
    {D : ℕ} {A : CoreData V} (hA : CoreSpec G D A) (hD : 2 ≤ D)
    {s t : V} (hst : s ≠ t) :
    ∃ out, (continuation A s t D).eval G.cut = some out ∧ OutputSpec G s t out := by
  obtain ⟨r, he, hr⟩ := Decision.searchProgram_correct hG hA hD
    (Phase.initial_invariant hA) hst (terminalValue_lt_card hG hst)
  refine ⟨(finish A s t r).eval G.cut, ?_, finish_correct hG hst hr⟩
  let next : Option (Decision.SearchResult V) →
      DTree (Finset V) ℝ (Option (Output V)) (finishBudget V) := fun answer =>
    match answer with
    | none => DTree.pure none
    | some r' => (finish A s t r').map some
  have hbind : (continuation A s t D).eval G.cut =
      (next ((Decision.searchProgram A s t D (Phase.State.initial A)).eval G.cut)).eval G.cut :=
    DTree.eval_bind (Decision.searchProgram A s t D (Phase.State.initial A)) next G.cut
  rw [hbind, he]
  exact DTree.eval_map some (finish A s t r) G.cut

theorem terminalProgram_correct (G : WeightedGraph V) (hG : AllPairsAudit.Unweighted G)
    {s t : V} (hst : s ≠ t) :
    ∃ out, (terminalProgram s t).eval G.cut = some out ∧ OutputSpec G s t out := by
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨s⟩
  have hD := degreeThreshold_two_le (Fintype.card V)
  have hcore := (coreProgram_spec (degreeThreshold (Fintype.card V)) hn (by omega)).2 G hG
  obtain ⟨out, he, hs⟩ := continuation_correct hG hcore hD hst
  refine ⟨out, ?_, hs⟩
  exact (DTree.eval_bind (coreProgram (degreeThreshold (Fintype.card V)))
    (fun A => continuation A s t (degreeThreshold (Fintype.card V))) G.cut).trans he

/-- The program is selected before the hidden graph. It returns an original
minimum shore, its queried value, and a feasible integral flow of that value. -/
theorem exists_terminal_query_program (s t : V) (hst : s ≠ t) :
    ∃ T : DTree (Finset V) ℝ (Option (Output V)) (queryBudget V),
      (∀ read : Finset V → ℝ, T.cost read ≤ queryBudget V) ∧
      ∀ G : WeightedGraph V, AllPairsAudit.Unweighted G →
        ∃ out, T.eval G.cut = some out ∧ OutputSpec G s t out := by
  exact ⟨terminalProgram s t, terminalProgram_cost s t,
    fun G hG => terminalProgram_correct G hG hst⟩

end
end CutQueryComplexity.CanonicalST

#print axioms CutQueryComplexity.CanonicalST.terminalValue_lt_card
#print axioms CutQueryComplexity.CanonicalST.finish_correct
#print axioms CutQueryComplexity.CanonicalST.terminalProgram_cost
#print axioms CutQueryComplexity.CanonicalST.terminalProgram_correct
#print axioms CutQueryComplexity.CanonicalST.exists_terminal_query_program
