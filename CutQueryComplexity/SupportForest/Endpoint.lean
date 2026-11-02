import CutQueryComplexity.SupportForest.Main
import CutQueryComplexity.DetMinCut.Parameters

/-! # Endpoints: the positive-support forest and the connectivity test

`forestBudget n = n + 2n + 4n ⌈log₂ n⌉` is the query cap: the degree queries (at most one per
merge, at most `n − 1` in all, charged as `n`), the at most `2n` fiber tests, and at most
`n − 1` merges of two searches of at most `2 ⌈log₂ n⌉` cut queries each. It is at most
`7 n L(n)` with `L(n) = max 1 ⌈log₂ 2n⌉`, hence `O(n log(2n))`.

`exists_support_forest` is the lemma: one decision tree per `n`, chosen before the graph,
that returns a maximal spanning forest of the positive support of every graph on `Fin n`.
`exists_connectivity_test` runs it and reports `none` when the support is connected and
otherwise a proper shore of cut value zero.
-/

namespace CutQueryComplexity
namespace SupportForest

open WeightedGraph Search Search.Comp Finset DetMinCut

/-! ## The budget -/

/-- The query cap of the forest routine. -/
def forestBudget (n : ℕ) : ℕ := n + 2 * n + 4 * n * Nat.clog 2 n

/-- The cap is `O(n log(2n))`: at most `7 n L(n)`. -/
theorem forestBudget_le_linear_log (n : ℕ) : forestBudget n ≤ 7 * n * logL n := by
  have h1 := one_le_logL' n
  have h2 : Nat.clog 2 n ≤ logL n := clog_le_logL le_rfl
  unfold forestBudget
  have h3 : 3 * n ≤ 3 * n * logL n := by nlinarith
  have h4 : 4 * n * Nat.clog 2 n ≤ 4 * n * logL n := Nat.mul_le_mul_left _ h2
  nlinarith

/-! ## The forest -/

/-- **Positive-support forest.** One decision tree per `n`, selected before the graph, that
learns a maximal spanning forest of the positive support of every graph on `Fin n` with at
most `forestBudget n` cut queries. -/
theorem exists_support_forest (n : ℕ) :
    ∃ D : DTree (Finset (Fin n)) ℝ (Option (Output (Fin n))) (forestBudget n),
      (∀ read, D.cost read ≤ forestBudget n) ∧
      ∀ G : WeightedGraph (Fin n), ∃ out, D.eval G.cut = some out ∧ Correct G out := by
  refine ⟨(program (V := Fin n)).toDTree (forestBudget n), fun read => DTree.cost_le _ read,
    fun G => ?_⟩
  obtain ⟨hc, hcost⟩ := program_spec (V := Fin n) G
  exact ⟨_, toDTree_eval _ _ (by simpa [forestBudget] using hcost), hc⟩

/-! ## The connectivity test -/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- From a forest output: `none` if every vertex has the representative of `x₀`, otherwise
the fiber of `x₀`. -/
def Output.test (out : Output V) (x₀ : V) : Option (Finset V) :=
  if ∀ x, out.r x = out.r x₀ then none else some (classOf out.r (out.r x₀))

theorem Correct.test_of_connected {G : WeightedGraph V} {out : Output V} (h : Correct G out)
    (x₀ : V) (hc : G.support.Connected) : out.test x₀ = none := by
  unfold Output.test
  rw [ite_eq_left]
  intro x
  exact (h.fiber_iff x x₀).mpr (hc.preconnected x x₀)

theorem Correct.test_of_not_connected {G : WeightedGraph V} {out : Output V}
    (h : Correct G out) (x₀ : V) (hc : ¬ G.support.Connected) :
    ∃ S, out.test x₀ = some S ∧ ProperShore S ∧ G.cut S = 0 := by
  have hall : ¬ ∀ x, out.r x = out.r x₀ := by
    intro hall
    apply hc
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    exact ⟨x₀, fun x => (h.fiber_iff x₀ x).mp (hall x).symm⟩
  unfold Output.test
  rw [ite_eq_right hall]
  push Not at hall
  obtain ⟨y, hy⟩ := hall
  refine ⟨_, rfl, ⟨⟨x₀, by simp⟩, fun huniv => hy ?_⟩, ?_⟩
  · have : y ∈ classOf out.r (out.r x₀) := huniv ▸ mem_univ y
    exact (mem_classOf _ _ _).mp this
  · have : classOf out.r (out.r x₀) = reachClass G x₀ := by
      ext z
      rw [mem_classOf, mem_reachClass, ← h.fiber_iff, eq_comm]
    rw [this]
    exact cut_reachClass G x₀

/-- **Connectivity test.** One decision tree per `n ≥ 2`, selected before the graph, that
returns `none` when the positive support is connected and otherwise a proper shore of cut
value zero, with at most `forestBudget n` cut queries. -/
theorem exists_connectivity_test (n : ℕ) (hn : 2 ≤ n) :
    ∃ D : DTree (Finset (Fin n)) ℝ (Option (Option (Finset (Fin n)))) (forestBudget n),
      ∀ G : WeightedGraph (Fin n),
        (G.support.Connected → D.eval G.cut = some none) ∧
        (¬ G.support.Connected → ∃ S, D.eval G.cut = some (some S) ∧
            ProperShore S ∧ G.cut S = 0) := by
  let x₀ : Fin n := ⟨0, by omega⟩
  refine ⟨((program (V := Fin n)).map fun out => out.test x₀).toDTree (forestBudget n),
    fun G => ?_⟩
  obtain ⟨hc, hcost⟩ := program_spec (V := Fin n) G
  have hev := toDTree_eval G.cut ((program (V := Fin n)).map fun out => out.test x₀)
    (q := forestBudget n) (by simpa [forestBudget] using hcost)
  rw [eval_map] at hev
  refine ⟨fun hconn => ?_, fun hconn => ?_⟩
  · rw [hev, hc.test_of_connected x₀ hconn]
  · obtain ⟨S, hS, hprop, hzero⟩ := hc.test_of_not_connected x₀ hconn
    exact ⟨S, by rw [hev, hS], hprop, hzero⟩

end SupportForest
end CutQueryComplexity
