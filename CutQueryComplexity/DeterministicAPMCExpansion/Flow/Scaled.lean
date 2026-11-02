import CutQueryComplexity.DeterministicAPMCExpansion.Flow.BFS
import CutQueryComplexity.DirectedUnitST.Blocking.Phase

/-!
# Public integer scaling of the hidden internal graph

Scaling is arithmetic on received answers. The public program contains no
hidden graph, and the transformation preserves the exact number of queries
on every real-valued transcript. Only the internal edges are scaled; the
two known terminal stars retain their public integral capacities.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.Flow

open Finset Certificate DirectedCertificate AllPairsAudit
open scoped Classical
noncomputable section

/-- Simulate a scaled cut oracle with one original query per scaled query. -/
def scaleAnswers {I O : Type} (C : ℕ) : Prog I ℝ O → Prog I ℝ O
  | .pure out => .pure out
  | .query query next => .query query (fun answer => scaleAnswers C (next (C * answer)))

theorem scaleAnswers_run {I O : Type} (C : ℕ) (program : Prog I ℝ O)
    (read : I → ℝ) :
    (scaleAnswers C program).run read = program.run (fun i => C * read i) := by
  induction program with
  | pure out => rfl
  | query query next ih => simp only [scaleAnswers, Prog.run, ih]

theorem scaleAnswers_eval {I O : Type} (C : ℕ) (program : Prog I ℝ O)
    (read : I → ℝ) :
    (scaleAnswers C program).eval read = program.eval (fun i => C * read i) :=
  congrArg Prod.fst (scaleAnswers_run C program read)

theorem scaleAnswers_cost {I O : Type} (C : ℕ) (program : Prog I ℝ O)
    (read : I → ℝ) :
    (scaleAnswers C program).cost read = program.cost (fun i => C * read i) :=
  congrArg Prod.snd (scaleAnswers_run C program read)

variable {V : Type} [Fintype V] [DecidableEq V]

def scaledInternal (G : WeightedGraph V) (C : ℕ) : WeightedGraph V :=
  G.scale (C : ℝ) (Nat.cast_nonneg C)

theorem scaledInternal_cut (G : WeightedGraph V) (C : ℕ) :
    (scaledInternal G C).cut = fun S => C * G.cut S := by
  funext S
  exact G.cut_scale (C : ℝ) (Nat.cast_nonneg C) S

/-- The scaled program is chosen before the hidden graph is supplied. -/
theorem scaleAnswers_graph_run {O : Type} (C : ℕ)
    (program : Prog (Finset V) ℝ O) (G : WeightedGraph V) :
    (scaleAnswers C program).run G.cut = program.run (scaledInternal G C).cut := by
  rw [scaleAnswers_run, scaledInternal_cut]

def IntegralWeights (G : WeightedGraph V) : Prop :=
  ∀ u v, ∃ k : ℕ, G.w u v = k

theorem scaledInternal_integral {G : WeightedGraph V} (hG : Unweighted G) (C : ℕ) :
    IntegralWeights (scaledInternal G C) := by
  intro u v
  rcases hG u v with hzero | hone
  · refine ⟨0, ?_⟩
    simp only [scaledInternal, WeightedGraph.scale, hzero, mul_zero, Nat.cast_zero]
  · refine ⟨C, ?_⟩
    simp only [scaledInternal, WeightedGraph.scale, hone, mul_one]

theorem twoStar_integral {G : WeightedGraph V} (hG : IntegralWeights G) (a z : V → ℕ) :
    DirectedUnitST.Blocking.IntegralCap (directed (twoStar G a z)) := by
  intro u v
  cases u with
  | inl u =>
      cases v with
      | inl v => simpa only [directed, twoStar_internal] using hG u v
      | inr i =>
          by_cases hi : i = 0
          · exact ⟨a u, by simp [directed, twoStar, embedded, knownStars, terminalCapacity, hi]⟩
          · exact ⟨z u, by simp [directed, twoStar, embedded, knownStars, terminalCapacity, hi]⟩
  | inr i =>
      cases v with
      | inl v =>
          by_cases hi : i = 0
          · exact ⟨a v, by simp [directed, twoStar, embedded, knownStars, terminalCapacity, hi]⟩
          · exact ⟨z v, by simp [directed, twoStar, embedded, knownStars, terminalCapacity, hi]⟩
      | inr j => exact ⟨0, by simp [directed, twoStar, embedded, knownStars]⟩

theorem scaled_internal_pair_bound {G : WeightedGraph V} (hG : Unweighted G)
    (C : ℕ) (a z : V → ℕ) (u v : V) :
    (directed (twoStar (scaledInternal G C) a z)).c (.inl u) (.inl v) +
      (directed (twoStar (scaledInternal G C) a z)).c (.inl v) (.inl u) ≤ 2 * (C : ℝ) := by
  have hweight := unweighted_edge_le_one hG u v
  have hscaled := mul_le_mul_of_nonneg_left hweight (Nat.cast_nonneg C : (0 : ℝ) ≤ C)
  simp only [directed, twoStar_internal, scaledInternal, WeightedGraph.scale, G.symm v u]
  nlinarith

end
end CutQueryComplexity.DeterministicAPMCExpansion.Flow

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.scaleAnswers_graph_run
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.twoStar_integral
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.scaled_internal_pair_bound
