import CutQueryComplexity.GHReduction.CanonicalCuts
import CutQueryComplexity.GHReduction.Contractions
import CutQueryComplexity.MinCut.RootedTree

/-! # Exact weighted primitive and witnessed cut-tree output

This is the only algorithmic input permitted in the final relative theorem:
a public canonical s-t program family on weighted compact instances. No
guide solver, single-source solver, or GH reduction is a field of the family.
The parameter `M` is fixed across all instance sizes.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical
open WeightedGraph

/-- Public input promise. Total capacity and the primitive's per-edge promise
are deliberately different conditions. -/
def InputPromise {V : Type} [Fintype V] [DecidableEq V]
    (M : ℕ) (G : WeightedGraph V) : Prop := G.IsIntegral ∧ G.edgeMass ≤ M

def SizeRegular (n : ℕ) (Q : ℕ → ℕ) : Prop :=
  ∀ s, 1 ≤ s → s ≤ n → n * Q s ≤ s * Q n

/-- Exact source-oriented weighted primitive, chosen before any hidden graph.
Only its correctness refers to capacities; its program arguments are public. -/
structure CanonicalSTFamily (M : ℕ) (Q : ℕ → ℕ) where
  program : ∀ n : ℕ, Fin n → Fin n →
    DTree (Finset (Fin n)) ℝ (Finset (Fin n)) (Q n)
  correct : ∀ (n : ℕ) (s t : Fin n), s ≠ t → ∀ G : WeightedGraph (Fin n),
    G.IsIntegral → (∀ u v, G.w u v ≤ M) →
      IsCanonicalSTCut G s t ((program n s t).eval G.cut)

variable {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

@[simp] theorem pull_equiv_image (e : V ≃ W) (S : Finset V) : pull e (S.image e) = S := by
  ext v
  simp

theorem stMinCut_equiv_image (G : WeightedGraph V) (e : V ≃ W) {s t : V}
    {S : Finset V} (hS : IsSTMinCut G s t S) :
    IsSTMinCut (G.contract e) (e s) (e t) (S.image e) := by
  refine ⟨by simpa using hS.1, by simpa using hS.2.1, fun A hsA htA => ?_⟩
  simp only [cut_contract, pull_equiv_image]
  exact hS.2.2 (pull e A) (by simpa using hsA) (by simpa using htA)

theorem stMinCut_equiv_pull (G : WeightedGraph V) (e : V ≃ W) {s t : V}
    {S : Finset W} (hS : IsSTMinCut (G.contract e) (e s) (e t) S) :
    IsSTMinCut G s t (pull e S) := by
  refine ⟨by simpa using hS.1, by simpa using hS.2.1, fun A hsA htA => ?_⟩
  have h := hS.2.2 (A.image e) (by simpa using hsA) (by simpa using htA)
  simpa only [cut_contract, pull_equiv_image] using h

theorem canonicalSTCut_equiv_pull (G : WeightedGraph V) (e : V ≃ W) {s t : V}
    {S : Finset W} (hS : IsCanonicalSTCut (G.contract e) (e s) (e t) S) :
    IsCanonicalSTCut G s t (pull e S) := by
  refine ⟨stMinCut_equiv_pull G e hS.1, fun A hA => ?_⟩
  have hsub := hS.2 (A.image e) (stMinCut_equiv_image G e hA)
  intro v hv
  have he : e v ∈ A.image e := hsub ((mem_pull e S v).mp hv)
  simpa using he

/-- Invoke the exact family on an actual finite type, compactly relabeled.
The original graph is not a computational argument. -/
def canonicalSTProgram {M : ℕ} {Q : ℕ → ℕ} (A : CanonicalSTFamily M Q)
    (s t : V) : DTree (Finset V) ℝ (Finset V) (Q (Fintype.card V)) :=
  (contractDetProgram (Fintype.equivFin V)
    (A.program (Fintype.card V) ((Fintype.equivFin V) s) ((Fintype.equivFin V) t))).map
      (pull (Fintype.equivFin V))

theorem canonicalSTProgram_correct {M : ℕ} {Q : ℕ → ℕ} (A : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (hG : InputPromise M G) {s t : V} (hst : s ≠ t) :
    IsCanonicalSTCut G s t ((canonicalSTProgram A s t).eval G.cut) := by
  rw [canonicalSTProgram, DTree.eval_map, contractDetProgram_eval]
  apply canonicalSTCut_equiv_pull G (Fintype.equivFin V)
  exact A.correct _ _ _ (fun he => hst ((Fintype.equivFin V).injective he)) _
    (integral_contract G hG.1 _) (contract_capacity_bounds G _ hG.2).1

theorem canonicalSTProgram_cost {M : ℕ} {Q : ℕ → ℕ} (A : CanonicalSTFamily M Q)
    (s t : V) (read : Finset V → ℝ) :
    (canonicalSTProgram A s t).cost read ≤ Q (Fintype.card V) := DTree.cost_le _ read

/-- The cut tree topology is independent of its real edge weights. The root's
entry is unused; every other vertex identifies its edge to its parent. -/
structure CutTree (V : Type) where
  topology : RootedTree V
  weight : V → ℝ
  nonneg : ∀ v, 0 ≤ weight v

/-- Fundamental shores witness exact minima and carry their original values.
The all-pairs bottleneck consequence is an additional theorem to be proved. -/
def IsGomoryHuTree (G : WeightedGraph V) (T : CutTree V) : Prop :=
  ∀ v, v ≠ T.topology.root →
    IsSTMinCut G v (T.topology.parent v) (T.topology.D v) ∧
      T.weight v = G.cut (T.topology.D v)

end
end CutQueryComplexity.GHReduction
