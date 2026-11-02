import CutQueryComplexity.GHReduction.SteinerTree

/-! # Removing the final terminal-label representation

Once the explicit terminal embedding covers every original vertex, its inverse
is the attachment map. Public relabeling produces an ordinary cut tree whose
fundamental shores are the original witnessed minimum cuts.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical
open WeightedGraph

variable {V U : Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]

def relabelRootedTree (T : RootedTree U) (e : U ≃ V) : RootedTree V where
  root := e T.root
  parent v := e (T.parent (e.symm v))
  depth v := T.depth (e.symm v)
  parent_root := by simp only [Equiv.symm_apply_apply, T.parent_root]
  depth_root := by simp only [Equiv.symm_apply_apply, T.depth_root]
  depth_parent v hv := by
    have hv' : e.symm v ≠ T.root := by
      intro he
      apply hv
      rw [← e.apply_symm_apply v, he]
    simpa only [Equiv.symm_apply_apply] using T.depth_parent (e.symm v) hv'

theorem relabelRootedTree_iterate (T : RootedTree U) (e : U ≃ V) (u : U) (k : ℕ) :
    (relabelRootedTree T e).parent^[k] (e u) = e (T.parent^[k] u) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    simp only [relabelRootedTree, Equiv.symm_apply_apply]

theorem relabelRootedTree_ancestor (T : RootedTree U) (e : U ≃ V) (u v : U) :
    (relabelRootedTree T e).IsAnc (e u) (e v) ↔ T.IsAnc u v := by
  constructor
  · rintro ⟨k, hk⟩
    rw [relabelRootedTree_iterate] at hk
    exact ⟨k, e.injective hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [relabelRootedTree_iterate, hk]⟩

theorem relabelRootedTree_subtree (T : RootedTree U) (e : U ≃ V) (u : U) :
    (relabelRootedTree T e).D (e u) = pull e.symm (T.D u) := by
  ext v
  simp only [RootedTree.mem_D, mem_pull]
  conv_lhs => rw [← e.apply_symm_apply v]
  exact relabelRootedTree_ancestor T e u (e.symm v)

theorem SteinerCutTree.terminal_attach (T : SteinerCutTree V U)
    (hcover : Function.Surjective T.terminal) (v : V) : T.terminal (T.attach v) = v := by
  obtain ⟨u, rfl⟩ := hcover v
  rw [T.attach_terminal]

def SteinerCutTree.terminalEquiv (T : SteinerCutTree V U)
    (hcover : Function.Surjective T.terminal) : U ≃ V :=
  Equiv.ofBijective T.terminal ⟨T.terminal_injective, hcover⟩

@[simp] theorem SteinerCutTree.terminalEquiv_apply (T : SteinerCutTree V U)
    (hcover : Function.Surjective T.terminal) (u : U) :
    T.terminalEquiv hcover u = T.terminal u := rfl

theorem SteinerCutTree.terminalEquiv_symm (T : SteinerCutTree V U)
    (hcover : Function.Surjective T.terminal) : (T.terminalEquiv hcover).symm = T.attach := by
  funext v
  apply T.terminal_injective
  exact (T.terminalEquiv hcover).apply_symm_apply v |>.trans (T.terminal_attach hcover v).symm

def completeSteinerTree (T : SteinerCutTree V U) (hcover : Function.Surjective T.terminal) :
    CutTree V where
  topology := relabelRootedTree T.tree.topology (T.terminalEquiv hcover)
  weight v := T.tree.weight (T.attach v)
  nonneg v := T.tree.nonneg (T.attach v)

theorem completeSteinerTree_subtree (T : SteinerCutTree V U)
    (hcover : Function.Surjective T.terminal) (u : U) :
    (completeSteinerTree T hcover).topology.D (T.terminal u) =
      pull T.attach (T.tree.topology.D u) := by
  have h := relabelRootedTree_subtree T.tree.topology (T.terminalEquiv hcover) u
  simpa only [completeSteinerTree, T.terminalEquiv_apply, T.terminalEquiv_symm] using h

theorem completeSteinerTree_correct (G : WeightedGraph V) (T : SteinerCutTree V U)
    (hcover : Function.Surjective T.terminal) (hT : IsSteinerCutTree G T) :
    IsGomoryHuTree G (completeSteinerTree T hcover) := by
  intro v hv
  obtain ⟨u, rfl⟩ := hcover v
  have hu : u ≠ T.tree.topology.root := by
    intro he
    apply hv
    rw [he]
    rfl
  have hparent : (completeSteinerTree T hcover).topology.parent (T.terminal u) =
      T.terminal (T.tree.topology.parent u) := by
    change T.terminalEquiv hcover
      (T.tree.topology.parent ((T.terminalEquiv hcover).symm (T.terminal u))) = _
    rw [T.terminalEquiv_symm, T.attach_terminal]
    rfl
  obtain ⟨hmin, hweight⟩ := hT u hu
  refine ⟨?_, ?_⟩
  · rwa [completeSteinerTree_subtree, hparent]
  · change T.tree.weight (T.attach (T.terminal u)) = _
    rw [T.attach_terminal, completeSteinerTree_subtree]
    exact hweight

theorem completeSteinerTree_allPairs (G : WeightedGraph V) (T : SteinerCutTree V U)
    (hcover : Function.Surjective T.terminal) (hT : IsSteinerCutTree G T)
    {s t : V} (hst : s ≠ t) :
    ∃ e ∈ pathEdges (completeSteinerTree T hcover).topology s t,
      (∀ d ∈ pathEdges (completeSteinerTree T hcover).topology s t,
        (completeSteinerTree T hcover).weight e ≤ (completeSteinerTree T hcover).weight d) ∧
      IsSTMinCut G s t (pathShore (completeSteinerTree T hcover).topology s e) ∧
      G.cut (pathShore (completeSteinerTree T hcover).topology s e) =
        (completeSteinerTree T hcover).weight e :=
  cutTree_allPairs G _ (completeSteinerTree_correct G T hcover hT) hst

end
end CutQueryComplexity.GHReduction

/-! ## Public zero-query decoding of the supplied completed tree

The tree and its terminal-surjectivity proof are public data. The hidden graph
and the existing fundamental-cut correctness premise occur only in theorems.
This decoder does not construct a Steiner tree or claim randomized success.
-/
namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical

variable {V U : Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]

def completeSteinerTreeAnswer (T : SteinerCutTree V U)
    (hcover : Function.Surjective T.terminal) (s t : V) : Finset V × ℝ :=
  cutTreeAnswer (completeSteinerTree T hcover) s t

def completeSteinerTreeAnswerProgram (T : SteinerCutTree V U)
    (hcover : Function.Surjective T.terminal) (s t : V) :
    DTree (Finset V) ℝ (Finset V × ℝ) 0 :=
  cutTreeAnswerProgram (completeSteinerTree T hcover) s t

/-- The original shore and supplied bottleneck value, with exactly zero calls,
are returned for every real-valued answer table. -/
@[simp] theorem completeSteinerTreeAnswerProgram_run (T : SteinerCutTree V U)
    (hcover : Function.Surjective T.terminal) (s t : V) (read : Finset V → ℝ) :
    (completeSteinerTreeAnswerProgram T hcover s t).run read =
      (completeSteinerTreeAnswer T hcover s t, 0) := rfl

@[simp] theorem completeSteinerTreeAnswerProgram_eval (T : SteinerCutTree V U)
    (hcover : Function.Surjective T.terminal) (s t : V) (read : Finset V → ℝ) :
    (completeSteinerTreeAnswerProgram T hcover s t).eval read =
      completeSteinerTreeAnswer T hcover s t := rfl

theorem completeSteinerTreeAnswer_correct (T : SteinerCutTree V U)
    (hcover : Function.Surjective T.terminal) (G : WeightedGraph V)
    (hT : IsSteinerCutTree G T) {s t : V} (hst : s ≠ t) :
    IsSTMinCut G s t (completeSteinerTreeAnswer T hcover s t).1 ∧
      G.cut (completeSteinerTreeAnswer T hcover s t).1 =
        (completeSteinerTreeAnswer T hcover s t).2 :=
  cutTreeAnswer_correct G (completeSteinerTree T hcover)
    (completeSteinerTree_correct G T hcover hT) hst

theorem completeSteinerTreeAnswerProgram_correct (T : SteinerCutTree V U)
    (hcover : Function.Surjective T.terminal) (G : WeightedGraph V)
    (hT : IsSteinerCutTree G T) {s t : V} (hst : s ≠ t) :
    IsSTMinCut G s t ((completeSteinerTreeAnswerProgram T hcover s t).eval G.cut).1 ∧
      G.cut ((completeSteinerTreeAnswerProgram T hcover s t).eval G.cut).1 =
        ((completeSteinerTreeAnswerProgram T hcover s t).eval G.cut).2 :=
  completeSteinerTreeAnswer_correct T hcover G hT hst

/-- One public decoder family serves every hidden graph certified by the
supplied tree. No graph, correctness proof or query-budget premise is used
in choosing the family; the original correctness premise remains explicit. -/
theorem completeSteinerTree_public_decoder (T : SteinerCutTree V U)
    (hcover : Function.Surjective T.terminal) :
    ∃ P : V → V → DTree (Finset V) ℝ (Finset V × ℝ) 0,
      (∀ (s t : V) (read : Finset V → ℝ),
        (P s t).run read = (completeSteinerTreeAnswer T hcover s t, 0)) ∧
      (∀ (G : WeightedGraph V), IsSteinerCutTree G T → ∀ (s t : V), s ≠ t →
        IsSTMinCut G s t ((P s t).eval G.cut).1 ∧
          G.cut ((P s t).eval G.cut).1 = ((P s t).eval G.cut).2) := by
  refine ⟨completeSteinerTreeAnswerProgram T hcover, ?_, ?_⟩
  · intro s t read
    exact completeSteinerTreeAnswerProgram_run T hcover s t read
  · intro G hT s t hst
    exact completeSteinerTreeAnswerProgram_correct T hcover G hT hst

#print axioms relabelRootedTree
#print axioms relabelRootedTree_iterate
#print axioms relabelRootedTree_ancestor
#print axioms relabelRootedTree_subtree
#print axioms SteinerCutTree.terminal_attach
#print axioms SteinerCutTree.terminalEquiv
#print axioms SteinerCutTree.terminalEquiv_apply
#print axioms SteinerCutTree.terminalEquiv_symm
#print axioms completeSteinerTree
#print axioms completeSteinerTree_subtree
#print axioms completeSteinerTree_correct
#print axioms completeSteinerTree_allPairs
#print axioms completeSteinerTreeAnswerProgram_run
#print axioms completeSteinerTreeAnswerProgram_eval
#print axioms completeSteinerTreeAnswer_correct
#print axioms completeSteinerTreeAnswerProgram_correct
#print axioms completeSteinerTree_public_decoder

end
end CutQueryComplexity.GHReduction
