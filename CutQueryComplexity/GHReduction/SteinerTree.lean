import CutQueryComplexity.GHReduction.CutTree

/-! # Cut trees on a terminal set with an explicit attachment map

Recursive auxiliary vertices are not output terminals. The public map from
graph vertices to tree terminals records where their components will attach
when recursive trees are joined. Correctness includes original-graph shores,
not just pair values in the terminal metric.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical
open WeightedGraph

variable {V U : Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]

/-- `terminal` embeds the tree labels into the graph. The retraction is public
output data, and fixes every terminal. No optimization or correctness is a field. -/
structure SteinerCutTree (V U : Type) where
  tree : CutTree U
  terminal : U → V
  attach : V → U
  attach_terminal : ∀ u, attach (terminal u) = u

theorem SteinerCutTree.terminal_injective (T : SteinerCutTree V U) :
    Function.Injective T.terminal := by
  intro u v h
  have := congrArg T.attach h
  simpa only [T.attach_terminal] using this

def IsSteinerCutTree (G : WeightedGraph V) (T : SteinerCutTree V U) : Prop :=
  ∀ u, u ≠ T.tree.topology.root →
    IsSTMinCut G (T.terminal u) (T.terminal (T.tree.topology.parent u))
      (pull T.attach (T.tree.topology.D u)) ∧
    T.tree.weight u = G.cut (pull T.attach (T.tree.topology.D u))

def terminalTrace (T : SteinerCutTree V U) (S : Finset V) : Finset U :=
  Finset.univ.filter (fun u => T.terminal u ∈ S)

@[simp] theorem mem_terminalTrace (T : SteinerCutTree V U) (S : Finset V) (u : U) :
    u ∈ terminalTrace T S ↔ T.terminal u ∈ S := by simp [terminalTrace]

def steinerPathShore (T : SteinerCutTree V U) (s e : U) : Finset V :=
  pull T.attach (pathShore T.tree.topology s e)

theorem steinerPathShore_separates (T : SteinerCutTree V U) {s t e : U}
    (he : e ∈ pathEdges T.tree.topology s t) :
    T.terminal s ∈ steinerPathShore T s e ∧ T.terminal t ∉ steinerPathShore T s e := by
  simpa only [steinerPathShore, mem_pull, T.attach_terminal] using
    pathShore_separates T.tree.topology he

theorem cut_steinerPathShore (G : WeightedGraph V) (T : SteinerCutTree V U) (s e : U) :
    G.cut (steinerPathShore T s e) = G.cut (pull T.attach (T.tree.topology.D e)) := by
  unfold steinerPathShore pathShore
  split
  · rfl
  · have hcomp : pull T.attach (T.tree.topology.D e)ᶜ =
        (pull T.attach (T.tree.topology.D e))ᶜ := by ext v; simp
    rw [hcomp, cut_compl]

theorem steiner_weight_le_crossing_cut (G : WeightedGraph V) (T : SteinerCutTree V U)
    (hT : IsSteinerCutTree G T) {S : Finset V} {e : U}
    (he : e ∈ T.tree.topology.crossSet (terminalTrace T S)) : T.tree.weight e ≤ G.cut S := by
  have hc : T.tree.topology.Crosses (terminalTrace T S) e := (Finset.mem_filter.mp he).2
  obtain ⟨hmin, hweight⟩ := hT e hc.1
  rw [hweight]
  by_cases hs : T.terminal e ∈ S
  · have hp : T.terminal (T.tree.topology.parent e) ∉ S := by
      intro hp
      exact hc.2 (by simpa only [mem_terminalTrace] using Iff.intro (fun _ => hp) (fun _ => hs))
    exact hmin.2.2 S hs hp
  · have hp : T.terminal (T.tree.topology.parent e) ∈ S := by
      by_contra hp
      apply hc.2
      simp only [mem_terminalTrace, hs, hp]
    simpa only [cut_compl] using hmin.2.2 Sᶜ (by simpa using hs) (by simpa using hp)

/-- The explicit attachment map lifts the bottleneck edge to a true minimum
shore for every terminal pair, against arbitrary original-graph competitors. -/
theorem steinerTree_allPairs (G : WeightedGraph V) (T : SteinerCutTree V U)
    (hT : IsSteinerCutTree G T) {s t : U} (hst : s ≠ t) :
    ∃ e ∈ pathEdges T.tree.topology s t,
      (∀ d ∈ pathEdges T.tree.topology s t, T.tree.weight e ≤ T.tree.weight d) ∧
      IsSTMinCut G (T.terminal s) (T.terminal t) (steinerPathShore T s e) ∧
      G.cut (steinerPathShore T s e) = T.tree.weight e := by
  obtain ⟨e, he, hleast⟩ := Finset.exists_min_image (pathEdges T.tree.topology s t)
    T.tree.weight (pathEdges_nonempty T.tree.topology hst)
  have he0 := ((mem_pathEdges T.tree.topology s t e).mp he).1
  have hweight : G.cut (steinerPathShore T s e) = T.tree.weight e := by
    rw [cut_steinerPathShore]
    exact (hT e he0).2.symm
  obtain ⟨hs, ht⟩ := steinerPathShore_separates T he
  refine ⟨e, he, hleast, ⟨hs, ht, fun S hsS htS => ?_⟩, hweight⟩
  obtain ⟨d, hcross, hpath⟩ := path_crossing T.tree.topology
    (S := terminalTrace T S) (by simpa using hsS) (by simpa using htS)
  rw [hweight]
  exact (hleast d hpath).trans (steiner_weight_le_crossing_cut G T hT hcross)

/-- An ordinary cut tree is the case in which every graph vertex is a terminal. -/
def CutTree.asSteiner (T : CutTree V) : SteinerCutTree V V where
  tree := T
  terminal := id
  attach := id
  attach_terminal _ := rfl

@[simp] theorem pull_id_shore (S : Finset V) : pull (id : V → V) S = S := by
  ext v
  simp

theorem cutTree_asSteiner_correct (G : WeightedGraph V) (T : CutTree V) :
    IsSteinerCutTree G T.asSteiner ↔ IsGomoryHuTree G T := by
  simp only [IsSteinerCutTree, CutTree.asSteiner, IsGomoryHuTree, id_eq, pull_id_shore]

end
end CutQueryComplexity.GHReduction
