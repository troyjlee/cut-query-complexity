import CutQueryComplexity.SupportForest.Round

/-! # The forest program and its correctness

The output is the final representative map and the learned edge list. `Correct G out` says
that the fibers of the map are exactly the components of the positive support, that every
listed edge is a positive edge with its exact weight, and that the listed edges form a maximal
spanning forest of the support. `forest_correct` derives it from the invariant once every
representative is finished, `program` runs the loop from the identity map with fuel `2n`, and
`program_spec` proves correctness with at most `3n + 4n ⌈log₂ n⌉` cut queries on every graph.
-/

namespace CutQueryComplexity
namespace SupportForest

open WeightedGraph Search Search.Comp Finset DetMinCut

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## Output and correctness -/

/-- A representative map and a list of weighted edges. -/
structure Output (V : Type) where
  r : V → V
  edges : List (V × V × ℝ)

/-- The output describes a maximal spanning forest of the positive support of `G`. -/
structure Correct (G : WeightedGraph V) (out : Output V) : Prop where
  fiber_iff : ∀ u v, out.r u = out.r v ↔ G.support.Reachable u v
  edges_pos : ∀ e ∈ out.edges, 0 < G.w e.1 e.2.1 ∧ e.2.2 = G.w e.1 e.2.1
  forest : (edgeGraph out.edges).IsAcyclic
  spanning : ∀ u v, G.support.Reachable u v ↔ (edgeGraph out.edges).Reachable u v

omit [Fintype V] [DecidableEq V] in
/-- The listed edges form a spanning forest in the sense of `IsSpanningForest`. -/
theorem Correct.isSpanningForest {G : WeightedGraph V} {out : Output V} (h : Correct G out) :
    IsSpanningForest G (edgeGraph out.edges) :=
  ⟨edgeGraph_le_support G _ fun e he => (h.edges_pos e he).1, h.forest,
    fun u v huv => (h.spanning u v).mp huv⟩

/-- The output of a state. -/
def St.output (st : St V) : Output V := ⟨st.r, st.edges⟩

/-- Once every representative is finished, the invariant gives a correct output. -/
theorem forest_correct (G : WeightedGraph V) {st : St V} (hI : Inv G st)
    (hdone : ∀ x, st.r x ∈ st.done) : Correct G st.output := by
  have hfib : ∀ u v, st.r u = st.r v ↔ G.support.Reachable u v := by
    intro u v
    refine ⟨hI.fiber_le u v, fun h => ?_⟩
    have hz := hI.done_zero _ (hdone u)
    have hmem : u ∈ classOf st.r (st.r u) := by simp
    have := reachable_mem_of_cut_zero G _ hz hmem h
    rw [mem_classOf] at this
    exact this.symm
  exact ⟨hfib, hI.edges_ok, hI.acyclic, fun u v => (hfib u v).symm.trans (hI.spanning u v)⟩

/-! ## The program -/

/-- The initial state: every vertex is its own unfinished representative, no edges. -/
def initSt : St V := ⟨id, ∅, []⟩

theorem inv_initSt (G : WeightedGraph V) : Inv G (initSt (V := V)) where
  idem _ := rfl
  fiber_le _ _ h := by simp only [initSt, id] at h; rw [h]
  done_zero _ h := by simp [initSt] at h
  done_rep _ h := by simp [initSt] at h
  edges_ok _ h := by simp [initSt] at h
  acyclic := by simp [initSt, SimpleGraph.isAcyclic_bot]
  spanning u v := by simp [initSt, SimpleGraph.reachable_bot]

theorem N_initSt : N (initSt (V := V)) = Fintype.card V := by
  simp [N, initSt, image_id]

theorem Φ_initSt : Φ (initSt (V := V)) = 2 * Fintype.card V := by
  simp [Φ, N, initSt, image_id]; ring

variable [LinearOrder V]

/-- The forest program: run the loop with fuel `2n` from the initial state. -/
noncomputable def program : Comp (Finset V) ℝ (Output V) :=
  (loop (2 * Fintype.card V) initSt).map St.output

/-- On every graph the forest program returns a correct output with at most
`3n + 4n ⌈log₂ n⌉` cut queries. -/
theorem program_spec (G : WeightedGraph V) :
    Correct G ((program (V := V)).eval G.cut) ∧
    (program (V := V)).cost G.cut ≤
      Fintype.card V + 2 * Fintype.card V + 4 * Fintype.card V * Nat.clog 2 (Fintype.card V) := by
  obtain ⟨hI, hdone, hcost⟩ :=
    loop_spec G (2 * Fintype.card V) initSt (inv_initSt G) (le_of_eq Φ_initSt)
  simp only [program, eval_map, cost_map]
  refine ⟨forest_correct G hI hdone, ?_⟩
  rw [Φ_initSt, N_initSt] at hcost
  simp only [K] at hcost
  have : 2 * Fintype.card V + (4 * Nat.clog 2 (Fintype.card V) + 1) * Fintype.card V =
      Fintype.card V + 2 * Fintype.card V + 4 * Fintype.card V * Nat.clog 2 (Fintype.card V) := by
    ring
  omega

end SupportForest
end CutQueryComplexity
