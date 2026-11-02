import CutQueryComplexity.Graph.Weighted
import CutQueryComplexity.Model.Composition
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Powerset

/-! # Explicit edge recovery and exact graph reconstruction -/

namespace CutQueryComplexity

noncomputable section

namespace DTree

variable {I A J : Type}

variable [DecidableEq J]

/-- Query a public list of coordinates, keeping their answers in a table. -/
def queryList (schedule : J → I) (fallback : J → A) :
    (js : List J) → DTree I A (J → A) js.length
  | [] => pure fallback
  | j :: js => query (schedule j) fun a =>
      (queryList schedule fallback js).map (fun table => Function.update table j a)

/-- Exact output and cost of the public-list query program. -/
theorem queryList_run (schedule : J → I) (fallback : J → A) (js : List J) (read : I → A) :
    run read (queryList schedule fallback js) =
      ((fun j => if j ∈ js then read (schedule j) else fallback j), js.length) := by
  induction js with
  | nil => simp [queryList, run, pure]
  | cons j js ih =>
      simp only [queryList, run_query, run_map, ih, List.length_cons]
      congr 1
      funext k
      by_cases h : k = j
      · subst k; simp
      · simp [h]

variable [Fintype J]

/-- Read a finite public family of oracle coordinates once each. -/
noncomputable def queryAll (schedule : J → I) (fallback : J → A) :
    DTree I A (J → A) (Fintype.card J) :=
  (queryList schedule fallback Finset.univ.toList).cast (by simp)

@[simp] theorem queryAll_run (schedule : J → I) (fallback : J → A) (read : I → A) :
    run read (queryAll schedule fallback) = (fun j => read (schedule j), Fintype.card J) := by
  simp [queryAll, queryList_run]

end DTree

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Three whole cut queries recover a specified off-diagonal weight. -/
def edgeRecovery (u v : V) : DTree (Finset V) ℝ ℝ 3 :=
  DTree.query {u} fun du =>
    DTree.query {v} fun dv =>
      DTree.query {u, v} fun cuv => DTree.pure ((du + dv - cuv) / 2)

/-- Correctness and exact query cost are linked to the same concrete program. -/
theorem edgeRecovery_run (G : WeightedGraph V) {u v : V} (huv : u ≠ v) :
    DTree.run G.cut (edgeRecovery u v) = (G.w u v, 3) := by
  simp only [edgeRecovery, DTree.run_query, DTree.run_pure]
  rw [← G.edge_eq_three_cuts huv]

/-- Exact recovery of a specified edge, uniformly over all weighted inputs. -/
theorem edgeRecovery_solves {u v : V} (huv : u ≠ v) :
    (edgeRecovery u v).Solves WeightedGraph.cut (fun G w => w = G.w u v) := by
  intro G
  simp [DTree.eval, edgeRecovery_run G huv]

/-- Public reconstruction coordinates: singleton shores and unordered pairs. -/
abbrev ReconstructionIndex (V : Type) [Fintype V] [DecidableEq V] :=
  V ⊕ ↥((Finset.univ : Finset V).powersetCard 2)

theorem card_reconstructionIndex :
    Fintype.card (ReconstructionIndex V) = Fintype.card V + (Fintype.card V).choose 2 := by
  simp [ReconstructionIndex]

/-- The shore at a reconstruction coordinate is known before seeing the graph. -/
def reconstructionShore : ReconstructionIndex V → Finset V
  | Sum.inl v => {v}
  | Sum.inr S => S.val

/-- Coordinate of the unordered pair of distinct vertices. -/
def pairIndex {u v : V} (huv : u ≠ v) : ReconstructionIndex V :=
  Sum.inr ⟨{u, v}, by simp [huv]⟩

theorem pairIndex_symm {u v : V} (huv : u ≠ v) :
    pairIndex huv = pairIndex (Ne.symm huv) := by
  simp [pairIndex, Finset.pair_comm]

/-- Total decoder, including transcripts inconsistent with any graph. -/
def reconstructionWeight (a : ReconstructionIndex V → ℝ) (u v : V) : ℝ :=
  if h : u = v then 0 else max 0 ((a (Sum.inl u) + a (Sum.inl v) - a (pairIndex h)) / 2)

/-- Decode to a valid graph on every branch; clipping never changes a promised input. -/
def reconstructionDecode (a : ReconstructionIndex V → ℝ) : WeightedGraph V where
  w := reconstructionWeight a
  symm u v := by
    by_cases h : u = v
    · subst v; rfl
    · simp only [reconstructionWeight, dite_eq_right h, dite_eq_right (Ne.symm h)]
      rw [← pairIndex_symm h, add_comm (a (Sum.inl v)) (a (Sum.inl u))]
  nonneg u v := by
    unfold reconstructionWeight
    split
    · exact le_rfl
    · exact le_max_left _ _
  diag v := by simp [reconstructionWeight]

theorem reconstructionDecode_correct (G : WeightedGraph V) :
    reconstructionDecode (fun j => G.cut (reconstructionShore j)) = G := by
  ext u v
  dsimp only [reconstructionDecode]
  by_cases h : u = v
  · subst v; simp [reconstructionWeight, G.diag]
  · simp only [reconstructionWeight, dite_eq_right h, reconstructionShore, pairIndex]
    rw [← G.edge_eq_three_cuts h, max_eq_right (G.nonneg u v)]

/-- Exact reconstruction, reusing all singleton answers, with a public query schedule. -/
noncomputable def reconstruct :
    DTree (Finset V) ℝ (WeightedGraph V) (Fintype.card V + (Fintype.card V).choose 2) :=
  ((DTree.queryAll reconstructionShore (fun _ => 0)).map reconstructionDecode).cast
    card_reconstructionIndex

/-- A single algorithm reconstructs every weighted graph in `n + binom(n,2)` queries. -/
theorem reconstruct_run (G : WeightedGraph V) :
    DTree.run G.cut reconstruct = (G, Fintype.card V + (Fintype.card V).choose 2) := by
  simp [reconstruct, reconstructionDecode_correct]

theorem reconstruct_solves :
    (reconstruct (V := V)).Solves WeightedGraph.cut (fun G H => H = G) := by
  intro G
  simp [DTree.eval, reconstruct_run]

end
end CutQueryComplexity
