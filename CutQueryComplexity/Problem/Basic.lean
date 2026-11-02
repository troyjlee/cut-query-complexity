import CutQueryComplexity.Graph.Capacity
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Order.MinMax

/-! # Cut problems as output relations

Singleton shores are proper cuts. A `NontrivialShore` additionally excludes
both kinds of singleton shore, as required in the star-contraction papers.
-/

namespace CutQueryComplexity

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Both shores of a proper cut are nonempty. -/
def ProperShore (S : Finset V) : Prop := S.Nonempty ∧ S ≠ Finset.univ

/-- Both shores have at least two vertices. -/
def NontrivialShore (S : Finset V) : Prop := 2 ≤ S.card ∧ 2 ≤ Sᶜ.card

/-- The finite domain over which global mincut is minimized. -/
def properShores (V : Type*) [Fintype V] [DecidableEq V] : Finset (Finset V) :=
  Finset.univ.filter (fun S => S.Nonempty ∧ S ≠ Finset.univ)

@[simp] theorem mem_properShores (S : Finset V) :
    S ∈ properShores V ↔ ProperShore S := by simp [properShores, ProperShore]

omit [DecidableEq V] in
/-- Every singleton is a valid cut when there are at least two vertices. -/
theorem properShore_singleton (v : V) (hn : 2 ≤ Fintype.card V) :
    ProperShore ({v} : Finset V) := by
  refine ⟨Finset.singleton_nonempty _, ?_⟩
  intro h
  have := congrArg Finset.card h
  simp at this
  omega

/-- The minimum over proper shores; zero by convention if none exist. -/
noncomputable def mincutValue (G : WeightedGraph V) : ℝ :=
  if h : (properShores V).Nonempty then (properShores V).inf' h G.cut else 0

/-- A proper shore attaining the global minimum, including disconnected inputs. -/
def IsMinCut (G : WeightedGraph V) (S : Finset V) : Prop :=
  ProperShore S ∧ ∀ T, ProperShore T → G.cut S ≤ G.cut T

/-- A minimum cut separating the two specified terminals. -/
def IsSTMinCut (G : WeightedGraph V) (s t : V) (S : Finset V) : Prop :=
  s ∈ S ∧ t ∉ S ∧ ∀ T, s ∈ T → t ∉ T → G.cut S ≤ G.cut T

theorem mincutValue_nonneg (G : WeightedGraph V) : 0 ≤ mincutValue G := by
  unfold mincutValue
  split
  · exact Finset.le_inf' _ _ (fun S _ => G.cut_nonneg S)
  · exact le_rfl

theorem mincutValue_le (G : WeightedGraph V) {S : Finset V} (hS : ProperShore S) :
    mincutValue G ≤ G.cut S := by
  have hm := (mem_properShores S).mpr hS
  rw [mincutValue, dite_eq_left ⟨S, hm⟩]
  exact Finset.inf'_le _ hm

/-- The finite minimum is attained whenever a proper shore exists. -/
theorem exists_isMinCut (G : WeightedGraph V) (h : (properShores V).Nonempty) :
    ∃ S, IsMinCut G S ∧ G.cut S = mincutValue G := by
  obtain ⟨S, hS, hmin⟩ := Finset.exists_mem_eq_inf' h G.cut
  refine ⟨S, ⟨(mem_properShores S).mp hS, ?_⟩, ?_⟩
  · intro T hT
    rw [← hmin]
    exact Finset.inf'_le _ ((mem_properShores T).mpr hT)
  · rw [mincutValue, dite_eq_left h, hmin]

theorem exists_isMinCut_of_two_le_card (G : WeightedGraph V)
    (hn : 2 ≤ Fintype.card V) : ∃ S, IsMinCut G S := by
  have hpos : 0 < Fintype.card V := by omega
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp hpos
  obtain ⟨S, hS, _⟩ := exists_isMinCut G
    ⟨{v}, (mem_properShores _).mpr (properShore_singleton v hn)⟩
  exact ⟨S, hS⟩

/-- A zero-weight proper cut certifies mincut zero. -/
theorem mincutValue_eq_zero_of_cut_eq_zero (G : WeightedGraph V) {S : Finset V}
    (hS : ProperShore S) (hzero : G.cut S = 0) : mincutValue G = 0 := by
  have := mincutValue_le G hS
  have := mincutValue_nonneg G
  linarith

namespace WeightedGraph

/-- The positive-edge support as a simple graph, independent of the weights' magnitudes. -/
def support (G : WeightedGraph V) : SimpleGraph V where
  Adj u v := G.w u v ≠ 0
  symm := ⟨fun u v h => by rwa [G.symm]⟩
  loopless := ⟨fun v => by simp [G.diag]⟩

/-- Number of unordered positive edges. -/
noncomputable def edgeCount (G : WeightedGraph V) : ℕ := by
  classical
  exact G.support.edgeFinset.card

end WeightedGraph

/-- A forest of original edges with the same connected components as the input. -/
def IsSpanningForest (G : WeightedGraph V) (F : SimpleGraph V) : Prop :=
  F ≤ G.support ∧ F.IsAcyclic ∧ ∀ u v, G.support.Reachable u v → F.Reachable u v

/-- Simultaneous multiplicative preservation of all cuts, with original-edge support. -/
def IsCutSparsifier (ε : ℝ) (G H : WeightedGraph V) : Prop :=
  H.support ≤ G.support ∧ ∀ S,
    (1 - ε) * G.cut S ≤ H.cut S ∧ H.cut S ≤ (1 + ε) * G.cut S

/-- A cut sparsifier with an explicit support-size bound. -/
def IsSparseCutSparsifier (ε : ℝ) (m : ℕ) (G H : WeightedGraph V) : Prop :=
  IsCutSparsifier ε G H ∧ H.edgeCount ≤ m

theorem isCutSparsifier_self (G : WeightedGraph V) : IsCutSparsifier 0 G G := by
  exact ⟨le_rfl, by simp⟩

/-- Multiplicative sparsification preserves zero cuts exactly. -/
theorem IsCutSparsifier.cut_eq_zero {ε : ℝ} {G H : WeightedGraph V}
    (h : IsCutSparsifier ε G H) {S : Finset V} (hS : G.cut S = 0) : H.cut S = 0 := by
  have := (h.2 S).2
  have := H.cut_nonneg S
  rw [hS, mul_zero] at *
  linarith

end CutQueryComplexity
