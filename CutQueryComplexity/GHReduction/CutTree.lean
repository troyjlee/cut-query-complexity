import CutQueryComplexity.GHReduction.Specification

/-! # Fundamental witnesses imply all-pairs cut equivalence

The topology remains a tree even when some or all edge weights are zero.
The proof uses the existing rooted-tree parity lemma to find a path edge
crossing every competing s-t shore.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical
open WeightedGraph

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Edges on the unique terminal path, indexed by their nonroot child. -/
def pathEdges (T : RootedTree V) (s t : V) : Finset V :=
  Finset.univ.filter (fun v => v ≠ T.root ∧ ¬(T.IsAnc v s ↔ T.IsAnc v t))

@[simp] theorem mem_pathEdges (T : RootedTree V) (s t v : V) :
    v ∈ pathEdges T s t ↔ v ≠ T.root ∧ ¬(T.IsAnc v s ↔ T.IsAnc v t) := by
  simp [pathEdges]

/-- Every separating shore crosses an edge of the terminal path. -/
theorem path_crossing (T : RootedTree V) {s t : V} {S : Finset V}
    (hs : s ∈ S) (ht : t ∉ S) :
    ∃ v, v ∈ T.crossSet S ∧ v ∈ pathEdges T s t := by
  by_contra hnone
  have heq : T.crossAbove S s = T.crossAbove S t := by
    ext v
    simp only [RootedTree.crossAbove, Finset.mem_filter]
    have hi : v ∈ T.crossSet S → (T.IsAnc v s ↔ T.IsAnc v t) := by
      intro hv
      by_contra hiff
      exact hnone ⟨v, hv, (mem_pathEdges T s t v).mpr
        ⟨T.ne_root_of_mem_crossSet hv, hiff⟩⟩
    constructor
    · rintro ⟨hv, hs⟩
      exact ⟨hv, (hi hv).mp hs⟩
    · rintro ⟨hv, ht⟩
      exact ⟨hv, (hi hv).mpr ht⟩
  have hspar := (T.mem_iff_parity S s).mp hs
  rw [heq] at hspar
  exact ht ((T.mem_iff_parity S t).mpr hspar)

theorem pathEdges_nonempty (T : RootedTree V) {s t : V} (hst : s ≠ t) :
    (pathEdges T s t).Nonempty := by
  obtain ⟨v, _, hv⟩ := path_crossing T (s := s) (t := t) (S := {s})
    (by simp) (by simp [Ne.symm hst])
  exact ⟨v, hv⟩

/-- Orient a fundamental cut to contain the requested source. -/
def pathShore (T : RootedTree V) (s v : V) : Finset V :=
  if s ∈ T.D v then T.D v else (T.D v)ᶜ

theorem pathShore_separates (T : RootedTree V) {s t v : V}
    (hv : v ∈ pathEdges T s t) : s ∈ pathShore T s v ∧ t ∉ pathShore T s v := by
  have hsep := ((mem_pathEdges T s t v).mp hv).2
  by_cases hs : s ∈ T.D v
  · have ht : t ∉ T.D v := by
      intro ht
      exact hsep ⟨fun _ => (T.mem_D _ _).mp ht, fun _ => (T.mem_D _ _).mp hs⟩
    simpa [pathShore, hs] using And.intro hs ht
  · have ht : t ∈ T.D v := by
      by_contra ht
      apply hsep
      constructor
      · intro h
        exact (hs ((T.mem_D _ _).mpr h)).elim
      · intro h
        exact (ht ((T.mem_D _ _).mpr h)).elim
    simpa [pathShore, hs] using And.intro hs ht

@[simp] theorem cut_pathShore (G : WeightedGraph V) (T : RootedTree V) (s v : V) :
    G.cut (pathShore T s v) = G.cut (T.D v) := by
  unfold pathShore
  split <;> simp

/-- An endpoint minimum certificate bounds its edge weight by any crossing cut. -/
theorem tree_weight_le_crossing_cut (G : WeightedGraph V) (T : CutTree V)
    (hT : IsGomoryHuTree G T) {S : Finset V} {v : V}
    (hv : v ∈ T.topology.crossSet S) : T.weight v ≤ G.cut S := by
  have hcross : T.topology.Crosses S v := (Finset.mem_filter.mp hv).2
  obtain ⟨hmin, hweight⟩ := hT v hcross.1
  rw [hweight]
  by_cases hs : v ∈ S
  · have hp : T.topology.parent v ∉ S := by
      intro hp
      exact hcross.2 ⟨fun _ => hp, fun _ => hs⟩
    exact hmin.2.2 S hs hp
  · have hp : T.topology.parent v ∈ S := by
      by_contra hp
      exact hcross.2 ⟨fun h => (hs h).elim, fun h => (hp h).elim⟩
    simpa only [cut_compl] using hmin.2.2 Sᶜ (by simpa using hs) (by simpa using hp)

/-- Any least-weight edge of the public path gives an original minimum shore.
The edge may be selected using the tree alone. -/
theorem pathShore_minimum_of_bottleneck (G : WeightedGraph V) (T : CutTree V)
    (hT : IsGomoryHuTree G T) {s t v : V}
    (hv : v ∈ pathEdges T.topology s t)
    (hmin : ∀ e ∈ pathEdges T.topology s t, T.weight v ≤ T.weight e) :
    IsSTMinCut G s t (pathShore T.topology s v) ∧
      G.cut (pathShore T.topology s v) = T.weight v := by
  have hnonroot := ((mem_pathEdges T.topology s t v).mp hv).1
  have hweight : G.cut (pathShore T.topology s v) = T.weight v := by
    rw [cut_pathShore]
    exact (hT v hnonroot).2.symm
  obtain ⟨hs, ht⟩ := pathShore_separates T.topology hv
  refine ⟨⟨hs, ht, fun S hsS htS => ?_⟩, hweight⟩
  obtain ⟨e, hecross, hepath⟩ := path_crossing T.topology hsS htS
  rw [hweight]
  exact (hmin e hepath).trans (tree_weight_le_crossing_cut G T hT hecross)

/-- The fundamental certificate interface entails both bottleneck values and
actual original-graph minimum shores for every distinct pair. -/
theorem cutTree_allPairs (G : WeightedGraph V) (T : CutTree V)
    (hT : IsGomoryHuTree G T) {s t : V} (hst : s ≠ t) :
    ∃ v ∈ pathEdges T.topology s t,
      (∀ e ∈ pathEdges T.topology s t, T.weight v ≤ T.weight e) ∧
      IsSTMinCut G s t (pathShore T.topology s v) ∧
      G.cut (pathShore T.topology s v) = T.weight v := by
  obtain ⟨v, hv, hmin⟩ := Finset.exists_min_image (pathEdges T.topology s t)
    T.weight (pathEdges_nonempty T.topology hst)
  exact ⟨v, hv, hmin, pathShore_minimum_of_bottleneck G T hT hv hmin⟩

/-- Public finite minimization; coincident terminals use the unused root entry.
No hidden graph or correctness witness enters this selector. -/
def minimumPathEdge (T : CutTree V) (s t : V) : V :=
  if h : (pathEdges T.topology s t).Nonempty then
    Classical.choose (Finset.exists_min_image (pathEdges T.topology s t) T.weight h)
  else T.topology.root

theorem minimumPathEdge_spec (T : CutTree V) {s t : V} (hst : s ≠ t) :
    minimumPathEdge T s t ∈ pathEdges T.topology s t ∧
      ∀ e ∈ pathEdges T.topology s t, T.weight (minimumPathEdge T s t) ≤ T.weight e := by
  have h := pathEdges_nonempty T.topology hst
  simpa only [minimumPathEdge, dite_eq_left h] using
    Classical.choose_spec (Finset.exists_min_image (pathEdges T.topology s t) T.weight h)

/-- Decode a shore and its value from a completed public cut tree. -/
def cutTreeAnswer (T : CutTree V) (s t : V) : Finset V × ℝ :=
  let v := minimumPathEdge T s t
  (pathShore T.topology s v, T.weight v)

theorem cutTreeAnswer_correct (G : WeightedGraph V) (T : CutTree V)
    (hT : IsGomoryHuTree G T) {s t : V} (hst : s ≠ t) :
    IsSTMinCut G s t (cutTreeAnswer T s t).1 ∧
      G.cut (cutTreeAnswer T s t).1 = (cutTreeAnswer T s t).2 := by
  obtain ⟨hv, hmin⟩ := minimumPathEdge_spec T hst
  exact pathShore_minimum_of_bottleneck G T hT hv hmin

def cutTreeAnswerProgram (T : CutTree V) (s t : V) :
    DTree (Finset V) ℝ (Finset V × ℝ) 0 := DTree.pure (cutTreeAnswer T s t)

@[simp] theorem cutTreeAnswerProgram_run (T : CutTree V) (s t : V)
    (read : Finset V → ℝ) :
    (cutTreeAnswerProgram T s t).run read = (cutTreeAnswer T s t, 0) := rfl

/-- The same zero-query decoder serves all hidden graphs represented by `T`. -/
theorem cutTreeAnswerProgram_correct (T : CutTree V) {s t : V} (hst : s ≠ t)
    (G : WeightedGraph V) (hT : IsGomoryHuTree G T) :
    IsSTMinCut G s t ((cutTreeAnswerProgram T s t).eval G.cut).1 ∧
      G.cut ((cutTreeAnswerProgram T s t).eval G.cut).1 =
        ((cutTreeAnswerProgram T s t).eval G.cut).2 :=
  cutTreeAnswer_correct G T hT hst

#print axioms path_crossing
#print axioms pathEdges_nonempty
#print axioms pathShore_separates
#print axioms tree_weight_le_crossing_cut
#print axioms pathShore_minimum_of_bottleneck
#print axioms cutTree_allPairs
#print axioms minimumPathEdge_spec
#print axioms cutTreeAnswer_correct
#print axioms cutTreeAnswerProgram_run
#print axioms cutTreeAnswerProgram_correct

end
end CutQueryComplexity.GHReduction
