import CutQueryComplexity.Certificate.Flow
import CutQueryComplexity.AllPairs.Representation

/-!
# Three queries per vertex identify a known unit graph

The competitors in this certificate are explicitly restricted to 0/1 graphs.
For every vertex query its singleton, its original neighbor set, and their union.
The three-cut identity fixes the entire neighbor mass; the unit upper bound
forces every original edge, and singleton degrees rule out all added edges.
Consequently the same certificate fixes every terminal minimum shore and value.
-/

set_option autoImplicit false

namespace CutQueryComplexity.Certificate.UnitAllPairs

open Finset WeightedGraph AllPairsAudit
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The neighbor set of the known graph; this is certificate data. -/
def neighbors (G : WeightedGraph V) (v : V) : Finset V :=
  univ.filter fun u => G.w v u = 1

@[simp] theorem mem_neighbors (G : WeightedGraph V) (v u : V) :
    u ∈ neighbors G v ↔ G.w v u = 1 := by simp [neighbors]

@[simp] theorem self_not_neighbors (G : WeightedGraph V) (v : V) :
    v ∉ neighbors G v := by simp [G.diag]

/-- At most three shores for each labeled vertex. -/
def queries (G : WeightedGraph V) : Finset (Finset V) :=
  (univ.image fun v : V => ({v} : Finset V)) ∪
  (univ.image fun v : V => neighbors G v) ∪
  (univ.image fun v : V => ({v} : Finset V) ∪ neighbors G v)

theorem queries_card (G : WeightedGraph V) :
    (queries G).card ≤ 3 * Fintype.card V := by
  have h1 := card_union_le
    (univ.image fun v : V => ({v} : Finset V))
    (univ.image fun v : V => neighbors G v)
  have h2 := card_union_le
    ((univ.image fun v : V => ({v} : Finset V)) ∪
      (univ.image fun v : V => neighbors G v))
    (univ.image fun v : V => ({v} : Finset V) ∪ neighbors G v)
  have ha := card_image_le (s := (univ : Finset V)) (f := fun v : V => ({v} : Finset V))
  have hb := card_image_le (s := (univ : Finset V)) (f := fun v : V => neighbors G v)
  have hc := card_image_le (s := (univ : Finset V))
    (f := fun v : V => ({v} : Finset V) ∪ neighbors G v)
  simp only [card_univ] at ha hb hc
  change _ ≤ _
  unfold queries
  omega

theorem singleton_mem (G : WeightedGraph V) (v : V) : {v} ∈ queries G := by
  simp [queries]

theorem neighbors_mem (G : WeightedGraph V) (v : V) : neighbors G v ∈ queries G := by
  simp only [queries, mem_union]
  exact Or.inl (Or.inr (mem_image_of_mem _ (mem_univ v)))

theorem union_mem (G : WeightedGraph V) (v : V) :
    ({v} : Finset V) ∪ neighbors G v ∈ queries G := by
  exact mem_union_right _ (mem_image_of_mem _ (mem_univ v))

theorem consistent_degree {G H : WeightedGraph V} (h : Consistent G H (queries G))
    (v : V) : H.degree v = G.degree v := by
  simpa using h {v} (singleton_mem G v)

theorem consistent_neighbor_mass {G H : WeightedGraph V}
    (h : Consistent G H (queries G)) (v : V) :
    (∑ u ∈ neighbors G v, H.w v u) = ∑ u ∈ neighbors G v, G.w v u := by
  have he := h.cross_eq (disjoint_singleton_left.mpr (self_not_neighbors G v))
    (singleton_mem G v) (neighbors_mem G v) (union_mem G v)
  simpa [WeightedGraph.cross] using he

/-- The unit bound forces every original neighbor individually. -/
theorem consistent_original_edge {G H : WeightedGraph V} (hH : Unweighted H)
    (h : Consistent G H (queries G)) {v u : V} (hu : G.w v u = 1) : H.w v u = 1 := by
  have hle (x : V) : H.w v x ≤ 1 := by rcases hH v x with hx | hx <;> simp [hx]
  have hs : (∑ x ∈ neighbors G v, (1 - H.w v x)) = 0 := by
    rw [sum_sub_distrib, consistent_neighbor_mass h v]
    have he : (∑ x ∈ neighbors G v, G.w v x) = ∑ _x ∈ neighbors G v, (1 : ℝ) :=
      sum_congr rfl fun x hx => (mem_neighbors G v x).mp hx
    rw [he, sub_self]
  have hz := (sum_eq_zero_iff_of_nonneg (fun x (_ : x ∈ neighbors G v) =>
    sub_nonneg.mpr (hle x))).mp hs u ((mem_neighbors G v u).mpr hu)
  linarith

/-- Full labeled graph equality, with no unrestricted weighted-competitor claim. -/
theorem eq_of_consistent {G H : WeightedGraph V} (hG : Unweighted G) (hH : Unweighted H)
    (h : Consistent G H (queries G)) : H = G := by
  have hle (v u : V) : G.w v u ≤ H.w v u := by
    rcases hG v u with hzero | hone
    · rw [hzero]; exact H.nonneg v u
    · rw [hone, consistent_original_edge hH h hone]
  ext v u
  have hs : (∑ x, (H.w v x - G.w v x)) = 0 := by
    rw [sum_sub_distrib]
    change H.degree v - G.degree v = 0
    rw [consistent_degree h v, sub_self]
  have hz := (sum_eq_zero_iff_of_nonneg (fun x (_ : x ∈ (univ : Finset V)) =>
    sub_nonneg.mpr (hle v x))).mp hs u (mem_univ u)
  exact sub_eq_zero.mp hz

/-- Offline answers for the known graph, shared by every consistent unit graph. -/
def answers (G : WeightedGraph V) : AllPairs.Answers V :=
  fun s t => ⟨AllPairs.offlineST G s t, G.cut (AllPairs.offlineST G s t)⟩

theorem answers_correct (G : WeightedGraph V) : AllPairs.allPairsGood G (answers G) :=
  fun _ _ hst => ⟨AllPairs.offlineST_correct G hst, rfl⟩

/-- One linear-size certificate simultaneously fixes all original optimum shores
and exact original optimum values against 0/1 competitors. -/
theorem exists_unit_allPairs_certificate (G : WeightedGraph V) (hG : Unweighted G) :
    ∃ Q : Finset (Finset V), Q.card ≤ 3 * Fintype.card V ∧
      ∃ out : AllPairs.Answers V, AllPairs.allPairsGood G out ∧
        ∀ H : WeightedGraph V, Unweighted H → Consistent G H Q →
          H = G ∧ AllPairs.allPairsGood H out := by
  refine ⟨queries G, queries_card G, answers G, answers_correct G, ?_⟩
  intro H hH h
  have he := eq_of_consistent hG hH h
  exact ⟨he, he.symm ▸ answers_correct G⟩

/-- A deterministic transcript provides a separate certificate at its inherited
program budget. This general wrapper does not weaken the direct `3n` theorem. -/
theorem transcript_certificate {q : ℕ} (T : DTree (Finset V) ℝ (AllPairs.Answers V) q)
    (hT : ∀ H : WeightedGraph V, Unweighted H → AllPairs.allPairsGood H (T.eval H.cut))
    (G : WeightedGraph V) (hG : Unweighted G) :
    ∃ Q : Finset (Finset V), Q.card ≤ q ∧
      AllPairs.allPairsGood G (T.eval G.cut) ∧
      ∀ H : WeightedGraph V, Unweighted H → Consistent G H Q →
        AllPairs.allPairsGood H (T.eval G.cut) := by
  let Q := ((DTree.transcript G.cut T).map Prod.fst).toFinset
  refine ⟨Q, ?_, hT G hG, ?_⟩
  · exact (List.toFinset_card_le _).trans (by
      rw [List.length_map, DTree.transcript_length]
      exact T.cost_le G.cut)
  · intro H hH h
    have he := DTree.run_eq_of_agree T G.cut H.cut (by
      intro S v hv
      exact (h S (List.mem_toFinset.mpr (List.mem_map.mpr ⟨(S,v), hv, rfl⟩))).symm)
    have heval : T.eval G.cut = T.eval H.cut := congrArg Prod.fst he
    rw [heval]
    exact hT H hH

end
end CutQueryComplexity.Certificate.UnitAllPairs
