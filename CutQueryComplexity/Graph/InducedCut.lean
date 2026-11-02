import CutQueryComplexity.Graph.Operations
import Mathlib.Data.Finset.Powerset

/-! # Cuts and minimum cuts inside a vertex set

Unlike `mincutValue (G.induce U)`, these definitions do not treat the vertices
outside `U` as isolated vertices eligible for a minimum cut. Empty and singleton
sets have induced minimum cut zero by convention.
-/

namespace CutQueryComplexity
namespace WeightedGraph

noncomputable section
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A nonempty proper shore of the vertex set `U`. -/
def LocalShore (U S : Finset V) : Prop :=
  S ⊆ U ∧ S.Nonempty ∧ (U \ S).Nonempty

def localShores (U : Finset V) : Finset (Finset V) :=
  U.powerset.filter (fun S => S.Nonempty ∧ (U \ S).Nonempty)

@[simp] theorem mem_localShores (U S : Finset V) :
    S ∈ localShores U ↔ LocalShore U S := by simp [localShores, LocalShore]

theorem LocalShore.two_le_card {U S : Finset V} (h : LocalShore U S) : 2 ≤ U.card := by
  have ha := h.2.1.card_pos
  have hb := h.2.2.card_pos
  have := Finset.card_sdiff_add_card_eq_card h.1
  omega

theorem LocalShore.ssubset {U S : Finset V} (h : LocalShore U S) : S ⊂ U := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨h.1, ?_⟩
  intro he
  simpa [he] using h.2.2

theorem LocalShore.compl {U S : Finset V} (h : LocalShore U S) :
    LocalShore U (U \ S) := by
  refine ⟨Finset.sdiff_subset, h.2.2, ?_⟩
  simpa [Finset.sdiff_sdiff_self_left, Finset.inter_eq_right.mpr h.1] using h.2.1

theorem localShores_nonempty_iff (U : Finset V) :
    (localShores U).Nonempty ↔ 2 ≤ U.card := by
  constructor
  · rintro ⟨S, hS⟩
    exact ((mem_localShores _ _).mp hS).two_le_card
  · intro hn
    obtain ⟨u, hu⟩ := Finset.card_pos.mp (by omega : 0 < U.card)
    refine ⟨{u}, (mem_localShores _ _).mpr ⟨by simpa, by simp, ?_⟩⟩
    apply Finset.card_pos.mp
    have := Finset.card_sdiff_add_card_eq_card (Finset.singleton_subset_iff.mpr hu)
    simp only [Finset.card_singleton] at this
    omega

/-- The cut of the induced graph on `U`; the query shore may extend outside `U`. -/
def localCut (G : WeightedGraph V) (U S : Finset V) : ℝ :=
  G.cross (S ∩ U) (U \ S)

theorem localCut_eq_cut_induce (G : WeightedGraph V) (U S : Finset V) :
    G.localCut U S = (G.induce U).cut S := (G.cut_induce U S).symm

theorem localCut_of_subset (G : WeightedGraph V) {U S : Finset V} (h : S ⊆ U) :
    G.localCut U S = G.cross S (U \ S) := by
  rw [localCut, Finset.inter_eq_left.mpr h]

theorem localCut_nonneg (G : WeightedGraph V) (U S : Finset V) :
    0 ≤ G.localCut U S := G.cross_nonneg _ _

theorem cross_mono (G : WeightedGraph V) {S T A B : Finset V}
    (hS : S ⊆ A) (hT : T ⊆ B) : G.cross S T ≤ G.cross A B := by
  calc
    _ ≤ G.cross A T := Finset.sum_le_sum_of_subset_of_nonneg hS
      (fun u _ _ => Finset.sum_nonneg (fun v _ => G.nonneg u v))
    _ ≤ _ := Finset.sum_le_sum fun u _ =>
      Finset.sum_le_sum_of_subset_of_nonneg hT (fun v _ _ => G.nonneg u v)

theorem localCut_mono (G : WeightedGraph V) {U W : Finset V}
    (h : U ⊆ W) (S : Finset V) : G.localCut U S ≤ G.localCut W S := by
  apply G.cross_mono
  · exact Finset.inter_subset_inter_left h
  · exact Finset.sdiff_subset_sdiff h le_rfl

@[simp] theorem localCut_univ (G : WeightedGraph V) (S : Finset V) :
    G.localCut Finset.univ S = G.cut S := by simp [localCut, ← Finset.compl_eq_univ_sdiff]

@[simp] theorem localCut_inter (G : WeightedGraph V) (U S : Finset V) :
    G.localCut U (S ∩ U) = G.localCut U S := by
  unfold localCut
  congr 1
  · ext v; simp
  · ext v; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto

/-- Finite minimum of the proper induced cuts, with zero for at most one vertex. -/
def inducedMincut (G : WeightedGraph V) (U : Finset V) : ℝ :=
  if h : (localShores U).Nonempty then (localShores U).inf' h (G.localCut U) else 0

theorem inducedMincut_nonneg (G : WeightedGraph V) (U : Finset V) :
    0 ≤ G.inducedMincut U := by
  unfold inducedMincut
  split
  · exact Finset.le_inf' _ _ (fun S _ => G.localCut_nonneg U S)
  · exact le_rfl

theorem inducedMincut_le (G : WeightedGraph V) {U S : Finset V}
    (h : LocalShore U S) : G.inducedMincut U ≤ G.localCut U S := by
  have hm := (mem_localShores _ _).mpr h
  rw [inducedMincut, dite_eq_left ⟨S, hm⟩]
  exact Finset.inf'_le _ hm

theorem exists_inducedMincut (G : WeightedGraph V) {U : Finset V}
    (hn : 2 ≤ U.card) :
    ∃ S, LocalShore U S ∧ G.localCut U S = G.inducedMincut U := by
  have h := (localShores_nonempty_iff U).mpr hn
  obtain ⟨S, hS, he⟩ := Finset.exists_mem_eq_inf' h (G.localCut U)
  exact ⟨S, (mem_localShores _ _).mp hS, by rw [inducedMincut, dite_eq_left h, he]⟩

theorem inducedMincut_eq_zero_of_card_le_one (G : WeightedGraph V) {U : Finset V}
    (hn : U.card ≤ 1) : G.inducedMincut U = 0 := by
  have h : ¬(localShores U).Nonempty := by rw [localShores_nonempty_iff]; omega
  simp [inducedMincut, h]

@[simp] theorem inducedMincut_singleton (G : WeightedGraph V) (u : V) :
    G.inducedMincut {u} = 0 := G.inducedMincut_eq_zero_of_card_le_one (by simp)

@[simp] theorem inducedMincut_empty (G : WeightedGraph V) :
    G.inducedMincut ∅ = 0 := G.inducedMincut_eq_zero_of_card_le_one (by simp)

@[simp] theorem inducedMincut_univ (G : WeightedGraph V) :
    G.inducedMincut Finset.univ = mincutValue G := by
  have he : localShores (Finset.univ : Finset V) = properShores V := by
    ext S
    simp [mem_localShores, mem_properShores, LocalShore, ProperShore,
      Finset.subset_univ, true_and, ← Finset.compl_eq_univ_sdiff,
      Finset.nonempty_iff_ne_empty, Finset.compl_eq_empty_iff]
  simp only [inducedMincut, he, localCut_univ, mincutValue]

end
end WeightedGraph
end CutQueryComplexity
