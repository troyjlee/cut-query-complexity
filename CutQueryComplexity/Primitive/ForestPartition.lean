import CutQueryComplexity.Graph.ForestFacts
import CutQueryComplexity.Primitive.ResidualCache

/-! # Public block labels for a growing forest -/

namespace CutQueryComplexity
noncomputable section
open scoped Classical
variable {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]

/-- The public labels describe exactly the connected components of the known forest. -/
def ForestPartition (F : _root_.SimpleGraph V) (π : V → B) : Prop :=
  ∀ u v, F.Reachable u v ↔ π u = π v

theorem reachable_label_eq (F : _root_.SimpleGraph V) (π : V → B)
    (h : ∀ u v, F.Adj u v → π u = π v) {u v : V} (hr : F.Reachable u v) : π u = π v := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => rfl
  | cons hadj p ih => exact (h _ _ hadj).trans ih

/-- Merge the blocks of the observed original endpoints. -/
def pairMerge (π : V → B) (u v : V) : V → B :=
  mergeBlocks π {π u, π v} (π u)

theorem pairMerge_coarsens (π : V → B) (u v : V) {a b : V} (h : π a = π b) :
    pairMerge π u v a = pairMerge π u v b := by simp only [pairMerge, mergeBlocks, h]

theorem isBlockMerge_pair (π : V → B) {u v : V} (h : π u ≠ π v) :
    IsBlockMerge π (pairMerge π u v) := by
  refine ⟨{π u, π v}, π u, ?_, by simp, by simp [h], rfl⟩
  intro b hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl <;> simp only [mem_liveBlocks]
  · exact ⟨u, rfl⟩
  · exact ⟨v, rfl⟩

theorem ForestPartition.merge_pair {F : _root_.SimpleGraph V} {π : V → B}
    (h : ForestPartition F π) {u v : V} (hne : u ≠ v) :
    ForestPartition (F ⊔ _root_.SimpleGraph.edge u v) (pairMerge π u v) := by
  let F' := F ⊔ _root_.SimpleGraph.edge u v
  have hadj : F'.Adj u v := Or.inr
    ((_root_.SimpleGraph.edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl, rfl⟩, hne⟩)
  have anchor (x : V) (hx : π x ∈ ({π u, π v} : Finset B)) : F'.Reachable u x := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx
    · exact ((h u x).mpr hx.symm).mono le_sup_left
    · exact hadj.reachable.trans (((h v x).mpr hx.symm).mono le_sup_left)
  intro a b
  constructor
  · apply reachable_label_eq F' (pairMerge π u v)
    intro x y hxy
    rcases hxy with hxy | hxy
    · exact pairMerge_coarsens π u v ((h x y).mp hxy.reachable)
    · rcases (_root_.SimpleGraph.edge_adj _ _ _ _).mp hxy with ⟨hxy | hxy, _⟩
      · rcases hxy with ⟨rfl, rfl⟩; simp [pairMerge, mergeBlocks]
      · rcases hxy with ⟨rfl, rfl⟩; simp [pairMerge, mergeBlocks]
  · intro hab
    by_cases ha : π a ∈ ({π u, π v} : Finset B)
    · have hb : π b ∈ ({π u, π v} : Finset B) := by
        by_contra hb
        have he : π u = π b := by simpa [pairMerge, mergeBlocks, ha, hb] using hab
        exact hb (by simp [← he])
      exact (anchor a ha).symm.trans (anchor b hb)
    · have hb : π b ∉ ({π u, π v} : Finset B) := by
        intro hb
        have he : π a = π u := by simpa [pairMerge, mergeBlocks, ha, hb] using hab
        exact ha (by simp [he])
      exact ((h a b).mpr (by simpa [pairMerge, mergeBlocks, ha, hb] using hab)).mono le_sup_left

theorem ForestPartition.of_one_block {F : _root_.SimpleGraph V} {π : V → B}
    (h : ForestPartition F π) (hc : (liveBlocks π).card ≤ 1) (u v : V) : F.Reachable u v := by
  apply (h u v).mpr
  exact Finset.card_le_one.mp hc _ (by simp [mem_liveBlocks]) _ (by simp [mem_liveBlocks])

end
end CutQueryComplexity
