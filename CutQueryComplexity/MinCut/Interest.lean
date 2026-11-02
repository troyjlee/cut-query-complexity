import CutQueryComplexity.Graph.InducedCut

/-! # Interest under sparsification

A cut `cut(Y ∪ Z)` of two disjoint sets equals `cut Y + cut Z − 2X` with cross
weight `X = cross(Y, Z)` (`cut_union_disjoint`). So if it beats both `cut Y` and
`cut Z`, the two sides have *mutual interest*: `cut Y < 2X` and `cut Z < 2X`
(`pruning`). This is the pruning step of the Mukhopadhyay–Nanongkai two-respecting
search, where `Y, Z` are the two sides of a pair of tree edges.

* `sparsifier_interest`: mutual interest in `G` gives `cut_H Y < 3·cross_H(Y, Z)`
  for any `1/11`-sparsifier `H`. One-sided interest does not transfer this way;
  the mutual hypothesis is what makes the three-cut error estimate close.
* `not_three_interested`: no set has `H`-interest in three disjoint partners.
-/

namespace CutQueryComplexity
namespace Interest

noncomputable section
open scoped Classical
variable {V : Type} [Fintype V]

/-- The cut of a disjoint union, through the cross weight. -/
theorem cut_union_disjoint (G : WeightedGraph V)
    {X Y : Finset V} (h : Disjoint X Y) :
    G.cut (X ∪ Y) = G.cut X + G.cut Y - 2 * G.cross X Y := by
  have hZ : Disjoint X (X ∪ Y)ᶜ := Finset.disjoint_left.mpr (fun v hv h' =>
    (Finset.mem_compl.mp h') (Finset.mem_union_left _ hv))
  have hZ' : Disjoint Y (X ∪ Y)ᶜ := Finset.disjoint_left.mpr (fun v hv h' =>
    (Finset.mem_compl.mp h') (Finset.mem_union_right _ hv))
  have hXc : Xᶜ = Y ∪ (X ∪ Y)ᶜ := by
    ext v
    simp only [Finset.mem_compl, Finset.mem_union]
    have : v ∈ X → v ∉ Y := fun hv => Finset.disjoint_left.mp h hv
    tauto
  have hYc : Yᶜ = X ∪ (X ∪ Y)ᶜ := by
    ext v
    simp only [Finset.mem_compl, Finset.mem_union]
    have : v ∈ X → v ∉ Y := fun hv => Finset.disjoint_left.mp h hv
    tauto
  rw [← WeightedGraph.cross_compl, ← WeightedGraph.cross_compl G X,
    ← WeightedGraph.cross_compl G Y, WeightedGraph.cross_union_left _ _ _ _ h, hXc, hYc,
    WeightedGraph.cross_union_right _ _ _ _ (Finset.disjoint_left.mpr (fun v hv h' =>
      (Finset.mem_compl.mp h') (Finset.mem_union_right _ hv))),
    WeightedGraph.cross_union_right _ _ _ _ (Finset.disjoint_left.mpr (fun v hv h' =>
      (Finset.mem_compl.mp h') (Finset.mem_union_left _ hv))), G.cross_comm Y X]
  ring

/-- `Y` sends more than half its cut into `Z`. -/
def Interested (G : WeightedGraph V) (Y Z : Finset V) : Prop := G.cut Y < 2 * G.cross Y Z

/-- `Y` sends more than a third of its cut into `Z`. -/
def Interested3 (G : WeightedGraph V) (Y Z : Finset V) : Prop := G.cut Y < 3 * G.cross Y Z

/-- **Pruning.** A pair beats both single cuts only under mutual interest. -/
theorem pruning (G : WeightedGraph V) {Y Z : Finset V} (h : Disjoint Y Z)
    (hY : G.cut (Y ∪ Z) < G.cut Y) (hZ : G.cut (Y ∪ Z) < G.cut Z) :
    Interested G Y Z ∧ Interested G Z Y := by
  rw [cut_union_disjoint G h] at hY hZ
  refine ⟨?_, ?_⟩
  · unfold Interested; linarith
  · unfold Interested; rw [G.cross_comm]; linarith

theorem cross_le_cut (G : WeightedGraph V) {Y Z : Finset V} (h : Disjoint Y Z) :
    G.cross Y Z ≤ G.cut Y := by
  rw [← WeightedGraph.cross_compl]
  exact G.cross_mono le_rfl (fun v hv => Finset.mem_compl.mpr
    (fun hY => Finset.disjoint_left.mp h hY hv))

/-- **Sparsifier transfer** under mutual interest. -/
theorem sparsifier_interest {G H : WeightedGraph V} {ε : ℝ} (hε : ε ≤ 1 / 11)
    (hH : ∀ S, (1 - ε) * G.cut S ≤ H.cut S ∧ H.cut S ≤ (1 + ε) * G.cut S)
    {Y Z : Finset V} (h : Disjoint Y Z) (hY : Interested G Y Z) (hZ : Interested G Z Y) :
    Interested3 H Y Z := by
  unfold Interested at hY hZ
  unfold Interested3
  rw [G.cross_comm] at hZ
  set X := G.cross Y Z
  have hu := cut_union_disjoint G h
  have hcY := cross_le_cut G h
  have hcZ : G.cross Y Z ≤ G.cut Z := by rw [G.cross_comm]; exact cross_le_cut G h.symm
  have hXH : 2 * H.cross Y Z = H.cut Y + H.cut Z - H.cut (Y ∪ Z) := by
    rw [cut_union_disjoint H h]; ring
  obtain ⟨hY1, hY2⟩ := hH Y
  obtain ⟨hZ1, _⟩ := hH Z
  obtain ⟨_, hU2⟩ := hH (Y ∪ Z)
  have hU : G.cut (Y ∪ Z) < 2 * X := by linarith
  have hε0 : 0 ≤ ε ∨ ε < 0 := le_or_gt 0 ε
  have hX0 : 0 ≤ X := G.cross_nonneg _ _
  -- Each of the three cuts is below `2X`, so the error is below `3εX`.
  have hYZ : 0 ≤ G.cut Y := G.cut_nonneg _
  have hZZ : 0 ≤ G.cut Z := G.cut_nonneg _
  have hUU : 0 ≤ G.cut (Y ∪ Z) := G.cut_nonneg _
  rcases hε0 with hε0 | hε0
  · nlinarith
  · nlinarith

/-- **Width two.** No set has `H`-interest in three disjoint sets outside it. -/
theorem not_three_interested (H : WeightedGraph V) {Y Z₁ Z₂ Z₃ : Finset V}
    (h1 : Disjoint Y Z₁) (h2 : Disjoint Y Z₂) (h3 : Disjoint Y Z₃) (h12 : Disjoint Z₁ Z₂)
    (h13 : Disjoint Z₁ Z₃) (h23 : Disjoint Z₂ Z₃) (i1 : Interested3 H Y Z₁)
    (i2 : Interested3 H Y Z₂) (i3 : Interested3 H Y Z₃) : False := by
  unfold Interested3 at i1 i2 i3
  have hd : Disjoint Z₁ (Z₂ ∪ Z₃) := Finset.disjoint_union_right.mpr ⟨h12, h13⟩
  have hsum : H.cross Y (Z₁ ∪ (Z₂ ∪ Z₃)) = H.cross Y Z₁ + H.cross Y Z₂ + H.cross Y Z₃ := by
    rw [H.cross_union_right _ _ _ hd, H.cross_union_right _ _ _ h23]
    ring
  have hle := cross_le_cut H (Y := Y) (Z := Z₁ ∪ (Z₂ ∪ Z₃))
    (Finset.disjoint_union_right.mpr ⟨h1, Finset.disjoint_union_right.mpr ⟨h2, h3⟩⟩)
  linarith

/-- Interest grows with the partner set. -/
theorem interested_mono (G : WeightedGraph V) {Y Z Z' : Finset V} (hZ : Z ⊆ Z')
    (h : Interested G Y Z) : Interested G Y Z' := by
  unfold Interested at *
  have := G.cross_mono (le_refl Y) hZ
  linarith

end
end Interest
end CutQueryComplexity
