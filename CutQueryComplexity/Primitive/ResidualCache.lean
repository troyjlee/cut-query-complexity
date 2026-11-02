import CutQueryComplexity.Primitive.Residual

/-! # Updating the residual cache after merging blocks

Every merge of at least two live blocks uses one new original cut query and
strictly decreases the number of live blocks. The bound on merge histories
does not depend on how previous oracle answers selected the merges.
-/

namespace CutQueryComplexity
noncomputable section
open scoped Classical
open WeightedGraph
variable {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]

/-- Current nonempty block labels, with empty labels omitted. -/
def liveBlocks (π : V → B) : Finset B := Finset.univ.image π

@[simp] theorem mem_liveBlocks (π : V → B) (b : B) : b ∈ liveBlocks π ↔ ∃ v, π v = b := by
  simp [liveBlocks]

theorem card_liveBlocks_le (π : V → B) : (liveBlocks π).card ≤ Fintype.card V :=
  (Finset.card_image_le).trans (by simp)

/-- Merge the labels in `S` into its designated representative `b`. -/
def mergeBlocks (π : V → B) (S : Finset B) (b : B) : V → B :=
  fun v => if π v ∈ S then b else π v

theorem fiber_mergeBlocks_root (π : V → B) (S : Finset B) {b : B} (hb : b ∈ S) :
    fiber (mergeBlocks π S b) b = pull π S := by
  ext v
  simp only [mem_fiber, mem_pull, mergeBlocks]
  by_cases hv : π v ∈ S
  · simp [hv]
  · simp only [ite_eq_right hv, hv, ite_false, iff_false]
    intro he; exact hv (he ▸ hb)

theorem fiber_mergeBlocks_other (π : V → B) (S : Finset B) {b c : B} (hcb : c ≠ b) :
    fiber (mergeBlocks π S b) c = if c ∈ S then ∅ else fiber π c := by
  ext v
  by_cases hc : c ∈ S <;> by_cases hv : π v ∈ S
  · simp [mergeBlocks, hc, hv, Ne.symm hcb]
  · simp only [ite_eq_left hc, Finset.notMem_empty, mem_fiber, mergeBlocks, ite_eq_right hv,
      iff_false]
    intro he; exact hv (he ▸ hc)
  · have hvc : π v ≠ c := fun h => hc (h ▸ hv)
    simp [mergeBlocks, hc, hv, Ne.symm hcb, hvc]
  · simp [mergeBlocks, hc, hv]

/-- Update surviving entries, set the removed labels to zero, and store the new cut. -/
def updateBlockCache (S : Finset B) (b : B) (cache : B → ℝ) (newCut : ℝ) : B → ℝ :=
  fun c => if c = b then newCut else if c ∈ S then 0 else cache c

/-- Only the cut of the new union needs to be queried. -/
def mergeBlockCache (π : V → B) (S : Finset B) (b : B) (cache : B → ℝ) :
    DTree (Finset V) ℝ (B → ℝ) 1 :=
  DTree.query (pull π S) fun c => DTree.pure (updateBlockCache S b cache c)

theorem mergeBlockCache_run (G : WeightedGraph V) (π : V → B) (S : Finset B)
    {b : B} (hb : b ∈ S) (cache : B → ℝ) (hc : ∀ c, cache c = G.cut (fiber π c)) :
    (mergeBlockCache π S b cache).run G.cut =
      ((fun c => G.cut (fiber (mergeBlocks π S b) c)), 1) := by
  simp only [mergeBlockCache, DTree.run_query, DTree.run_pure]
  congr 1
  funext c
  by_cases hcb : c = b
  · subst c
    simp [updateBlockCache, fiber_mergeBlocks_root π S hb]
  · rw [fiber_mergeBlocks_other π S hcb]
    by_cases hcS : c ∈ S <;> simp [updateBlockCache, hcb, hcS, hc]

theorem liveBlocks_merge (π : V → B) {S : Finset B} {b : B}
    (hS : S ⊆ liveBlocks π) (hb : b ∈ S) :
    liveBlocks (mergeBlocks π S b) = (liveBlocks π \ S) ∪ {b} := by
  ext c
  simp only [mem_liveBlocks, Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · rintro ⟨v, hv⟩
    by_cases hs : π v ∈ S
    · right
      simpa [mergeBlocks, hs] using hv.symm
    · left
      have he : π v = c := by simpa [mergeBlocks, hs] using hv
      exact ⟨⟨v, he⟩, by simpa [he] using hs⟩
  · rintro (⟨⟨v, hv⟩, hc⟩ | rfl)
    · exact ⟨v, by simp [mergeBlocks, hv, hc]⟩
    · obtain ⟨v, hv⟩ := (mem_liveBlocks π c).mp (hS hb)
      exact ⟨v, by simp [mergeBlocks, hv, hb]⟩

theorem card_liveBlocks_merge (π : V → B) {S : Finset B} {b : B}
    (hS : S ⊆ liveBlocks π) (hb : b ∈ S) :
    (liveBlocks (mergeBlocks π S b)).card = (liveBlocks π).card - S.card + 1 := by
  rw [liveBlocks_merge π hS hb, Finset.card_union_of_disjoint]
  · rw [Finset.card_sdiff_of_subset hS, Finset.card_singleton]
  · exact Finset.disjoint_left.mpr (fun c hc he =>
      (Finset.mem_sdiff.mp hc).2 ((Finset.mem_singleton.mp he) ▸ hb))

/-- A valid nontrivial merge, independent of how the algorithm chose it. -/
def IsBlockMerge (π π' : V → B) : Prop := ∃ (S : Finset B) (b : B),
  S ⊆ liveBlocks π ∧ b ∈ S ∧ 2 ≤ S.card ∧ π' = mergeBlocks π S b

theorem IsBlockMerge.card_lt {π π' : V → B} (h : IsBlockMerge π π') :
    (liveBlocks π').card < (liveBlocks π).card := by
  obtain ⟨S, b, hS, hb, hn, rfl⟩ := h
  rw [card_liveBlocks_merge π hS hb]
  have := Finset.card_le_card hS
  omega

/-- Each step pays for at least one disappearing block. -/
theorem blockMerge_history_bound (π : ℕ → V → B) (m : ℕ)
    (h : ∀ i < m, IsBlockMerge (π i) (π (i + 1))) :
    m + (liveBlocks (π m)).card ≤ (liveBlocks (π 0)).card := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hprev := ih (fun i hi => h i (by omega))
      have hstep := (h m (by omega)).card_lt
      omega

/-- Any adaptive history has at most `n-1` nontrivial merges, including `n=0`. -/
theorem blockMerge_history_le (π : ℕ → V → B) (m : ℕ)
    (h : ∀ i < m, IsBlockMerge (π i) (π (i + 1))) : m ≤ Fintype.card V - 1 := by
  have hm := blockMerge_history_bound π m h
  have hn := card_liveBlocks_le (π 0)
  cases isEmpty_or_nonempty V with
  | inl he =>
      letI := he
      have hz : Fintype.card V = 0 := Fintype.card_eq_zero
      omega
  | inr he =>
      obtain ⟨v⟩ := he
      have hp : 0 < (liveBlocks (π m)).card := Finset.card_pos.mpr
        ⟨π m v, (mem_liveBlocks _ _).mpr ⟨v, rfl⟩⟩
      omega

end
end CutQueryComplexity
