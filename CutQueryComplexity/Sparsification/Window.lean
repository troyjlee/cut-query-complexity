import CutQueryComplexity.Sparsification.KruskalInvariant
import CutQueryComplexity.Sparsification.EstimateCall

/-! # Scale windows and batch invariants

Let `H` be the approximate maximum spanning forest, with
`d̃(u,v) = H.bottleneck u v ≤ k(u,v) ≤ (n²/2) d̃(u,v)`. A pair is *remaining* if its
endpoints are in different blocks and `d̃ > 0`. Before each batch the schedule
computes `D`, the largest `d̃` of a remaining pair, and uses scale
`κ ≤ n² D / 2` and regions: the components of `H` restricted to edges of weight
at least `D/n²`.

The batch invariant at scale `κ` has two parts:

* `Refines G π κ`: vertices in one block are `κ`-strongly related in `G`;
* `Separated G π (2κ)`: vertices in different blocks have strength below `2κ`.

A remaining pair attaining `D` then gives `D/2 < κ`. So every `κ`-strongly
related pair is connected in the region forest, and each true `κ`-component lies
in a single region.

A successful batch coarsens the partition. It merges only `κ/2`-related pairs and
merges every `κ`-related pair. It therefore establishes `Refines (κ/2)` and
`Separated κ`, and the next scale `min(κ/2, n²D'/2)` again satisfies the
invariant. Each positive edge first internalized at scale `κ` gets the label
`β = κ/2` with `k_e/4 < β ≤ k_e`. A batch at scale at most `D` contracts a pair
attaining `D`.
-/

namespace CutQueryComplexity.WeightedGraph
noncomputable section
open scoped Classical
variable {V B : Type} [Fintype V] [DecidableEq V]

/-! ### Invariants -/

/-- Every block lies inside a true `κ`-strong component. -/
def Refines (G : WeightedGraph V) (π : V → B) (κ : ℝ) : Prop :=
  ∀ u v, π u = π v → G.StrongRelated κ u v

/-- Pairs in different blocks have strength below `κ`. -/
def Separated (G : WeightedGraph V) (π : V → B) (κ : ℝ) : Prop :=
  ∀ u v, π u ≠ π v → G.strength u v < κ

theorem Refines.mono {G : WeightedGraph V} {π : V → B} {κ τ : ℝ} (h : G.Refines π κ)
    (hle : τ ≤ κ) : G.Refines π τ := fun u v he => (h u v he).mono hle

theorem Separated.mono {G : WeightedGraph V} {π : V → B} {κ τ : ℝ} (h : G.Separated π κ)
    (hle : κ ≤ τ) : G.Separated π τ := fun u v he => (h u v he).trans_le hle

theorem refines_of_injective (G : WeightedGraph V) {π : V → B} (hπ : Function.Injective π)
    (κ : ℝ) : G.Refines π κ := fun u _ he => hπ he ▸ G.strongRelated_refl κ u

/-- Separation contracts every `κ`-related pair. -/
theorem Separated.eq_of_related {G : WeightedGraph V} {π : V → B} {κ : ℝ}
    (h : G.Separated π κ) {u v : V} (hr : G.StrongRelated κ u v) : π u = π v := by
  by_contra hne
  have huv : u ≠ v := fun he => hne (he ▸ rfl)
  exact absurd ((G.le_strength_iff huv κ).mpr hr) (not_le.mpr (h u v hne))

theorem separated_of_related (G : WeightedGraph V) {π : V → B} {κ : ℝ}
    (h : ∀ u v, G.StrongRelated κ u v → π u = π v) : G.Separated π κ := by
  intro u v hne
  by_contra hle
  have huv : u ≠ v := fun he => hne (he ▸ rfl)
  exact hne (h u v ((G.le_strength_iff huv κ).mp (not_lt.mp hle)))

/-! ### Remaining pairs and the top level -/

/-- Pairs in different blocks joined by the forest. -/
def remaining (H : WeightedGraph V) (π : V → B) : Finset (V × V) :=
  Finset.univ.filter (fun p => π p.1 ≠ π p.2 ∧ 0 < H.bottleneck p.1 p.2)

@[simp] theorem mem_remaining (H : WeightedGraph V) (π : V → B) (p : V × V) :
    p ∈ remaining H π ↔ π p.1 ≠ π p.2 ∧ 0 < H.bottleneck p.1 p.2 := by
  simp [remaining]

/-- The largest forest bottleneck of a remaining pair, and zero if none remains. -/
def topLevel (H : WeightedGraph V) (π : V → B) : ℝ :=
  if h : (remaining H π).Nonempty then
    (remaining H π).sup' h (fun p => H.bottleneck p.1 p.2) else 0

theorem le_topLevel (H : WeightedGraph V) (π : V → B) {p : V × V}
    (hp : p ∈ remaining H π) : H.bottleneck p.1 p.2 ≤ topLevel H π := by
  simp only [topLevel, show (remaining H π).Nonempty from ⟨p, hp⟩, ↓reduceDIte]
  exact Finset.le_sup' (fun p : V × V => H.bottleneck p.1 p.2) hp

theorem exists_topLevel (H : WeightedGraph V) (π : V → B) (h : (remaining H π).Nonempty) :
    ∃ p ∈ remaining H π, H.bottleneck p.1 p.2 = topLevel H π := by
  obtain ⟨p, hp, he⟩ := Finset.exists_mem_eq_sup' h (fun p : V × V => H.bottleneck p.1 p.2)
  exact ⟨p, hp, by simp only [topLevel, h, ↓reduceDIte, he]⟩

theorem topLevel_pos (H : WeightedGraph V) (π : V → B) (h : (remaining H π).Nonempty) :
    0 < topLevel H π := by
  obtain ⟨p, hp, he⟩ := exists_topLevel H π h
  exact he ▸ ((mem_remaining H π p).mp hp).2

theorem topLevel_nonneg (H : WeightedGraph V) (π : V → B) : 0 ≤ topLevel H π := by
  by_cases h : (remaining H π).Nonempty
  · exact (topLevel_pos H π h).le
  · simp only [topLevel, h, ↓reduceDIte, le_refl]

/-! ### Bounds from the forest -/

variable {G H : WeightedGraph V}

/-- Every pair in different blocks has strength at most `n² D / 2`. -/
theorem strength_le_topLevel (hH : IsApproxKruskalForest G H) (π : V → B) {u v : V}
    (hne : π u ≠ π v) :
    G.strength u v ≤ (Fintype.card V : ℝ) ^ 2 / 2 * topLevel H π := by
  have hb := (hH.bottleneck_bounds u v).2
  by_cases hp : 0 < H.bottleneck u v
  · exact hb.trans (mul_le_mul_of_nonneg_left
      (le_topLevel H π ((mem_remaining H π (u, v)).mpr ⟨hne, hp⟩)) (by positivity))
  · have hz : H.bottleneck u v = 0 := le_antisymm (not_lt.mp hp) (H.bottleneck_nonneg u v)
    have h0 : G.strength u v ≤ 0 := by simpa [hz] using hb
    have htop := topLevel_nonneg H π
    exact h0.trans (by positivity)

/-- A remaining pair attaining `D` forces `D < 2κ` under separation at `2κ`. -/
theorem topLevel_lt (hH : IsApproxKruskalForest G H) {π : V → B} {κ : ℝ}
    (hsep : G.Separated π (2 * κ)) (h : (remaining H π).Nonempty) :
    topLevel H π < 2 * κ := by
  obtain ⟨p, hp, he⟩ := exists_topLevel H π h
  have hl := (hH.bottleneck_bounds p.1 p.2).1
  rw [he] at hl
  exact hl.trans_lt (hsep p.1 p.2 ((mem_remaining H π p).mp hp).1)

/-- **Regions.** A `κ`-related pair is joined in the forest restricted to weights at
least `t`, whenever `0 < t ≤ 2κ/n²`. -/
theorem reachable_of_related (hH : IsApproxKruskalForest G H) {κ t : ℝ} (ht : 0 < t)
    (htκ : t * (Fintype.card V : ℝ) ^ 2 ≤ 2 * κ) {u v : V} (hr : G.StrongRelated κ u v) :
    (H.threshold t).Reachable u v := by
  by_cases huv : u = v
  · subst huv
    rfl
  have hk := (G.le_strength_iff huv κ).mpr hr
  have he := hH.estimate u v
  have hn : (0 : ℝ) < (Fintype.card V : ℝ) ^ 2 := by
    have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨u⟩
    positivity
  apply (H.le_bottleneck_iff huv ht).mp
  by_contra hlt
  push Not at hlt
  have : (Fintype.card V : ℝ) ^ 2 * H.bottleneck u v < (Fintype.card V : ℝ) ^ 2 * t :=
    mul_lt_mul_of_pos_left hlt hn
  nlinarith

/-- The region threshold `D/n²` works at every scale above `D/2`. -/
theorem reachable_of_related_top (hH : IsApproxKruskalForest G H) {π : V → B} {κ : ℝ}
    (hD : 0 < topLevel H π) (hκ : topLevel H π < 2 * κ) {u v : V}
    (hr : G.StrongRelated κ u v) :
    (H.threshold (topLevel H π / (Fintype.card V : ℝ) ^ 2)).Reachable u v := by
  have hn : (0 : ℝ) < (Fintype.card V : ℝ) ^ 2 := by
    have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨u⟩
    positivity
  refine reachable_of_related hH (by positivity) ?_ hr
  rw [div_mul_cancel₀ _ hn.ne']
  exact hκ.le

/-! ### One batch -/

/-- **Batch step.** A coarsening that merges only `κ/2`-related pairs and merges all
`κ`-related pairs turns `Refines κ` into `Refines (κ/2)` and establishes
`Separated κ`. -/
theorem batch_step {π π' : V → B} {κ : ℝ} (hpre : G.Refines π κ)
    (hsound : ∀ u v, π' u = π' v → π u = π v ∨ G.StrongRelated (κ / 2) u v)
    (hcomplete : ∀ u v, G.StrongRelated κ u v → π' u = π' v) (hκ : 0 ≤ κ) :
    G.Refines π' (κ / 2) ∧ G.Separated π' κ := by
  refine ⟨fun u v he => ?_, separated_of_related G hcomplete⟩
  rcases hsound u v he with h | h
  · exact (hpre u v h).mono (by linarith)
  · exact h

/-- The next scale `min(κ/2, n² D'/2)` restores the invariant. -/
theorem next_scale_invariant (hH : IsApproxKruskalForest G H) {π : V → B} {κ : ℝ}
    (hr : G.Refines π (κ / 2)) (hs : G.Separated π κ) (hrem : (remaining H π).Nonempty) :
    let κ' := min (κ / 2) ((Fintype.card V : ℝ) ^ 2 / 2 * topLevel H π)
    G.Refines π κ' ∧ G.Separated π (2 * κ') := by
  intro κ'
  refine ⟨hr.mono (min_le_left _ _), ?_⟩
  rcases le_total (κ / 2) ((Fintype.card V : ℝ) ^ 2 / 2 * topLevel H π) with h | h
  · rw [show κ' = κ / 2 from min_eq_left h]
    exact hs.mono (by linarith)
  · rw [show κ' = (Fintype.card V : ℝ) ^ 2 / 2 * topLevel H π from min_eq_right h]
    intro u v hne
    have hle := strength_le_topLevel hH π hne
    have hpos : 0 < (Fintype.card V : ℝ) ^ 2 / 2 * topLevel H π := by
      have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨u⟩
      have := topLevel_pos H π hrem
      positivity
    linarith

/-- The first scale satisfies the invariant for the singleton partition. -/
theorem initial_invariant (hH : IsApproxKruskalForest G H) (hrem : (remaining H id).Nonempty) :
    let κ := (Fintype.card V : ℝ) ^ 2 / 2 * topLevel H (id : V → V)
    G.Refines (id : V → V) κ ∧ G.Separated (id : V → V) (2 * κ) := by
  intro κ
  refine ⟨refines_of_injective G Function.injective_id κ, ?_⟩
  intro u v hne
  have hle := strength_le_topLevel hH (id : V → V) hne
  have hpos : 0 < κ := by
    have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨u⟩
    have := topLevel_pos H (id : V → V) hrem
    positivity
  have hk : κ = (Fintype.card V : ℝ) ^ 2 / 2 * topLevel H (id : V → V) := rfl
  linarith

/-- **Labels.** A pair first joined in a successful batch at `κ` has strength in
`[κ/2, 2κ)`, so the label `β = κ/2` satisfies `k/4 < β ≤ k`. -/
theorem label_bounds {π π' : V → B} {κ : ℝ} (hsep : G.Separated π (2 * κ))
    (hnew : G.Refines π' (κ / 2)) {u v : V} (hne : π u ≠ π v) (hmerge : π' u = π' v) :
    G.strength u v / 4 < κ / 2 ∧ κ / 2 ≤ G.strength u v := by
  have huv : u ≠ v := fun he => hne (he ▸ rfl)
  refine ⟨by linarith [hsep u v hne], (G.le_strength_iff huv _).mpr (hnew u v hmerge)⟩

/-- **Progress.** After a successful batch at a scale at most `D`, every pair
attaining `D` is contracted. -/
theorem top_contracted (hH : IsApproxKruskalForest G H) {π π' : V → B} {κ : ℝ}
    (hs : G.Separated π' κ) (hκD : κ ≤ topLevel H π) {p : V × V}
    (hp : H.bottleneck p.1 p.2 = topLevel H π) : π' p.1 = π' p.2 := by
  by_contra hne
  have := hs p.1 p.2 hne
  have hl := (hH.bottleneck_bounds p.1 p.2).1
  linarith

end
end CutQueryComplexity.WeightedGraph
