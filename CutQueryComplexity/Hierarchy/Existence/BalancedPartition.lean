import CutQueryComplexity.Hierarchy.Existence.BandwidthPartition

/-! # Balanced partitions with the child-weight property (hierarchy plan, Milestone 4)

For `|P| ≥ 2` with bandwidth `λ`, `exists_balanced_partition` gives a partition of `P` whose
parts have bandwidth `λ` and at most `5|P|/6` vertices, and with child weight `25λ`:

  `2|X| ≤ |P|  ⟹  ∑_C cross(X ∩ C, Cᶜ) ≤ 25λ cross(X, P ∖ X)`.

Proof outline.

1. Take a minimum cut `A | B` of `P` among those with `6|A|, 6|B| ≥ |P|`. Moving a set `U` with
   `3|U| ≤ 2|P|` to either side keeps one side balanced, so `cross(A ∩ U, B ∩ U) ≤ out(U)`
   (`uncross`).
2. Among partitions of `P` into parts with bandwidth `λ`, each inside `A` or inside `B`, take
   one minimizing `∑ out(C)`. Replacing parts with union `U` (`3|U| ≤ 2|P|`) by bandwidth
   partitions of `A ∩ U` and `B ∩ U` shows `∑_{C ⊆ U} out(C) ≤ 6 out(U)`.
3. For `X`, the children with `4|X ∩ C| > 3|C|` are heavy; their union `U` has
   `out(U) ≤ (3λ + 1) cross(X, P ∖ X)`, and the light children are controlled by their own
   bandwidth. This gives child weight `19λ + 6 ≤ 25λ`. (The plan's `24λ` overlooks the boundary
   of `X` toward `Pᶜ`; it is bounded by the bandwidth of `P` at the cost of one more `λ`.)
-/

namespace CutQueryComplexity
namespace Hierarchy

open WeightedGraph Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## Cut and cross helpers -/

omit [Fintype V] in
/-- Sums of crosses of disjoint pieces into a common set. -/
theorem sum_cross_le_cross (J : WeightedGraph V) {ι : Type} (Y : Finset ι) (f g : ι → Finset V)
    (T : Finset V) (hdisj : (Y : Set ι).PairwiseDisjoint f) (hg : ∀ y ∈ Y, g y ⊆ T) :
    ∑ y ∈ Y, J.cross (f y) (g y) ≤ J.cross (Y.biUnion f) T := by
  calc ∑ y ∈ Y, J.cross (f y) (g y) ≤ ∑ y ∈ Y, J.cross (f y) T :=
        sum_le_sum fun y hy => cross_mono J le_rfl (hg y hy)
    _ = J.cross (Y.biUnion f) T := by unfold cross; rw [sum_biUnion hdisj]

/-- The cut of a disjoint union is at most the sum of the cuts. -/
theorem cut_biUnion_le (J : WeightedGraph V) {ι : Type} (Y : Finset ι) (f : ι → Finset V)
    (hdisj : (Y : Set ι).PairwiseDisjoint f) :
    J.cut (Y.biUnion f) ≤ ∑ y ∈ Y, J.cut (f y) := by
  rw [← cross_compl]
  unfold cross
  rw [sum_biUnion hdisj]
  refine sum_le_sum fun y hy => ?_
  rw [← cross_compl]
  exact cross_mono J le_rfl (compl_subset_compl.mpr (subset_biUnion_of_mem f hy))

/-- `out(U ∪ W) ≤ out(U) + out(W)` for disjoint `U`, `W`. -/
theorem cut_union_le (J : WeightedGraph V) {U W : Finset V} (h : Disjoint U W) :
    J.cut (U ∪ W) ≤ J.cut U + J.cut W := by
  rw [← cross_compl, cross_union_left J _ _ _ h]
  gcongr <;> rw [← cross_compl] <;> exact cross_mono J le_rfl (compl_subset_compl.mpr (by simp))

/-- Bandwidth of a singleton. -/
theorem bandwidth_singleton (J : WeightedGraph V) (v : V) {lam : ℝ} :
    Bandwidth J {v} lam := by
  intro U hU hc
  have : U = ∅ := by
    rw [card_singleton] at hc
    exact card_eq_zero.mp (by omega)
  subst this; simp

/-! ## Moving a set across a cut -/

/-- Moving `U` to the side of `A` changes the cut of `P` by at most
`out(U) − cross(A ∩ U, (P ∖ A) ∩ U)`. -/
theorem move_le (J : WeightedGraph V) {P A U : Finset V} (_hA : A ⊆ P) (hU : U ⊆ P) :
    J.cross (A ∪ U) (P \ (A ∪ U)) ≤
      J.cross A (P \ A) - J.cross (A ∩ U) ((P \ A) ∩ U) + J.cut U := by
  set B := P \ A
  have hBU : P \ (A ∪ U) = B \ U := by ext v; simp [B]; tauto
  have hUA : U \ A = B ∩ U := by
    ext v; simp only [mem_sdiff, mem_inter, B]
    exact ⟨fun ⟨h1, h2⟩ => ⟨⟨hU h1, h2⟩, h1⟩, fun ⟨⟨_, h2⟩, h1⟩ => ⟨h1, h2⟩⟩
  rw [hBU]
  have h1 : J.cross (A ∪ U) (B \ U) = J.cross A (B \ U) + J.cross (B ∩ U) (B \ U) := by
    rw [← union_sdiff_self_eq_union, cross_union_left J _ _ _ disjoint_sdiff, hUA]
  have h2 : J.cross A B = J.cross A (B \ U) + J.cross A (B ∩ U) := by
    rw [← cross_union_right J _ _ _ (disjoint_sdiff_inter B U), sdiff_union_inter]
  have h3 : J.cross (A ∩ U) (B ∩ U) ≤ J.cross A (B ∩ U) := cross_mono J inter_subset_left le_rfl
  have h4 : J.cross (B ∩ U) (B \ U) ≤ J.cut U := by
    rw [← cross_compl]
    exact cross_mono J inter_subset_right fun v hv => mem_compl.mpr (mem_sdiff.mp hv).2
  have h5 : J.cross (A ∩ U) (B ∩ U) = J.cross (A ∩ U) ((P \ A) ∩ U) := rfl
  linarith

/-- A balanced cut of `P`. -/
def Balanced (P A : Finset V) : Prop := A ⊆ P ∧ P.card ≤ 6 * A.card ∧ P.card ≤ 6 * (P \ A).card

/-- **Uncrossing at a minimum balanced cut.** -/
theorem uncross (J : WeightedGraph V) {P A : Finset V} (hA : Balanced P A)
    (hmin : ∀ A', Balanced P A' → J.cross A (P \ A) ≤ J.cross A' (P \ A'))
    {U : Finset V} (hU : U ⊆ P) (hUc : 3 * U.card ≤ 2 * P.card) :
    J.cross (A ∩ U) ((P \ A) ∩ U) ≤ J.cut U := by
  by_contra hcon
  push Not at hcon
  -- moving `U` to `A` is cheaper, so it is unbalanced
  have h1 := move_le J hA.1 hU
  have hunb1 : ¬ Balanced P (A ∪ U) := fun hb => by
    have := hmin _ hb; linarith
  -- moving `U` to `B` is cheaper, so it is unbalanced
  have hB : P \ A ⊆ P := sdiff_subset
  have h2 := move_le J hB hU
  have hPPA : P \ (P \ A) = A := Finset.sdiff_sdiff_eq_self hA.1
  have hBA : P \ (P \ A ∪ U) = A \ U := by ext v; have hv1 : v ∈ U → v ∈ P := fun h => hU h; have hv2 : v ∈ A → v ∈ P := fun h => hA.1 h; simp; tauto
  have hsym : ∀ X Y : Finset V, J.cross X Y = J.cross Y X := fun X Y => J.cross_comm X Y
  have hunb2 : ¬ Balanced P (A \ U) := fun hb => by
    have := hmin _ hb
    have e : P \ (A \ U) = P \ A ∪ U := by ext v; have hv1 : v ∈ U → v ∈ P := fun h => hU h; have hv2 : v ∈ A → v ∈ P := fun h => hA.1 h; simp; tauto
    rw [e, hsym (A \ U)] at this
    rw [hPPA, hBA] at h2
    rw [hsym (P \ A) A, hsym ((P \ A) ∩ U) (A ∩ U)] at h2
    linarith
  -- the sizes
  have hcA : (A ∪ U).card = A.card + (U \ A).card := by
    rw [← card_union_of_disjoint disjoint_sdiff, union_sdiff_self_eq_union]
  apply hunb1
  refine ⟨union_subset hA.1 hU, ?_, ?_⟩
  · have := card_le_card (subset_union_left : A ⊆ A ∪ U); have := hA.2.1; omega
  · by_contra hc
    push Not at hc
    apply hunb2
    refine ⟨sdiff_subset.trans hA.1, ?_, ?_⟩
    · by_contra hc'
      push Not at hc'
      -- `|P| = |A ∖ U| + |(P ∖ A) ∖ U| + |U|`
      have e1 : P \ (A ∪ U) = (P \ A) \ U := by ext v; have hv1 : v ∈ U → v ∈ P := fun h => hU h; have hv2 : v ∈ A → v ∈ P := fun h => hA.1 h; simp; tauto
      have hpart : (A \ U).card + ((P \ A) \ U).card + U.card = P.card := by
        have d1 : Disjoint (A \ U) ((P \ A) \ U) := disjoint_left.mpr fun v h h' =>
          (mem_sdiff.mp (mem_sdiff.mp h').1).2 (mem_sdiff.mp h).1
        have d2 : Disjoint (A \ U ∪ (P \ A) \ U) U := disjoint_left.mpr fun v h h' => by
          rcases mem_union.mp h with h | h
          · exact (mem_sdiff.mp h).2 h'
          · exact (mem_sdiff.mp h).2 h'
        have e : A \ U ∪ (P \ A) \ U ∪ U = P := by
          ext v; simp only [mem_union, mem_sdiff]
          constructor
          · rintro ((⟨h, _⟩ | ⟨⟨h, _⟩, _⟩) | h)
            exacts [hA.1 h, h, hU h]
          · intro hv; by_cases hvU : v ∈ U
            · exact Or.inr hvU
            · by_cases hvA : v ∈ A
              · exact Or.inl (Or.inl ⟨hvA, hvU⟩)
              · exact Or.inl (Or.inr ⟨⟨hv, hvA⟩, hvU⟩)
        rw [← card_union_of_disjoint d1, ← card_union_of_disjoint d2, e]
      rw [e1] at hc
      omega
    · have e : P \ (A \ U) = (P \ A) ∪ U := by ext v; have hv1 : v ∈ U → v ∈ P := fun h => hU h; have hv2 : v ∈ A → v ∈ P := fun h => hA.1 h; simp; tauto
      rw [e]
      have := card_le_card (subset_union_left : P \ A ⊆ (P \ A) ∪ U); have := hA.2.2; omega

/-! ## The minimal admissible partition -/

/-- Partitions of `P` into parts of bandwidth `λ`, each inside `A` or inside `P ∖ A`. -/
def Admissible (J : WeightedGraph V) (lam : ℝ) (P A : Finset V) (Ps : Finset (Finset V)) :
    Prop :=
  IsPart P Ps ∧ ∀ C ∈ Ps, Bandwidth J C lam ∧ (C ⊆ A ∨ C ⊆ P \ A)

theorem admissible_singletons (J : WeightedGraph V) (lam : ℝ) {P A : Finset V} :
    Admissible J lam P A (P.image singleton) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro C hC; obtain ⟨v, -, rfl⟩ := mem_image.mp hC; exact singleton_nonempty v
  · intro C hC C' hC' hne
    obtain ⟨v, -, rfl⟩ := mem_image.mp hC
    obtain ⟨w, -, rfl⟩ := mem_image.mp hC'
    show Disjoint ({v} : Finset V) {w}
    rw [disjoint_singleton]
    exact fun h => hne (by rw [h])
  · ext v
    simp only [mem_biUnion, mem_image, id]
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, hv⟩
      rw [mem_singleton.mp hv]; exact hw
    · intro hv; exact ⟨{v}, ⟨v, hv, rfl⟩, mem_singleton_self v⟩
  · intro C hC
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hC
    refine ⟨bandwidth_singleton J v, ?_⟩
    by_cases hvA : v ∈ A
    · exact Or.inl (singleton_subset_iff.mpr hvA)
    · exact Or.inr (singleton_subset_iff.mpr (mem_sdiff.mpr ⟨hv, hvA⟩))

omit [Fintype V] in
/-- A part outside a subfamily is disjoint from its union. -/
theorem disjoint_biUnion_of_not_mem {P : Finset V} {Ps Q : Finset (Finset V)} (h : IsPart P Ps)
    (hQ : Q ⊆ Ps) {X : Finset V} (hX : X ∈ Ps) (hXQ : X ∉ Q) : Disjoint X (Q.biUnion id) := by
  rw [disjoint_biUnion_right]
  intro C hC
  exact h.disj hX (hQ hC) (fun he => hXQ (he ▸ hC))

/-- **Replacement.** At a minimal admissible partition, parts with union `U`,
`3|U| ≤ 2|P|`, have total boundary at most `6 out(U)`. -/
theorem replace_le (J : WeightedGraph V) {lam : ℝ} (hlam1 : 1 ≤ lam)
    (hlamB : 4 * beta (Fintype.card V) ≤ lam) {P A : Finset V} (hA : Balanced P A)
    (hAmin : ∀ A', Balanced P A' → J.cross A (P \ A) ≤ J.cross A' (P \ A'))
    {Ps : Finset (Finset V)} (hPs : Admissible J lam P A Ps)
    (hmin : ∀ Ps', Admissible J lam P A Ps' → F J Ps ≤ F J Ps')
    {Q : Finset (Finset V)} (hQ : Q ⊆ Ps) (hUc : 3 * (Q.biUnion id).card ≤ 2 * P.card) :
    ∑ C ∈ Q, J.cut C ≤ 6 * J.cut (Q.biUnion id) := by
  set U := Q.biUnion id
  have hUP : U ⊆ P := biUnion_subset.mpr fun C hC => hPs.1.subset (hQ hC)
  obtain ⟨Pa, hPa, hPab, hPaF⟩ := exists_bandwidth_partition J hlam1 hlamB (A ∩ U)
  obtain ⟨Pb, hPb, hPbb, hPbF⟩ := exists_bandwidth_partition J hlam1 hlamB ((P \ A) ∩ U)
  set Ps' := (Ps \ Q) ∪ (Pa ∪ Pb)
  have hrestU : ∀ X ∈ Ps \ Q, Disjoint X U := fun X hX =>
    disjoint_biUnion_of_not_mem hPs.1 hQ (mem_sdiff.mp hX).1 (mem_sdiff.mp hX).2
  have hPaU : ∀ X ∈ Pa, X ⊆ U := fun X hX => (hPa.subset hX).trans inter_subset_right
  have hPbU : ∀ X ∈ Pb, X ⊆ U := fun X hX => (hPb.subset hX).trans inter_subset_right
  have hPaA : ∀ X ∈ Pa, X ⊆ A := fun X hX => (hPa.subset hX).trans inter_subset_left
  have hPbA : ∀ X ∈ Pb, X ⊆ P \ A := fun X hX => (hPb.subset hX).trans inter_subset_left
  -- the three families are disjoint
  have hd1 : Disjoint (Ps \ Q) (Pa ∪ Pb) := by
    rw [disjoint_left]
    intro X hX hX'
    have hX0 : X.Nonempty := hPs.1.nonempty X (mem_sdiff.mp hX).1
    obtain ⟨v, hv⟩ := hX0
    have hsub : X ⊆ U := by
      rcases mem_union.mp hX' with h | h
      exacts [hPaU X h, hPbU X h]
    exact disjoint_left.mp (hrestU X hX) hv (hsub hv)
  have hd2 : Disjoint Pa Pb := by
    rw [disjoint_left]
    intro X hX hX'
    obtain ⟨v, hv⟩ := hPa.nonempty X hX
    exact (mem_sdiff.mp (hPbA X hX' hv)).2 (hPaA X hX hv)
  -- the replacement is admissible
  have hadm : Admissible J lam P A Ps' := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro X hX
      rcases mem_union.mp hX with h | h
      · exact hPs.1.nonempty X (mem_sdiff.mp h).1
      · rcases mem_union.mp h with h | h
        exacts [hPa.nonempty X h, hPb.nonempty X h]
    · intro X hX Y hY hne
      rcases mem_union.mp hX with hX | hX <;> rcases mem_union.mp hY with hY | hY
      · exact hPs.1.disj (mem_sdiff.mp hX).1 (mem_sdiff.mp hY).1 hne
      · have hsub : Y ⊆ U := by
          rcases mem_union.mp hY with h | h
          exacts [hPaU Y h, hPbU Y h]
        exact (hrestU X hX).mono_right hsub
      · have hsub : X ⊆ U := by
          rcases mem_union.mp hX with h | h
          exacts [hPaU X h, hPbU X h]
        exact ((hrestU Y hY).mono_right hsub).symm
      · rcases mem_union.mp hX with hX | hX <;> rcases mem_union.mp hY with hY | hY
        · exact hPa.disj hX hY hne
        · exact disjoint_left.mpr fun v hv hv' =>
            (mem_sdiff.mp (hPbA Y hY hv')).2 (hPaA X hX hv)
        · exact disjoint_left.mpr fun v hv hv' =>
            (mem_sdiff.mp (hPbA X hX hv)).2 (hPaA Y hY hv')
        · exact hPb.disj hX hY hne
    · show ((Ps \ Q) ∪ (Pa ∪ Pb)).biUnion id = P
      rw [union_biUnion, union_biUnion, hPa.union, hPb.union]
      apply subset_antisymm
      · refine union_subset (biUnion_subset.mpr fun X hX => hPs.1.subset (mem_sdiff.mp hX).1)
          (union_subset (inter_subset_left.trans hA.1) (inter_subset_left.trans sdiff_subset))
      · intro v hv
        by_cases hvU : v ∈ U
        · by_cases hvA : v ∈ A
          · exact mem_union_right _ (mem_union_left _ (mem_inter.mpr ⟨hvA, hvU⟩))
          · exact mem_union_right _ (mem_union_right _ (mem_inter.mpr ⟨mem_sdiff.mpr ⟨hv, hvA⟩, hvU⟩))
        · refine mem_union_left _ ?_
          rw [← hPs.1.union] at hv
          obtain ⟨X, hX, hvX⟩ := mem_biUnion.mp hv
          refine mem_biUnion.mpr ⟨X, mem_sdiff.mpr ⟨hX, fun hXQ => hvU ?_⟩, hvX⟩
          exact mem_biUnion.mpr ⟨X, hXQ, hvX⟩
    · intro X hX
      rcases mem_union.mp hX with h | h
      · exact hPs.2 X (mem_sdiff.mp h).1
      · rcases mem_union.mp h with h | h
        · exact ⟨hPab X h, Or.inl (hPaA X h)⟩
        · exact ⟨hPbb X h, Or.inr (hPbA X h)⟩
  -- the boundary sums
  have hFPs : F J Ps = F J (Ps \ Q) + ∑ C ∈ Q, J.cut C := by
    unfold F; rw [← sum_sdiff hQ]
  have hFPs' : F J Ps' = F J (Ps \ Q) + F J Pa + F J Pb := by
    unfold F; rw [sum_union hd1, sum_union hd2]; ring
  have hsplit := cut_split J (inter_subset_right : A ∩ U ⊆ U)
  have hUA : U \ (A ∩ U) = (P \ A) ∩ U := by
    ext v; simp only [mem_sdiff, mem_inter]
    exact ⟨fun ⟨h1, h2⟩ => ⟨⟨hUP h1, fun h => h2 ⟨h, h1⟩⟩, h1⟩,
      fun ⟨⟨_, h2⟩, h1⟩ => ⟨h1, fun h => h2 h.1⟩⟩
  rw [hUA] at hsplit
  have hunc := uncross J hA hAmin hUP hUc
  have := hmin Ps' hadm
  linarith

/-! ## The child-weight bound -/

/-- **Child weight.** At a minimal admissible partition of a set with bandwidth `λ`. -/
theorem childWeight_le (J : WeightedGraph V) {lam : ℝ} (hlam1 : 1 ≤ lam)
    (hlamB : 4 * beta (Fintype.card V) ≤ lam) {P A : Finset V} (hbP : Bandwidth J P lam)
    (hA : Balanced P A)
    (hAmin : ∀ A', Balanced P A' → J.cross A (P \ A) ≤ J.cross A' (P \ A'))
    {Ps : Finset (Finset V)} (hPs : Admissible J lam P A Ps)
    (hmin : ∀ Ps', Admissible J lam P A Ps' → F J Ps ≤ F J Ps')
    {X : Finset V} (hXP : X ⊆ P) (hXc : 2 * X.card ≤ P.card) :
    ∑ C ∈ Ps, J.cross (X ∩ C) Cᶜ ≤ 25 * lam * J.cross X (P \ X) := by
  classical
  set c := J.cross X (P \ X)
  have hc0 : 0 ≤ c := J.cross_nonneg _ _
  have hdisj : (Ps : Set (Finset V)).PairwiseDisjoint id := hPs.1.disj
  set Hv := Ps.filter fun C => 3 * C.card < 4 * (X ∩ C).card
  set Lt := Ps.filter fun C => ¬ (3 * C.card < 4 * (X ∩ C).card)
  set U := Hv.biUnion id
  have hHv : Hv ⊆ Ps := filter_subset _ _
  have hLt : Lt ⊆ Ps := filter_subset _ _
  have hdisjHv : (Hv : Set (Finset V)).PairwiseDisjoint id := hdisj.subset (coe_subset.mpr hHv)
  have hdisjLt : (Lt : Set (Finset V)).PairwiseDisjoint id := hdisj.subset (coe_subset.mpr hLt)
  have hpw : ∀ (Y : Finset (Finset V)), Y ⊆ Ps → (f : Finset V → Finset V) →
      (∀ C, f C ⊆ C) → (Y : Set (Finset V)).PairwiseDisjoint f := by
    intro Y hY f hf C hC C' hC' hne
    exact (hdisj (hY hC) (hY hC') hne).mono (hf C) (hf C')
  -- `3|U| ≤ 2|P|`
  have hUc : 3 * U.card ≤ 2 * P.card := by
    have h1 : U.card = ∑ C ∈ Hv, C.card := card_biUnion hdisjHv
    have h2 : ∑ C ∈ Hv, (X ∩ C).card ≤ X.card := by
      rw [← card_biUnion (hpw Hv hHv (fun C => X ∩ C) fun C => inter_subset_right)]
      exact card_le_card (biUnion_subset.mpr fun C _ => inter_subset_left)
    have h3 : ∑ C ∈ Hv, 3 * C.card ≤ ∑ C ∈ Hv, 4 * (X ∩ C).card :=
      sum_le_sum fun C hC => (mem_filter.mp hC).2.le
    rw [← mul_sum, ← mul_sum] at h3
    omega
  -- light children
  have hlight : ∑ C ∈ Lt, J.cut (X ∩ C) ≤ lam * c := by
    calc ∑ C ∈ Lt, J.cut (X ∩ C) ≤ ∑ C ∈ Lt, lam * J.cross (X ∩ C) (C \ X) := by
          refine sum_le_sum fun C hC => ?_
          have hb := (hPs.2 C (hLt hC)).1
          have := hb (X ∩ C) inter_subset_right (by
            have := (mem_filter.mp hC).2; push Not at this
            exact this)
          have e : C \ (X ∩ C) = C \ X := by ext v; simp
          rwa [e] at this
      _ = lam * ∑ C ∈ Lt, J.cross (X ∩ C) (C \ X) := by rw [mul_sum]
      _ ≤ lam * J.cross (Lt.biUnion fun C => X ∩ C) (P \ X) := by
          gcongr
          exact sum_cross_le_cross J Lt _ _ _ (hpw Lt hLt _ fun C => inter_subset_right)
            fun C hC => fun v hv =>
              mem_sdiff.mpr ⟨hPs.1.subset (hLt hC) (mem_sdiff.mp hv).1, (mem_sdiff.mp hv).2⟩
      _ ≤ lam * c := by
          gcongr
          exact cross_mono J (biUnion_subset.mpr fun C _ => inter_subset_left) le_rfl
  -- the heavy union
  have hUP : U ⊆ P := biUnion_subset.mpr fun C hC => hPs.1.subset (hHv hC)
  have hYc : J.cut (U \ X) ≤ lam * c := by
    have e : U \ X = Hv.biUnion fun C => C \ X := by
      ext v; simp only [mem_sdiff, mem_biUnion, U, id]
      exact ⟨fun ⟨⟨C, hC, hv⟩, hvX⟩ => ⟨C, hC, hv, hvX⟩, fun ⟨C, hC, hv, hvX⟩ => ⟨⟨C, hC, hv⟩, hvX⟩⟩
    rw [e]
    calc J.cut (Hv.biUnion fun C => C \ X) ≤ ∑ C ∈ Hv, J.cut (C \ X) :=
          cut_biUnion_le J Hv _ (hpw Hv hHv _ fun C => sdiff_subset)
      _ ≤ ∑ C ∈ Hv, lam * J.cross (C \ X) (X ∩ C) := by
          refine sum_le_sum fun C hC => ?_
          have hb := (hPs.2 C (hHv hC)).1
          have hheavy := (mem_filter.mp hC).2
          have hcard : (C \ X).card + (X ∩ C).card = C.card := by
            rw [inter_comm, card_sdiff_add_card_inter]
          have := hb (C \ X) sdiff_subset (by omega)
          have e : C \ (C \ X) = X ∩ C := by ext v; simp; tauto
          rwa [e] at this
      _ = lam * ∑ C ∈ Hv, J.cross (X ∩ C) (C \ X) := by
          rw [mul_sum]; exact sum_congr rfl fun C _ => by rw [J.cross_comm]
      _ ≤ lam * J.cross (Hv.biUnion fun C => X ∩ C) (P \ X) := by
          gcongr
          exact sum_cross_le_cross J Hv _ _ _ (hpw Hv hHv _ fun C => inter_subset_right)
            fun C hC => fun v hv =>
              mem_sdiff.mpr ⟨hPs.1.subset (hHv hC) (mem_sdiff.mp hv).1, (mem_sdiff.mp hv).2⟩
      _ ≤ lam * c := by
          gcongr
          exact cross_mono J (biUnion_subset.mpr fun C _ => inter_subset_left) le_rfl
  set XU := X ∩ U
  have hXUcomp : J.cross XU Uᶜ ≤ (2 * lam + 1) * c := by
    -- `Uᶜ = Pᶜ ∪ ((P ∖ U) ∖ X) ∪ ((P ∖ U) ∩ X)`
    have hsplit1 : J.cross XU Uᶜ ≤ J.cross XU Pᶜ + J.cross XU (P \ U) := by
      rw [← cross_union_right J _ _ _ (disjoint_left.mpr fun v h h' =>
        (mem_compl.mp h) (mem_sdiff.mp h').1)]
      exact cross_mono J le_rfl fun v hv => by
        by_cases hvP : v ∈ P
        · exact mem_union.mpr (Or.inr (mem_sdiff.mpr ⟨hvP, mem_compl.mp hv⟩))
        · exact mem_union.mpr (Or.inl (mem_compl.mpr hvP))
    have hP : J.cross XU Pᶜ ≤ lam * c := by
      calc J.cross XU Pᶜ ≤ J.cross X Xᶜ := cross_mono J inter_subset_left
            (compl_subset_compl.mpr hXP)
        _ = J.cut X := cross_compl J X
        _ ≤ lam * c := hbP X hXP (by omega)
    have hsplit2 : J.cross XU (P \ U) = J.cross XU ((P \ U) \ X) + J.cross XU ((P \ U) ∩ X) := by
      rw [← cross_union_right J _ _ _ (disjoint_sdiff_inter _ _), sdiff_union_inter]
    have hA1 : J.cross XU ((P \ U) \ X) ≤ c :=
      cross_mono J inter_subset_left fun v hv =>
        mem_sdiff.mpr ⟨(mem_sdiff.mp (mem_sdiff.mp hv).1).1, (mem_sdiff.mp hv).2⟩
    have hA2 : J.cross XU ((P \ U) ∩ X) ≤ lam * c := by
      have e : (P \ U) ∩ X = Lt.biUnion fun C => X ∩ C := by
        ext v; simp only [mem_inter, mem_sdiff, mem_biUnion, U, id, Lt, mem_filter]
        constructor
        · rintro ⟨⟨hvP, hvU⟩, hvX⟩
          rw [← hPs.1.union] at hvP
          obtain ⟨C, hC, hvC⟩ := mem_biUnion.mp hvP
          refine ⟨C, ⟨hC, fun hh => hvU ⟨C, mem_filter.mpr ⟨hC, hh⟩, hvC⟩⟩, hvX, hvC⟩
        · rintro ⟨C, ⟨hC, hlt⟩, hvX, hvC⟩
          refine ⟨⟨hPs.1.subset hC hvC, ?_⟩, hvX⟩
          rintro ⟨C', hC', hvC'⟩
          have := IsPart.eq_of_mem_of_inter (h := hPs.1) hC (hHv hC') hvC hvC'
          subst this
          exact hlt (mem_filter.mp hC').2
      rw [e]
      calc J.cross XU (Lt.biUnion fun C => X ∩ C)
          = ∑ C ∈ Lt, J.cross XU (X ∩ C) := by
            rw [J.cross_comm]; unfold cross
            rw [sum_biUnion (hpw Lt hLt _ fun C => inter_subset_right)]
            exact sum_congr rfl fun C _ => by
              rw [show (∑ u ∈ X ∩ C, ∑ v ∈ XU, J.w u v) = J.cross (X ∩ C) XU from rfl,
                J.cross_comm]; rfl
        _ ≤ ∑ C ∈ Lt, J.cut (X ∩ C) := by
            refine sum_le_sum fun C hC => ?_
            rw [J.cross_comm, ← cross_compl]
            refine cross_mono J le_rfl fun v hv => mem_compl.mpr fun hv' => ?_
            -- `v ∈ U` lies in a heavy part, `v ∈ C` in a light one
            obtain ⟨C', hC', hvC'⟩ := mem_biUnion.mp (mem_inter.mp hv).2
            have := IsPart.eq_of_mem_of_inter (h := hPs.1) (hLt hC) (hHv hC')
              (mem_inter.mp hv').2 hvC'
            subst this
            exact (mem_filter.mp hC).2 (mem_filter.mp hC').2
        _ ≤ lam * c := hlight
    linarith
  have hUcut : J.cut U ≤ (3 * lam + 1) * c := by
    have hsplitU : J.cut U = J.cross XU Uᶜ + J.cross (U \ X) Uᶜ := by
      rw [← cross_compl, ← cross_union_left J _ _ _ (by
        exact disjoint_left.mpr fun v h h' => (mem_sdiff.mp h').2 (mem_inter.mp h).1)]
      congr 1; ext v; simp [XU]; tauto
    have hY : J.cross (U \ X) Uᶜ ≤ J.cut (U \ X) := by
      rw [← cross_compl]; exact cross_mono J le_rfl (compl_subset_compl.mpr sdiff_subset)
    linarith
  -- heavy children
  have hheavy : ∑ C ∈ Hv, J.cut C ≤ 6 * J.cut U :=
    replace_le J hlam1 hlamB hA hAmin hPs hmin hHv hUc
  -- assemble
  have hsplitSum : ∑ C ∈ Ps, J.cross (X ∩ C) Cᶜ =
      ∑ C ∈ Hv, J.cross (X ∩ C) Cᶜ + ∑ C ∈ Lt, J.cross (X ∩ C) Cᶜ := by
    rw [sum_filter_add_sum_filter_not]
  have hH : ∑ C ∈ Hv, J.cross (X ∩ C) Cᶜ ≤ ∑ C ∈ Hv, J.cut C :=
    sum_le_sum fun C _ => by rw [← cross_compl]; exact cross_mono J inter_subset_right le_rfl
  have hL : ∑ C ∈ Lt, J.cross (X ∩ C) Cᶜ ≤ ∑ C ∈ Lt, J.cut (X ∩ C) :=
    sum_le_sum fun C _ => by
      rw [← cross_compl]; exact cross_mono J le_rfl (compl_subset_compl.mpr inter_subset_right)
  nlinarith

/-! ## The balanced partition -/

/-- **Milestone 4.** -/
theorem exists_balanced_partition (J : WeightedGraph V) {lam : ℝ} (hlam1 : 1 ≤ lam)
    (hlamB : 4 * beta (Fintype.card V) ≤ lam) {P : Finset V} (hP2 : 2 ≤ P.card)
    (hbP : Bandwidth J P lam) :
    ∃ Ps, IsPart P Ps ∧ (∀ C ∈ Ps, Bandwidth J C lam) ∧ (∀ C ∈ Ps, 6 * C.card ≤ 5 * P.card) ∧
      ∀ X ⊆ P, 2 * X.card ≤ P.card →
        ∑ C ∈ Ps, J.cross (X ∩ C) Cᶜ ≤ 25 * lam * J.cross X (P \ X) := by
  classical
  -- a minimum balanced cut
  have hbal : (P.powerset.filter (Balanced P)).Nonempty := by
    obtain ⟨A, hA, hAc⟩ := exists_subset_card_eq (show P.card / 2 ≤ P.card by omega)
    refine ⟨A, mem_filter.mpr ⟨mem_powerset.mpr hA, hA, by omega, ?_⟩⟩
    rw [card_sdiff_of_subset hA]; omega
  obtain ⟨A, hAmem, hAmin⟩ := exists_min_image _ (fun A => J.cross A (P \ A)) hbal
  have hA : Balanced P A := (mem_filter.mp hAmem).2
  have hAmin' : ∀ A', Balanced P A' → J.cross A (P \ A) ≤ J.cross A' (P \ A') := fun A' hA' =>
    hAmin A' (mem_filter.mpr ⟨mem_powerset.mpr hA'.1, hA'⟩)
  -- a minimal admissible partition
  have hfam : ((P.powerset.powerset).filter (Admissible J lam P A)).Nonempty := by
    refine ⟨P.image singleton, mem_filter.mpr ⟨mem_powerset.mpr fun C hC => ?_,
      admissible_singletons J lam⟩⟩
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hC
    exact mem_powerset.mpr (singleton_subset_iff.mpr hv)
  obtain ⟨Ps, hPsmem, hPsmin⟩ := exists_min_image _ (F J) hfam
  have hPs : Admissible J lam P A Ps := (mem_filter.mp hPsmem).2
  have hmin : ∀ Ps', Admissible J lam P A Ps' → F J Ps ≤ F J Ps' := fun Ps' h' =>
    hPsmin Ps' (mem_filter.mpr ⟨mem_powerset.mpr fun C hC =>
      mem_powerset.mpr (h'.1.subset hC), h'⟩)
  refine ⟨Ps, hPs.1, fun C hC => (hPs.2 C hC).1, fun C hC => ?_, fun X hX hXc =>
    childWeight_le J hlam1 hlamB hbP hA hAmin' hPs hmin hX hXc⟩
  rcases (hPs.2 C hC).2 with h | h
  · have h1 := card_le_card h
    have h2 := hA.2.2
    have h3 : (P \ A).card + A.card = P.card := card_sdiff_add_card_eq_card hA.1
    omega
  · have h1 := card_le_card h
    have h2 := hA.2.1
    have h3 : (P \ A).card + A.card = P.card := card_sdiff_add_card_eq_card hA.1
    omega

end Hierarchy
end CutQueryComplexity
