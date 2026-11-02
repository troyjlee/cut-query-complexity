import CutQueryComplexity.Sparsification.CountedConcentration
import CutQueryComplexity.Probability.FiniteEvents
import CutQueryComplexity.Probability.Chernoff

/-! # Soundness of the estimation contraction

An estimation call samples a graph `X` whose mean is the reference graph `Q`,
then contracts the `3κ/4`-strong sets of `X`. Soundness says these sets never
cross the true `κ/2`-strong structure of `Q`.

Fix, before sampling, a recursive split of the region `T` along induced cuts of
`Q`-weight below `κ/2`, ending in `κ/2`-strong parts. It uses at most `|T|−1`
cuts. If each split cut keeps sampled weight below `3κ/4`, no `3κ/4`-strong set
of `X` can cross one, so each lies in a `κ/2`-strong set of `Q`. For counted
draws of weight at most `κ/ρ`, an additive Chernoff bound with exponent `1/4`
makes each split cut fail with probability at most `exp(−ρ/32)`.
Only this fixed family is union-bounded; the random strong sets are not.
-/

namespace CutQueryComplexity.WeightedGraph
noncomputable section
open scoped Classical ENNReal
open Probability
variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Additive upper tail -/

/-- Upper tail at an absolute threshold, for any upper bound on the mean. -/
theorem _root_.CutQueryComplexity.Probability.BoundedDraw.sum_additive_upper_tail
    (ds : List BoundedDraw) {μ : ℝ} (hμ : BoundedDraw.sumMean ds ≤ μ) (a : ℝ) :
    mass (BoundedDraw.sumLaw ds) (fun x => a ≤ x) ≤
      ENNReal.ofReal (Real.exp (5 / 16 * μ - a / 4)) := by
  have ht : Real.exp (1 / 4) - 1 ≤ 5 / 16 := by
    have := exp_sub_one_le_add_sq (t := 1 / 4) (by rw [abs_of_nonneg] <;> norm_num)
    linarith
  have ht0 : 0 ≤ Real.exp (1 / 4) - 1 := by
    have := Real.add_one_le_exp (1 / 4 : ℝ)
    linarith
  have hm := BoundedDraw.expMoment_sumLaw_le ds (1 / 4)
  have hb : expMoment (BoundedDraw.sumLaw ds) id (1 / 4) ≤
      ENNReal.ofReal (Real.exp (5 / 16 * μ)) := by
    refine hm.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
    have h0 := BoundedDraw.sumMean_nonneg ds
    nlinarith
  have := upper_tail_le_exp (BoundedDraw.sumLaw ds) id a (by norm_num : (0 : ℝ) ≤ 1 / 4) hb
  convert this using 3
  simp only [id]
  ring

/-! ### Local cuts of sampled graphs -/

omit [Fintype V] [DecidableEq V] in
theorem cross_addition (G H : WeightedGraph V) (S T : Finset V) :
    (G + H).cross S T = G.cross S T + H.cross S T := by
  simp only [cross, add_weight, Finset.sum_add_distrib]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem cross_zero (S T : Finset V) : (0 : WeightedGraph V).cross S T = 0 := by
  simp [cross]

omit [Fintype V] in
theorem localCut_addition (G H : WeightedGraph V) (U S : Finset V) :
    (G + H).localCut U S = G.localCut U S + H.localCut U S := cross_addition _ _ _ _

omit [Fintype V] in
@[simp] theorem localCut_zero (U S : Finset V) : (0 : WeightedGraph V).localCut U S = 0 :=
  cross_zero _ _

theorem localCut_le_cut_inter (G : WeightedGraph V) (U S : Finset V) :
    G.localCut U S ≤ G.cut (S ∩ U) := by
  apply G.cross_mono le_rfl
  intro v hv
  simp only [Finset.mem_sdiff] at hv
  simp [hv.2]

theorem localCut_edgeGraph_le (e : EdgeIndex V) (a : ℝ) (ha : 0 ≤ a) (U S : Finset V) :
    (edgeGraph e a ha).localCut U S ≤ a :=
  ((edgeGraph e a ha).localCut_le_cut_inter U S).trans (cut_edgeGraph_le e a ha _)

omit [Fintype V] in
theorem HasMean.localCut {p : PMF (WeightedGraph V)} {G : WeightedGraph V}
    (h : HasMean p G) (U S : Finset V) :
    expect p (fun X => ENNReal.ofReal (X.localCut U S)) = ENNReal.ofReal (G.localCut U S) :=
  h.cross _ _

/-! ### A fixed family of light split cuts -/

/-- Split cuts of weight below `κ₀`; any set not separated by them lies in a strong part. -/
def IsSplitFamily (Q : WeightedGraph V) (κ₀ : ℝ) (T : Finset V)
    (D : List (Finset V × Finset V)) : Prop :=
  (∀ x ∈ D, Q.localCut x.1 x.2 < κ₀) ∧
  ∀ K ⊆ T, (∀ x ∈ D, K ⊆ x.1 → K ⊆ x.2 ∨ K ⊆ x.1 \ x.2) →
    ∃ W, K ⊆ W ∧ W ⊆ T ∧ Q.IsStrong κ₀ W

theorem exists_splitFamily (Q : WeightedGraph V) (κ₀ : ℝ) (T : Finset V) :
    ∃ D, Q.IsSplitFamily κ₀ T D ∧ D.length ≤ T.card - 1 := by
  induction hn : T.card using Nat.strong_induction_on generalizing T with
  | _ n ih =>
  by_cases hs : Q.IsStrong κ₀ T
  · exact ⟨[], ⟨by simp, fun K hK _ => ⟨T, hK, le_rfl, hs⟩⟩, by simp⟩
  simp only [IsStrong, not_forall, not_le, exists_prop] at hs
  obtain ⟨S, hST, hTS, hcut⟩ := hs
  set A := S ∩ T
  have hA : A ⊆ T := Finset.inter_subset_right
  have hTA : T \ A = T \ S := by ext v; simp [A]
  have hcardA : A.card < n := hn ▸ Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨hA, fun he => by
      obtain ⟨v, hv⟩ := hTS
      have : v ∈ A := he ▸ (Finset.mem_sdiff.mp hv).1
      exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_inter.mp this).1⟩)
  have hcardB : (T \ A).card < n := by
    rw [← hn]
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, fun he => ?_⟩
    obtain ⟨v, hv⟩ := hST
    have hvT := (Finset.mem_inter.mp hv).2
    rw [← he] at hvT
    exact (Finset.mem_sdiff.mp hvT).2 hv
  obtain ⟨D₁, ⟨hc₁, hs₁⟩, hl₁⟩ := ih _ hcardA A rfl
  obtain ⟨D₂, ⟨hc₂, hs₂⟩, hl₂⟩ := ih _ hcardB (T \ A) rfl
  have hApos : 1 ≤ A.card := Finset.card_pos.mpr hST
  have hBpos : 1 ≤ (T \ A).card := Finset.card_pos.mpr (hTA ▸ hTS)
  have hsplit : (T \ A).card + A.card = T.card := Finset.card_sdiff_add_card_eq_card hA
  refine ⟨(T, A) :: (D₁ ++ D₂), ⟨?_, ?_⟩, ?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · simpa only [A, localCut_inter] using hcut
    · rcases List.mem_append.mp hx with hx | hx
      · exact hc₁ x hx
      · exact hc₂ x hx
  · intro K hK hsep
    rcases hsep (T, A) (by simp) hK with hKA | hKB
    · obtain ⟨W, hKW, hWA, hW⟩ := hs₁ K hKA (fun x hx => hsep x (by simp [hx]))
      exact ⟨W, hKW, hWA.trans hA, hW⟩
    · obtain ⟨W, hKW, hWB, hW⟩ := hs₂ K hKB (fun x hx => hsep x (by simp [hx]))
      exact ⟨W, hKW, hWB.trans Finset.sdiff_subset, hW⟩
  · simp only [List.length_cons, List.length_append]
    omega

/-- A strong set of `X` cannot cross a split cut that is light in `X`. -/
theorem IsSplitFamily.strong_subset {Q X : WeightedGraph V} {κ₀ θ : ℝ} {T : Finset V}
    {D : List (Finset V × Finset V)} (hD : Q.IsSplitFamily κ₀ T D)
    (hlight : ∀ x ∈ D, X.localCut x.1 x.2 < θ) {K : Finset V} (hKT : K ⊆ T)
    (hK : X.IsStrong θ K) : ∃ W, K ⊆ W ∧ W ⊆ T ∧ Q.IsStrong κ₀ W := by
  apply hD.2 K hKT
  intro x hx hKP
  by_contra hcross
  simp only [not_or, Finset.not_subset] at hcross
  obtain ⟨⟨a, haK, haA⟩, ⟨b, hbK, hbPA⟩⟩ := hcross
  have hbA : b ∈ x.2 := by
    by_contra hb
    exact hbPA (Finset.mem_sdiff.mpr ⟨hKP hbK, hb⟩)
  have hθ := hK x.2 ⟨b, Finset.mem_inter.mpr ⟨hbA, hbK⟩⟩ ⟨a, Finset.mem_sdiff.mpr ⟨haK, haA⟩⟩
  have := (X.localCut_mono hKP x.2).trans_lt (hlight x hx)
  linarith

namespace CountedBucket

/-! ### Counted draws keep each fixed light cut light -/

/-- Normalized local cuts of counted samples are independent sums of `[0,1]` draws. -/
theorem sampleLaw_localCut_boundedLaw (bs : List (CountedBucket V)) {lam : ℝ} (hlam : 0 ≤ lam)
    (hb : ∀ b ∈ bs, lam * (b.mass / b.count) ≤ 1) (U S : Finset V) :
    ∃ ds : List BoundedDraw,
      (sampleLaw bs).map (fun X => lam * X.localCut U S) = BoundedDraw.sumLaw ds := by
  apply independentGraphSum_boundedLaw
  · simp
  · intro X Y
    rw [localCut_addition, mul_add]
  · intro p hp X hX
    obtain ⟨b, hb', rfl⟩ := List.mem_map.mp hp
    obtain ⟨e, _, rfl⟩ := (b.mem_support_drawLaw X).mp hX
    refine ⟨mul_nonneg hlam (localCut_nonneg _ _ _), ?_⟩
    exact (mul_le_mul_of_nonneg_left (localCut_edgeGraph_le e _ _ U S) hlam).trans
      (hb b (mem_of_mem_expanded hb'))

/-- A fixed cut lighter than `κ/2` reaches `3κ/4` with probability at most `exp(−ρ/32)`. -/
theorem sampleLaw_light_cut (bs : List (CountedBucket V)) {κ ρ : ℝ} (hκ : 0 < κ)
    (hρ : 0 ≤ ρ) (hb : ∀ b ∈ bs, ρ * (b.mass / b.count) ≤ κ) {U S : Finset V}
    (hQ : (reference bs).localCut U S ≤ κ / 2) :
    Probability.mass (sampleLaw bs) (fun X => 3 * κ / 4 ≤ X.localCut U S) ≤
      ENNReal.ofReal (Real.exp (-(ρ / 32))) := by
  set lam := ρ / κ
  have hlam : 0 ≤ lam := div_nonneg hρ hκ.le
  have hb' : ∀ b ∈ bs, lam * (b.mass / b.count) ≤ 1 := by
    intro b hbs
    rw [div_mul_eq_mul_div, div_le_one hκ]
    exact hb b hbs
  obtain ⟨ds, hds⟩ := sampleLaw_localCut_boundedLaw bs hlam hb' U S
  -- The draw sum has mean `lam` times the reference cut.
  have hmean : BoundedDraw.sumMean ds = lam * (reference bs).localCut U S := by
    have he : ENNReal.ofReal (BoundedDraw.sumMean ds) =
        ENNReal.ofReal (lam * (reference bs).localCut U S) := by
      rw [← BoundedDraw.expect_sumLaw_eq, ← hds, expect_map]
      simp only [ENNReal.ofReal_mul hlam, expect_const_mul]
      rw [(sampleLaw_mean bs).localCut U S]
    have hr := congrArg ENNReal.toReal he
    rwa [ENNReal.toReal_ofReal (BoundedDraw.sumMean_nonneg ds),
      ENNReal.toReal_ofReal (mul_nonneg hlam (localCut_nonneg _ _ _))] at hr
  have hμ : BoundedDraw.sumMean ds ≤ ρ / 2 := by
    rw [hmean]
    calc
      lam * (reference bs).localCut U S ≤ lam * (κ / 2) := mul_le_mul_of_nonneg_left hQ hlam
      _ = ρ / 2 := by simp only [lam]; field_simp
  have htail := BoundedDraw.sum_additive_upper_tail ds hμ (3 * ρ / 4)
  rw [← hds, mass_map] at htail
  calc
    Probability.mass (sampleLaw bs) (fun X => 3 * κ / 4 ≤ X.localCut U S)
        ≤ Probability.mass (sampleLaw bs) ((fun x => 3 * ρ / 4 ≤ x) ∘ fun X => lam * X.localCut U S) := by
      apply mass_mono
      intro X hX
      simp only [Function.comp_apply]
      have := mul_le_mul_of_nonneg_left hX hlam
      have he : lam * (3 * κ / 4) = 3 * ρ / 4 := by simp only [lam]; field_simp
      linarith
    _ ≤ _ := htail
    _ = _ := by congr 2; ring

/-- **Soundness.** With probability at least `1 − (|T|−1) exp(−ρ/32)`, every
`3κ/4`-strong subset of the region in the sample lies in a `κ/2`-strong subset of
the region in the reference graph. -/
theorem sampleLaw_sound (bs : List (CountedBucket V)) {κ ρ : ℝ} (hκ : 0 < κ)
    (hρ : 0 ≤ ρ) (hb : ∀ b ∈ bs, ρ * (b.mass / b.count) ≤ κ) (T : Finset V) :
    Probability.mass (sampleLaw bs) (fun X => ¬∀ K ⊆ T, X.IsStrong (3 * κ / 4) K →
        ∃ W, K ⊆ W ∧ W ⊆ T ∧ (reference bs).IsStrong (κ / 2) W) ≤
      ((T.card - 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(ρ / 32))) := by
  obtain ⟨D, hD, hlen⟩ := (reference bs).exists_splitFamily (κ / 2) T
  calc
    _ ≤ (D.toFinset.card : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(ρ / 32))) := by
      apply mass_failure_le_card_mul (sampleLaw bs) D.toFinset
        (fun x X => X.localCut x.1 x.2 < 3 * κ / 4)
      · intro X _ hlight K hKT hK
        exact hD.strong_subset (fun x hx => hlight x (List.mem_toFinset.mpr hx)) hKT hK
      · intro x hx
        simp only [not_lt]
        exact sampleLaw_light_cut bs hκ hρ hb (hD.1 x (List.mem_toFinset.mp hx)).le
    _ ≤ _ := by
      gcongr
      exact_mod_cast (List.toFinset_card_le D).trans hlen

end CountedBucket
end
end CutQueryComplexity.WeightedGraph
