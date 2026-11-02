import CutQueryComplexity.Hierarchy.RackeShah.Basic
import CutQueryComplexity.Certificate.MaxFlow

/-! # Bounded transportation and the split certificate (Räcke–Shah, M2)

`exists_transport`: nonnegative supplies `a` can be routed through `Q` to receiving capacities
`z` whenever `a(U) ≤ c_Q(U) + z(U)` for every `U`: there is a flow `F` feasible in `Q` and a
receiving function `0 ≤ r ≤ z` with `div F = a − r`. The proof adds a sink copy `inr v` of
every vertex joined to `inl v` by capacity `z v` and applies `exists_maxFlow` with all originals
as capacitated sources; the hypothesis makes every source cut at least the total supply, so the
maximum flow saturates every source, and the sink copies have a single edge each, which keeps
the received amounts nonnegative. Supplies dominated by `a` route with the same bounds, since the
hypothesis is monotone in `a`.

`exists_splitCert`: a bottleneck `U` of `X` (small side, positive boundary `e = b_X(U)`, internal
cut `h` with `f h ≤ 2e`) contains a set `W` minimizing `c_G(W, X ∖ W) / b_X(W)` among the sets
of positive boundary; with `ρ` that minimum, `ρ f ≤ 2` and every `Z ⊆ W` satisfies
`c_G(Z, X ∖ W) ≤ c_{G[W]}(Z) + ρ b_X(Z)` (`SplitCert`), and `W ⊆ U` is part of the conclusion.
This is the finite-minimizer form of the source's Lemma 3, with `ρ = 0` allowed.
-/

namespace CutQueryComplexity
namespace Hierarchy
namespace RackeShah

open WeightedGraph Finset Certificate

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## The sink network -/

/-- `Q` on the originals `inl v`, a sink copy `inr v` joined to `inl v` with capacity `z v`. -/
noncomputable def sinkNet (Q : WeightedGraph V) (z : V → ℝ) (hz : ∀ v, 0 ≤ z v) :
    WeightedGraph (V ⊕ V) where
  w x y := match x, y with
    | Sum.inl u, Sum.inl v => Q.w u v
    | Sum.inl u, Sum.inr v => if u = v then z u else 0
    | Sum.inr u, Sum.inl v => if u = v then z u else 0
    | Sum.inr _, Sum.inr _ => 0
  symm x y := by
    rcases x with u | u <;> rcases y with v | v
    · exact Q.symm u v
    · show (if u = v then z u else 0) = if v = u then z v else 0
      by_cases h : u = v
      · subst h; rfl
      · simp [h, Ne.symm h]
    · show (if u = v then z u else 0) = if v = u then z v else 0
      by_cases h : u = v
      · subst h; rfl
      · simp [h, Ne.symm h]
    · rfl
  nonneg x y := by
    rcases x with u | u <;> rcases y with v | v
    · exact Q.nonneg u v
    · show 0 ≤ if u = v then z u else 0
      split <;> simp [hz]
    · show 0 ≤ if u = v then z u else 0
      split <;> simp [hz]
    · exact le_rfl
  diag x := by
    rcases x with u | u
    · exact Q.diag u
    · rfl

omit [Fintype V] in
theorem sinkNet_ll (Q : WeightedGraph V) (z : V → ℝ) (hz : ∀ v, 0 ≤ z v) (u v : V) :
    (sinkNet Q z hz).w (Sum.inl u) (Sum.inl v) = Q.w u v := rfl

omit [Fintype V] in
theorem sinkNet_lr (Q : WeightedGraph V) (z : V → ℝ) (hz : ∀ v, 0 ≤ z v) (u v : V) :
    (sinkNet Q z hz).w (Sum.inl u) (Sum.inr v) = if u = v then z u else 0 := rfl

omit [Fintype V] in
theorem sinkNet_rl (Q : WeightedGraph V) (z : V → ℝ) (hz : ∀ v, 0 ≤ z v) (u v : V) :
    (sinkNet Q z hz).w (Sum.inr u) (Sum.inl v) = if u = v then z u else 0 := rfl

omit [Fintype V] in
theorem sinkNet_rr (Q : WeightedGraph V) (z : V → ℝ) (hz : ∀ v, 0 ≤ z v) (u v : V) :
    (sinkNet Q z hz).w (Sum.inr u) (Sum.inr v) = 0 := rfl

/-- **Bounded transportation.** -/
theorem exists_transport (Q : WeightedGraph V) (a z : V → ℝ) (ha : ∀ v, 0 ≤ a v)
    (hz : ∀ v, 0 ≤ z v)
    (h : ∀ U : Finset V, ∑ v ∈ U, a v ≤ Q.cut U + ∑ v ∈ U, z v) :
    ∃ F : V → V → ℝ, ∃ r : V → ℝ, Feasible Q F ∧ (∀ v, netOut F v = a v - r v) ∧
      ∀ v, 0 ≤ r v ∧ r v ≤ z v := by
  set A : Finset (V ⊕ V) := univ.image Sum.inl with hAdef
  set B : Finset (V ⊕ V) := univ.image Sum.inr with hBdef
  have hAmem : ∀ v, Sum.inl v ∈ A := fun v => mem_image_of_mem _ (mem_univ v)
  have hBmem : ∀ v, Sum.inr v ∈ B := fun v => mem_image_of_mem _ (mem_univ v)
  have hAinr : ∀ v, Sum.inr v ∉ A := by
    intro v hv
    obtain ⟨u, -, h⟩ := mem_image.mp hv
    exact Sum.inl_ne_inr h
  have hAB : Disjoint A B := by
    rw [disjoint_left]
    intro x hx hx'
    obtain ⟨u, -, rfl⟩ := mem_image.mp hx
    obtain ⟨v, -, h⟩ := mem_image.mp hx'
    exact Sum.inr_ne_inl h
  let cap : V ⊕ V → ℝ := fun x => match x with | Sum.inl v => a v | Sum.inr _ => 0
  have hcap : ∀ x, 0 ≤ cap x := by
    intro x; rcases x with v | v
    · exact ha v
    · exact le_rfl
  obtain ⟨f, S, hf, hcons, hsrc, hsink, hSB, hval⟩ := exists_maxFlow (sinkNet Q z hz) A B hAB cap hcap
  -- the shore on the originals
  set S₀ : Finset V := univ.filter fun v => Sum.inl v ∈ S
  have hinl : ∀ v, Sum.inl v ∈ S ↔ v ∈ S₀ := by intro v; simp [S₀]
  have hinr : ∀ v, Sum.inr v ∉ S := by
    intro v hv
    exact disjoint_left.mp hSB hv (hBmem v)
  -- the cut of the sink network at `S`
  have hcut : (sinkNet Q z hz).cut S = Q.cut S₀ + ∑ v ∈ S₀, z v := by
    rw [cut_eq_sum_ite, cut_eq_sum_ite]
    simp only [Fintype.sum_sum_type, sinkNet_ll, sinkNet_lr, sinkNet_rl, sinkNet_rr, hinl,
      hinr, not_false_eq_true, and_true, false_and, ite_false, sum_const_zero,
      _root_.add_zero]
    rw [sum_add_distrib]
    congr 1
    conv_rhs => rw [← univ_inter S₀, ← filter_mem_eq_inter, sum_filter]
    refine sum_congr rfl fun u _ => ?_
    by_cases hu : u ∈ S₀ <;> simp [hu]
  -- the value is at least the total supply, hence every source is saturated
  have hA : ∑ x ∈ A, netOut f x = ∑ v, netOut f (Sum.inl v) := by
    rw [sum_image fun u _ v _ h => Sum.inl_injective h]
  have hcapA : ∑ x ∈ A \ S, cap x = ∑ v, a v - ∑ v ∈ S₀, a v := by
    have h1 : ∑ x ∈ A \ (A ∩ S), cap x + ∑ x ∈ A ∩ S, cap x = ∑ x ∈ A, cap x :=
      sum_sdiff inter_subset_left
    have h1' : A \ (A ∩ S) = A \ S := by
      ext x; simp only [mem_sdiff, mem_inter, not_and]; tauto
    have h2 : ∑ x ∈ A, cap x = ∑ v, a v := by
      rw [sum_image fun u _ v _ h => Sum.inl_injective h]
    have h3 : ∑ x ∈ A ∩ S, cap x = ∑ v ∈ S₀, a v := by
      have : A ∩ S = S₀.image Sum.inl := by
        ext x
        rcases x with v | v
        · constructor
          · intro h
            exact mem_image_of_mem _ ((hinl v).mp (mem_inter.mp h).2)
          · intro h
            obtain ⟨u, hu, hu'⟩ := mem_image.mp h
            rw [Sum.inl_injective hu'] at hu
            exact mem_inter.mpr ⟨hAmem v, (hinl v).mpr hu⟩
        · constructor
          · intro h; exact absurd (mem_inter.mp h).1 (hAinr v)
          · intro h
            obtain ⟨u, -, hu⟩ := mem_image.mp h
            exact absurd hu Sum.inl_ne_inr
      rw [this, sum_image fun u _ v _ h => Sum.inl_injective h]
    rw [h1'] at h1
    linarith
  have hsat : ∀ v, netOut f (Sum.inl v) = a v := by
    have hle : ∀ v ∈ (univ : Finset V), netOut f (Sum.inl v) ≤ a v :=
      fun v _ => hsrc _ (hAmem v)
    have hsum : ∑ v, netOut f (Sum.inl v) = ∑ v, a v := by
      refine le_antisymm (sum_le_sum hle) ?_
      rw [← hA, hval, hcut, hcapA]
      have := h S₀
      linarith
    intro v
    exact (sum_eq_sum_iff_of_le hle).mp hsum v (mem_univ v)
  -- the flow on the originals and the received amounts
  refine ⟨fun u v => f (Sum.inl u) (Sum.inl v), fun v => f (Sum.inl v) (Sum.inr v), ⟨?_, ?_⟩,
    ?_, ?_⟩
  · intro u v; exact hf.1 _ _
  · intro u v; exact hf.2 (Sum.inl u) (Sum.inl v)
  · intro v
    have hv := hsat v
    unfold netOut at hv ⊢
    rw [Fintype.sum_sum_type] at hv
    have hzero : ∀ u, u ≠ v → f (Sum.inl v) (Sum.inr u) = 0 := by
      intro u huv
      have := hf.2 (Sum.inl v) (Sum.inr u)
      rw [sinkNet_lr, ite_eq_right (Ne.symm huv)] at this
      exact abs_nonpos_iff.mp this
    rw [sum_eq_single v (fun u _ huv => hzero u huv) (fun h => absurd (mem_univ v) h)] at hv
    linarith
  · intro v
    constructor
    · have hs := hsink (Sum.inr v) (hBmem v)
      unfold netOut at hs
      rw [Fintype.sum_sum_type] at hs
      have hzero : ∀ u, u ≠ v → f (Sum.inr v) (Sum.inl u) = 0 := by
        intro u huv
        have := hf.2 (Sum.inr v) (Sum.inl u)
        rw [sinkNet_rl, ite_eq_right (Ne.symm huv)] at this
        exact abs_nonpos_iff.mp this
      have hzero' : ∀ u, f (Sum.inr v) (Sum.inr u) = 0 := by
        intro u
        have := hf.2 (Sum.inr v) (Sum.inr u)
        rw [sinkNet_rr] at this
        exact abs_nonpos_iff.mp this
      rw [sum_eq_single v (fun u _ huv => hzero u huv) (fun h => absurd (mem_univ v) h),
        sum_eq_zero fun u _ => hzero' u, _root_.add_zero] at hs
      have := hf.1 (Sum.inl v) (Sum.inr v)
      linarith
    · have := hf.2 (Sum.inl v) (Sum.inr v)
      rw [sinkNet_lr, ite_eq_left rfl] at this
      exact (le_abs_self _).trans this

/-! ## Bottlenecks and split certificates -/

/-- A bottleneck of `X` for the expansion factor `f`: a small side `U` of positive boundary
whose internal cut `h = c_G(U, X ∖ U)` satisfies `f h ≤ 2 b_X(U)`. -/
structure Bottleneck (G : WeightedGraph V) (f : ℝ) (X U : Finset V) : Prop where
  subset : U ⊆ X
  half : 2 * U.card ≤ X.card
  pos : 0 < ∑ v ∈ U, bd G X v
  small : f * G.cross U (X \ U) ≤ 2 * ∑ v ∈ U, bd G X v

/-- The certificate of a split `X = W ⊔ (X ∖ W)` with ratio `ρ`: `W` is a small nonempty side,
`ρ f ≤ 2`, and every `Z ⊆ W` has weight into `X ∖ W` at most `c_{G[W]}(Z) + ρ b_X(Z)`. -/
structure SplitCert (G : WeightedGraph V) (f : ℝ) (X W : Finset V) (ρ : ℝ) : Prop where
  subset : W ⊆ X
  nonempty : W.Nonempty
  half : 2 * W.card ≤ X.card
  rho_nonneg : 0 ≤ ρ
  rho_small : ρ * f ≤ 2
  cutIneq : ∀ Z ⊆ W, G.cross Z (X \ W) ≤ G.cross Z (W \ Z) + ρ * ∑ v ∈ Z, bd G X v

/-- **The split certificate of a bottleneck** (source Lemma 3, finite-minimizer form). -/
theorem exists_splitCert {G : WeightedGraph V} {f : ℝ} (hf : 0 ≤ f) {X U : Finset V}
    (hb : Bottleneck G f X U) : ∃ W ρ, W ⊆ U ∧ SplitCert G f X W ρ := by
  set e : Finset V → ℝ := fun W => ∑ v ∈ W, bd G X v with he_def
  have he : ∀ W, e W = ∑ v ∈ W, bd G X v := fun _ => rfl
  set cand := U.powerset.filter fun W => 0 < e W
  have hU : U ∈ cand := mem_filter.mpr ⟨mem_powerset.mpr subset_rfl, hb.pos⟩
  obtain ⟨W, hW, hmin⟩ := exists_min_image cand (fun W => G.cross W (X \ W) / e W) ⟨U, hU⟩
  have hWU : W ⊆ U := mem_powerset.mp (mem_filter.mp hW).1
  have heW : 0 < e W := (mem_filter.mp hW).2
  set ρ := G.cross W (X \ W) / e W
  have hρ0 : 0 ≤ ρ := div_nonneg (G.cross_nonneg _ _) heW.le
  have hWX : W ⊆ X := hWU.trans hb.subset
  -- the ratio inequality for subsets of `W`
  have hkey : ∀ Y ⊆ W, ρ * e Y ≤ G.cross Y (X \ Y) := by
    intro Y hY
    have hY0 : 0 ≤ e Y := by rw [he]; exact sum_nonneg fun v _ => bd_nonneg G X v
    rcases hY0.lt_or_eq with hpos | hzero
    · have hYc : Y ∈ cand := mem_filter.mpr ⟨mem_powerset.mpr (hY.trans hWU), hpos⟩
      have := hmin Y hYc
      rwa [le_div_iff₀ hpos] at this
    · rw [← hzero, mul_zero]; exact G.cross_nonneg _ _
  have hattain : G.cross W (X \ W) = ρ * e W := by
    rw [div_mul_cancel₀ _ heW.ne']
  refine ⟨W, ρ, hWU, hWX, ?_, ?_, hρ0, ?_, ?_⟩
  · rcases W.eq_empty_or_nonempty with rfl | hne
    · simp [e] at heW
    · exact hne
  · have := card_le_card hWU; have := hb.half; omega
  · -- `ρ ≤ h / e` and `f h ≤ 2 e`
    have hUe : 0 < e U := hb.pos
    have h1 : ρ ≤ G.cross U (X \ U) / e U := hmin U hU
    have h2 : G.cross U (X \ U) / e U * f ≤ 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hUe]
      have := hb.small
      linarith
    calc ρ * f ≤ G.cross U (X \ U) / e U * f := mul_le_mul_of_nonneg_right h1 hf
      _ ≤ 2 := h2
  · intro Z hZ
    have hsplitW : G.cross W (X \ W) = G.cross Z (X \ W) + G.cross (W \ Z) (X \ W) := by
      rw [← cross_union_left G _ _ _ disjoint_sdiff, union_sdiff_of_subset hZ]
    have hsplitY : G.cross (W \ Z) (X \ (W \ Z)) =
        G.cross (W \ Z) (X \ W) + G.cross (W \ Z) Z := by
      have hdisj : Disjoint (X \ W) Z := by
        rw [disjoint_left]; intro v hv hvZ; exact (mem_sdiff.mp hv).2 (hZ hvZ)
      rw [← cross_union_right G _ _ _ hdisj]
      congr 1
      ext v
      simp only [mem_sdiff, mem_union]
      constructor
      · rintro ⟨hvX, hv⟩
        by_cases hvZ : v ∈ Z
        · exact Or.inr hvZ
        · exact Or.inl ⟨hvX, fun hvW => hv ⟨hvW, hvZ⟩⟩
      · rintro (⟨hvX, hvW⟩ | hvZ)
        · exact ⟨hvX, fun h => hvW h.1⟩
        · exact ⟨hWX (hZ hvZ), fun h => h.2 hvZ⟩
    have hkeyY := hkey (W \ Z) sdiff_subset
    have heWZ : e W = e Z + e (W \ Z) := by
      simp only [e]
      rw [← sum_union disjoint_sdiff, union_sdiff_of_subset hZ]
    rw [cross_comm G (W \ Z) Z] at hsplitY
    have : G.cross Z (X \ W) = ρ * e Z + ρ * e (W \ Z) - G.cross (W \ Z) (X \ W) := by
      have := hattain; rw [heWZ] at this; linarith
    rw [this]
    linarith

end RackeShah
end Hierarchy
end CutQueryComplexity
