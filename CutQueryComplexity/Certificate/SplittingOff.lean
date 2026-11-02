import CutQueryComplexity.Certificate.MaxFlow

/-! # Fractional splitting off to a terminal set

A shore `S` separates `U` when both `S` and its complement meet `U`. Suppose every
`U`-separating cut of `G` has value at least `λ`.

* `exists_splitOff`: there is a weighted graph `J` with no weight at vertices outside
  `U`, with `c_J(S) ≤ c_G(S)` for every shore, and with every `U`-separating cut of
  `J` still at least `λ`.

This is the global (Lovász-type) splitting theorem for terminal connectivity, in a
fractional form that suffices for Lemma 8. Instead of iterating integral splittings,
we minimize the total weight at non-terminals over the compact set of graphs below
`G` that keep `U`-connectivity `λ`. At a minimizer with weight left at a
non-terminal `x`, neither deleting a little of an edge `xu` nor splitting a little of
a pair `xu, xv` is admissible, so tight `U`-separating sets block both. Lovász's
uncrossing argument (`no_blocking_config`) shows that this is impossible.
-/

namespace CutQueryComplexity
namespace Certificate

open WeightedGraph Filter Topology

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `S` separates the terminal set `U`. -/
def Separates (U S : Finset V) : Prop := (S ∩ U).Nonempty ∧ ¬ U ⊆ S

theorem Separates.compl {U S : Finset V} (h : Separates U S) : Separates U Sᶜ := by
  obtain ⟨⟨b, hb⟩, hU⟩ := h
  refine ⟨?_, fun hsub => ?_⟩
  · obtain ⟨a, haU, haS⟩ := Finset.not_subset.mp hU
    exact ⟨a, Finset.mem_inter.mpr ⟨Finset.mem_compl.mpr haS, haU⟩⟩
  · rw [Finset.mem_inter] at hb
    exact Finset.mem_compl.mp (hsub hb.2) hb.1

/-! ### Cut identities with slack -/

/-- Submodularity of the cut function, with its exact slack. -/
theorem cut_submodular_eq (G : WeightedGraph V) (A B : Finset V) :
    G.cut (A ∪ B) + G.cut (A ∩ B) + 2 * G.cross (A \ B) (B \ A) = G.cut A + G.cut B := by
  have h : G.cut (A ∪ B) + G.cut (A ∩ B) + G.cross (A \ B) (B \ A) + G.cross (B \ A) (A \ B) =
      G.cut A + G.cut B := by
    simp only [cut_eq_sum_ite, cross_eq_sum_ite, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    by_cases ha : p ∈ A <;> by_cases hb : p ∈ B <;> by_cases hc : q ∈ A <;>
      by_cases hd : q ∈ B <;> simp [ha, hb, hc, hd]
  rw [G.cross_comm (B \ A)] at h
  linarith

/-- Posimodularity of the cut function, with its exact slack. -/
theorem cut_posimodular_eq (G : WeightedGraph V) (X Y : Finset V) :
    G.cut (X \ Y) + G.cut (Y \ X) + 2 * G.cross (X ∩ Y) (X ∪ Y)ᶜ = G.cut X + G.cut Y := by
  have h := cut_submodular_eq G X Yᶜ
  have e1 : X ∪ Yᶜ = (Y \ X)ᶜ := by ext; simp; tauto
  have e2 : X ∩ Yᶜ = X \ Y := by ext; simp
  have e3 : X \ Yᶜ = X ∩ Y := by ext; simp
  have e4 : Yᶜ \ X = (X ∪ Y)ᶜ := by ext; simp; tauto
  rw [e1, e2, e3, e4, cut_compl, cut_compl] at h
  linarith

/-- Adding a vertex `x ∉ X` to a shore. -/
theorem cut_insert_eq (G : WeightedGraph V) {x : V} {X : Finset V} (hx : x ∉ X) :
    G.cut (insert x X) = G.cut X + G.degree x - 2 * G.cross {x} X := by
  rw [G.cross_eq_three_cuts (Finset.disjoint_singleton_left.mpr hx), cut_singleton,
    ← Finset.insert_eq]
  ring

theorem degree_eq_cross (G : WeightedGraph V) (x : V) (X : Finset V) :
    G.degree x = G.cross {x} X + G.cross {x} Xᶜ := by
  simp only [cross, Finset.sum_singleton, degree]
  exact (Finset.sum_add_sum_compl X _).symm

omit [Fintype V] [DecidableEq V] in
theorem w_le_cross (G : WeightedGraph V) {x u : V} {X : Finset V} (hu : u ∈ X) :
    G.w x u ≤ G.cross {x} X := by
  simp only [cross, Finset.sum_singleton]
  exact Finset.single_le_sum (fun v _ => G.nonneg x v) hu

/-! ### Lovász's uncrossing argument -/

/-- At a vertex `x ∉ U` of positive degree, tight `U`-separating sets cannot block every
deletion `xu` and every splitting of a pair `xu, xv`. -/
theorem no_blocking_config (H : WeightedGraph V) (U : Finset V) (lam : ℝ) {x : V}
    (hxU : x ∉ U) (hconn : ∀ S, Separates U S → lam ≤ H.cut S) (hdeg : ∃ y, 0 < H.w x y)
    (T1 : ∀ u, 0 < H.w x u → ∃ X, Separates U X ∧ x ∉ X ∧ u ∈ X ∧ H.cut X ≤ lam)
    (T2 : ∀ u v, 0 < H.w x u → 0 < H.w x v → u ≠ v →
      ∃ X, Separates U X ∧ x ∉ X ∧ u ∈ X ∧ v ∈ X ∧ H.cut X ≤ lam) : False := by
  classical
  set F := Finset.univ.filter fun X : Finset V =>
    Separates U X ∧ x ∉ X ∧ H.cut X ≤ lam ∧ ∃ u ∈ X, 0 < H.w x u
  obtain ⟨y, hy⟩ := hdeg
  obtain ⟨X₀, hX₀, hxX₀, hyX₀, hcX₀⟩ := T1 y hy
  have hFne : F.Nonempty := ⟨X₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hX₀, hxX₀, hcX₀,
    y, hyX₀, hy⟩⟩
  obtain ⟨X, hXF, hXmax⟩ := Finset.exists_max_image F Finset.card hFne
  obtain ⟨-, hXsep, hxX, hXcut, u, huX, hu⟩ := Finset.mem_filter.mp hXF
  -- At most half of the degree of `x` goes into `X`.
  have hins : Separates U (insert x X) := by
    refine ⟨hXsep.1.mono (Finset.inter_subset_inter (Finset.subset_insert _ _) le_rfl),
      fun hsub => hXsep.2 fun a ha => ?_⟩
    rcases Finset.mem_insert.mp (hsub ha) with h | h
    · exact absurd (h ▸ ha) hxU
    · exact h
  have hhalf : 2 * H.cross {x} X ≤ H.degree x := by
    have := hconn _ hins
    rw [cut_insert_eq H hxX] at this
    linarith
  -- So some neighbor `v` lies outside `X`.
  have hcrossX : 0 < H.cross {x} X := lt_of_lt_of_le hu (w_le_cross H huX)
  have hout : 0 < H.cross {x} Xᶜ := by
    have := degree_eq_cross H x X; linarith
  obtain ⟨v, hvX, hv⟩ : ∃ v ∈ Xᶜ, 0 < H.w x v := by
    by_contra hall
    push Not at hall
    have : H.cross {x} Xᶜ ≤ 0 := by
      simp only [cross, Finset.sum_singleton]
      exact Finset.sum_nonpos hall
    linarith
  have hvX' : v ∉ X := Finset.mem_compl.mp hvX
  have huv : u ≠ v := fun h => hvX' (h ▸ huX)
  obtain ⟨Y, hYsep, hxY, huY, hvY, hYcut⟩ := T2 u v hu hv huv
  have hXeq : H.cut X = lam := le_antisymm hXcut (hconn X hXsep)
  have hYeq : H.cut Y = lam := le_antisymm hYcut (hconn Y hYsep)
  by_cases hcase : Separates U (X ∩ Y) ∧ Separates U (X ∪ Y)
  · -- The union is a larger tight set containing a neighbor.
    have h1 := cut_submodular_eq H X Y
    have h2 := hconn _ hcase.1
    have h3 := H.cross_nonneg (X \ Y) (Y \ X)
    have hU : H.cut (X ∪ Y) ≤ lam := by linarith
    have hmem : X ∪ Y ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcase.2,
      by simp [hxX, hxY], hU, u, Finset.mem_union_left _ huX, hu⟩
    have hlt : X.card < (X ∪ Y).card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left,
        fun h => hvX' (h ▸ Finset.mem_union_right _ hvY)⟩)
    exact absurd (hXmax _ hmem) (not_le.mpr hlt)
  · -- Both differences separate `U`; posimodularity forces `w(x, X ∩ Y) = 0`.
    obtain ⟨⟨a, ha⟩, hXU⟩ := hXsep
    obtain ⟨⟨b, hb⟩, hYU⟩ := hYsep
    rw [Finset.mem_inter] at ha hb
    have hdiff : Separates U (X \ Y) ∧ Separates U (Y \ X) := by
      rcases not_and_or.mp hcase with hI | hUn
      · -- `X ∩ Y` meets no terminal.
        have hIU : ∀ c, c ∈ U → c ∈ X → c ∉ Y := by
          intro c hcU hcX hcY
          by_cases hall : U ⊆ X ∩ Y
          · exact hXU (hall.trans Finset.inter_subset_left)
          · exact hI ⟨⟨c, by simp [hcU, hcX, hcY]⟩, hall⟩
        have hbX : b ∉ X := fun h => hIU b hb.2 h hb.1
        refine ⟨⟨⟨a, by simp [ha.1, ha.2, hIU a ha.2 ha.1]⟩, fun h => hXU (h.trans
          Finset.sdiff_subset)⟩, ⟨⟨b, by simp [hb.1, hb.2, hbX]⟩,
          fun h => hYU (h.trans Finset.sdiff_subset)⟩⟩
      · -- `X ∪ Y` contains every terminal.
        have hall : U ⊆ X ∪ Y := by
          by_contra hn
          exact hUn ⟨⟨a, by simp [ha.1, ha.2]⟩, hn⟩
        obtain ⟨c, hcU, hcY⟩ := Finset.not_subset.mp hYU
        obtain ⟨d, hdU, hdX⟩ := Finset.not_subset.mp hXU
        have hcX : c ∈ X := by
          rcases Finset.mem_union.mp (hall hcU) with h | h
          · exact h
          · exact absurd h hcY
        have hdY : d ∈ Y := by
          rcases Finset.mem_union.mp (hall hdU) with h | h
          · exact absurd h hdX
          · exact h
        refine ⟨⟨⟨c, by simp [hcU, hcX, hcY]⟩, fun h => ?_⟩, ⟨⟨d, by simp [hdU, hdX, hdY]⟩,
          fun h => ?_⟩⟩
        · exact (Finset.mem_sdiff.mp (h hb.2)).2 hb.1
        · exact (Finset.mem_sdiff.mp (h ha.2)).2 ha.1
    have h1 := cut_posimodular_eq H X Y
    have h2 := hconn _ hdiff.1
    have h3 := hconn _ hdiff.2
    have h4 : H.w u x ≤ H.cross (X ∩ Y) (X ∪ Y)ᶜ := by
      simp only [cross]
      refine (Finset.single_le_sum (f := fun p => ∑ q ∈ (X ∪ Y)ᶜ, H.w p q)
        (fun p _ => Finset.sum_nonneg fun q _ => H.nonneg p q)
        (Finset.mem_inter.mpr ⟨huX, huY⟩)).trans' ?_
      exact Finset.single_le_sum (fun q _ => H.nonneg u q) (by simp [hxX, hxY])
    rw [H.symm] at h4
    linarith

/-! ### Graphs as matrices -/

/-- Cut value of a raw weight matrix. -/
def cutW (w : V → V → ℝ) (S : Finset V) : ℝ := ∑ u ∈ S, ∑ v ∈ Sᶜ, w u v

/-- Total weight at non-terminals. -/
def outMass (U : Finset V) (w : V → V → ℝ) : ℝ := ∑ z ∈ Uᶜ, ∑ y, w z y

theorem cutW_add_smul (w D : V → V → ℝ) (ε : ℝ) (S : Finset V) :
    cutW (fun p q => w p q + ε * D p q) S = cutW w S + ε * cutW D S := by
  simp [cutW, Finset.sum_add_distrib, Finset.mul_sum]

theorem outMass_add_smul (U : Finset V) (w D : V → V → ℝ) (ε : ℝ) :
    outMass U (fun p q => w p q + ε * D p q) = outMass U w + ε * outMass U D := by
  simp [outMass, Finset.sum_add_distrib, Finset.mul_sum]

/-- The unit undirected pair `{a, b}` as a matrix. -/
def symM (a b : V) : V → V → ℝ := fun p q =>
  (if p = a ∧ q = b then 1 else 0) + (if p = b ∧ q = a then 1 else 0)

/-- Indicator that `S` separates `a` from `b`. -/
def sepI (a b : V) (S : Finset V) : ℝ :=
  (if a ∈ S ∧ b ∉ S then 1 else 0) + (if b ∈ S ∧ a ∉ S then 1 else 0)

theorem cutW_symM (a b : V) (S : Finset V) : cutW (symM a b) S = sepI a b S := by
  simp only [cutW, symM, sepI, Finset.sum_add_distrib, ite_and]
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> simp [ha, hb, Finset.sum_ite_eq']

theorem outMass_symM (U : Finset V) {a b : V} :
    outMass U (symM a b) = (if a ∉ U then 1 else 0) + (if b ∉ U then 1 else 0) := by
  simp only [outMass, symM, Finset.sum_add_distrib, ite_and]
  by_cases ha : a ∈ U <;> by_cases hb : b ∈ U <;> simp [ha, hb, Finset.sum_ite_eq']

omit [Fintype V] in
theorem symM_symm (a b p q : V) : symM a b p q = symM a b q p := by
  unfold symM
  rw [add_comm]
  congr 1 <;> simp only [and_comm]

omit [Fintype V] in
theorem symM_nonneg (a b p q : V) : 0 ≤ symM a b p q := by
  simp only [symM]; split_ifs <;> norm_num

omit [Fintype V] in
theorem symM_pos {a b p q : V} (h : 0 < symM a b p q) :
    (p = a ∧ q = b) ∨ (p = b ∧ q = a) := by
  simp only [symM] at h
  by_contra hn
  push Not at hn
  simp only [ite_eq_right_iff.mpr (fun h' => absurd h' (not_and.mpr hn.1)),
    ite_eq_right_iff.mpr (fun h' => absurd h' (not_and.mpr hn.2)), add_zero] at h
  exact lt_irrefl _ h

omit [Fintype V] in
theorem symM_diag {a b : V} (hab : a ≠ b) (p : V) : symM a b p p = 0 := by
  simp only [symM]
  have h1 : ¬ (p = a ∧ p = b) := fun h => hab (h.1 ▸ h.2)
  have h2 : ¬ (p = b ∧ p = a) := fun h => hab (h.2 ▸ h.1)
  simp [h1, h2]

/-! ### The compact set of admissible reductions -/

/-- Graphs below `G` on every cut that keep every `U`-separating cut at least `lam`. -/
def Admissible (G : WeightedGraph V) (U : Finset V) (lam : ℝ) : Set (V → V → ℝ) :=
  {w | (∀ u v, w u v = w v u) ∧ (∀ u v, 0 ≤ w u v) ∧ (∀ v, w v v = 0) ∧
    (∀ S, cutW w S ≤ G.cut S) ∧ ∀ S, Separates U S → lam ≤ cutW w S}

theorem continuous_cutW (S : Finset V) : Continuous fun w : V → V → ℝ => cutW w S := by
  unfold cutW; fun_prop

theorem continuous_outMass (U : Finset V) : Continuous fun w : V → V → ℝ => outMass U w := by
  unfold outMass; fun_prop

theorem isCompact_admissible (G : WeightedGraph V) (U : Finset V) (lam : ℝ) :
    IsCompact (Admissible G U lam) := by
  have hbox : IsCompact (Set.univ.pi fun u : V => Set.univ.pi fun _ : V =>
      Set.Icc (0 : ℝ) (G.cut {u})) :=
    isCompact_univ_pi fun u => isCompact_univ_pi fun _ => isCompact_Icc
  refine hbox.of_isClosed_subset ?_ ?_
  · have hev : ∀ u v : V, Continuous fun f : V → V → ℝ => f u v := fun u v => by fun_prop
    simp only [Admissible, Set.ofPred_and, Set.ofPred_forall]
    refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_)))
    · exact isClosed_iInter fun u => isClosed_iInter fun v => isClosed_eq (hev u v) (hev v u)
    · exact isClosed_iInter fun u => isClosed_iInter fun v =>
        isClosed_le continuous_const (hev u v)
    · exact isClosed_iInter fun v => isClosed_eq (hev v v) continuous_const
    · exact isClosed_iInter fun S => isClosed_le (continuous_cutW S) continuous_const
    · exact isClosed_iInter fun S => isClosed_iInter fun _ =>
        isClosed_le continuous_const (continuous_cutW S)
  · intro w hw
    obtain ⟨-, hnn, hdiag, hle, -⟩ := hw
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies]
    intro u v
    refine ⟨hnn u v, ?_⟩
    by_cases huv : v = u
    · rw [huv, hdiag]; exact G.cut_nonneg _
    · refine le_trans ?_ (hle {u})
      simp only [cutW, Finset.sum_singleton]
      exact Finset.single_le_sum (fun q _ => hnn u q) (by simpa using huv)

/-- At a minimizer of `outMass`, a reducing direction is blocked by a tight set. -/
theorem exists_tight_of_isMinOn {G : WeightedGraph V} {U : Finset V} {lam : ℝ}
    {w : V → V → ℝ} (hw : w ∈ Admissible G U lam)
    (hmin : IsMinOn (outMass U) (Admissible G U lam) w) (D : V → V → ℝ)
    (hDs : ∀ p q, D p q = D q p) (hDd : ∀ p, D p p = 0) (hneg : ∀ p q, D p q < 0 → 0 < w p q)
    (hcut : ∀ S, cutW D S ≤ 0) (hΦ : outMass U D < 0) :
    ∃ S, Separates U S ∧ cutW D S < 0 ∧ cutW w S ≤ lam := by
  by_contra hno
  push Not at hno
  obtain ⟨hsym, hnn, hdiag, hle, hconn⟩ := hw
  have hε : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have hnn' : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ p q, 0 ≤ w p q + ε * D p q := by
    rw [eventually_all]; intro p; rw [eventually_all]; intro q
    by_cases hD : D p q < 0
    · have := eventually_add_mul_lt (a := -w p q) (b := 0) (by linarith [hneg p q hD]) (-D p q)
      filter_upwards [this] with ε h; linarith
    · filter_upwards [hε] with ε h
      nlinarith [hnn p q, not_lt.mp hD]
  have hconn' : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ S, Separates U S →
      lam ≤ cutW w S + ε * cutW D S := by
    rw [eventually_all]; intro S
    by_cases hS : Separates U S
    · by_cases hD : cutW D S < 0
      · have := eventually_add_mul_lt (a := lam - cutW w S) (b := 0)
          (by linarith [hno S hS hD]) (-cutW D S)
        filter_upwards [this] with ε h _; linarith
      · filter_upwards [hε] with ε h _
        have := hcut S
        have h0 : cutW D S = 0 := le_antisymm this (not_lt.mp hD)
        rw [h0, mul_zero, add_zero]; exact hconn S hS
    · filter_upwards with ε h; exact absurd h hS
  obtain ⟨ε, hεpos, hεnn, hεconn⟩ := (hε.and (hnn'.and hconn')).exists
  have hmem : (fun p q => w p q + ε * D p q) ∈ Admissible G U lam := by
    refine ⟨fun u v => show w u v + ε * D u v = w v u + ε * D v u by rw [hsym u v, hDs u v],
      hεnn, fun v => show w v v + ε * D v v = 0 by rw [hdiag, hDd]; ring,
      fun S => ?_, fun S hS => ?_⟩
    · rw [cutW_add_smul]
      have := mul_nonpos_of_nonneg_of_nonpos hεpos.le (hcut S)
      linarith [hle S]
    · rw [cutW_add_smul]; exact hεconn S hS
  have := hmin hmem
  simp only [Set.mem_ofPred_eq, outMass_add_smul] at this
  nlinarith

/-- Splitting off: a graph supported on `U`, below `G` on every cut, keeping
`U`-connectivity `lam`. -/
theorem exists_splitOff (G : WeightedGraph V) (U : Finset V) (lam : ℝ)
    (hconn : ∀ S, Separates U S → lam ≤ G.cut S) :
    ∃ J : WeightedGraph V, (∀ x y, x ∉ U → J.w x y = 0) ∧ (∀ S, J.cut S ≤ G.cut S) ∧
      ∀ S, Separates U S → lam ≤ J.cut S := by
  have hG : G.w ∈ Admissible G U lam :=
    ⟨G.symm, G.nonneg, G.diag, fun S => le_rfl, hconn⟩
  obtain ⟨w, hw, hmin⟩ := (isCompact_admissible G U lam).exists_isMinOn ⟨_, hG⟩
    (continuous_outMass U).continuousOn
  have hw' := hw
  obtain ⟨hsym, hnn, hdiag, hle, hconnw⟩ := hw'
  set H : WeightedGraph V := ⟨w, hsym, hnn, hdiag⟩
  have hHcut : ∀ S, H.cut S = cutW w S := fun S => rfl
  refine ⟨H, fun x y hx => ?_, hle, hconnw⟩
  by_contra hxy
  have hpos : 0 < H.w x y := lt_of_le_of_ne (hnn x y) (Ne.symm hxy)
  have hxU := hx
  have hconnH : ∀ S, Separates U S → lam ≤ H.cut S := hconnw
  -- Normalize a set with `x` on one side to the side avoiding `x`.
  have norm : ∀ S, Separates U S → H.cut S ≤ lam → ∀ P : Finset V → Prop,
      (x ∉ S → P S) → (x ∈ S → P Sᶜ) →
      ∃ X, Separates U X ∧ x ∉ X ∧ H.cut X ≤ lam ∧ (P X) := by
    intro S hS hc P h1 h2
    by_cases hxS : x ∈ S
    · exact ⟨Sᶜ, hS.compl, by simpa using hxS, by rwa [cut_compl], h2 hxS⟩
    · exact ⟨S, hS, hxS, hc, h1 hxS⟩
  apply no_blocking_config H U lam hxU hconnH ⟨y, hpos⟩
  · -- deletions
    intro u hu
    have hux : u ≠ x := fun h => by rw [h] at hu; simp [H, hdiag] at hu
    obtain ⟨S, hS, hD, hc⟩ := exists_tight_of_isMinOn hw hmin (fun p q => -symM x u p q)
      (fun p q => by rw [symM_symm]) (fun p => by rw [symM_diag (Ne.symm hux)]; simp)
      (fun p q h => by
        rcases symM_pos (a := x) (b := u) (by linarith) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hu
        · rw [hsym]; exact hu)
      (fun S => by
        have : cutW (fun p q => -symM x u p q) S = -cutW (symM x u) S := by
          simp [cutW]
        rw [this, cutW_symM, sepI]; split_ifs <;> norm_num)
      (by
        have : outMass U (fun p q => -symM x u p q) = -outMass U (symM x u) := by
          simp [outMass]
        rw [this, outMass_symM]; simp [hxU]; split_ifs <;> norm_num)
    have hsep : (x ∈ S ∧ u ∉ S) ∨ (u ∈ S ∧ x ∉ S) := by
      have : cutW (fun p q => -symM x u p q) S = -cutW (symM x u) S := by simp [cutW]
      rw [this, cutW_symM, sepI] at hD
      by_contra hn
      push Not at hn
      by_cases h1 : x ∈ S <;> by_cases h2 : u ∈ S <;> simp_all
    obtain ⟨X, hX, hxX, hcX, huX⟩ := norm S hS hc (fun X => u ∈ X)
      (fun hxS => by tauto) (fun hxS => by simp; tauto)
    exact ⟨X, hX, hxX, huX, hcX⟩
  · -- splittings
    intro u v hu hv huv
    have hux : u ≠ x := fun h => by rw [h] at hu; simp [H, hdiag] at hu
    have hvx : v ≠ x := fun h => by rw [h] at hv; simp [H, hdiag] at hv
    set D : V → V → ℝ := fun p q => -symM x u p q - symM x v p q + symM u v p q
    have hcutD : ∀ S, cutW D S = -sepI x u S - sepI x v S + sepI u v S := by
      intro S
      have : cutW D S = -cutW (symM x u) S - cutW (symM x v) S + cutW (symM u v) S := by
        simp [D, cutW, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [this, cutW_symM, cutW_symM, cutW_symM]
    obtain ⟨S, hS, hD, hc⟩ := exists_tight_of_isMinOn hw hmin D
      (fun p q => by simp only [D]; rw [symM_symm x u, symM_symm x v, symM_symm u v])
      (fun p => by simp only [D]; rw [symM_diag (Ne.symm hux), symM_diag (Ne.symm hvx),
        symM_diag huv]; ring)
      (fun p q h => by
        simp only [D] at h
        have h3 := symM_nonneg u v p q
        by_cases h1 : 0 < symM x u p q
        · rcases symM_pos h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hu
          · rw [hsym]; exact hu
        · have h2 : 0 < symM x v p q := by linarith [symM_nonneg x u p q]
          rcases symM_pos h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hv
          · rw [hsym]; exact hv)
      (fun S => by
        rw [hcutD, sepI, sepI, sepI]
        by_cases h1 : x ∈ S <;> by_cases h2 : u ∈ S <;> by_cases h3 : v ∈ S <;>
          simp [h1, h2, h3])
      (by
        have : outMass U D = -outMass U (symM x u) - outMass U (symM x v) +
            outMass U (symM u v) := by
          simp [D, outMass, Finset.sum_add_distrib, Finset.sum_sub_distrib]
        rw [this, outMass_symM, outMass_symM, outMass_symM]
        simp only [hxU, not_false_eq_true, ite_true]
        split_ifs <;> norm_num)
    have hsep : (x ∈ S ∧ u ∉ S ∧ v ∉ S) ∨ (u ∈ S ∧ v ∈ S ∧ x ∉ S) := by
      rw [hcutD, sepI, sepI, sepI] at hD
      by_cases h1 : x ∈ S <;> by_cases h2 : u ∈ S <;> by_cases h3 : v ∈ S <;>
        simp [h1, h2, h3] at hD ⊢
    obtain ⟨X, hX, hxX, hcX, huX, hvX⟩ := norm S hS hc (fun X => u ∈ X ∧ v ∈ X)
      (fun hxS => by tauto) (fun hxS => by simp; tauto)
    exact ⟨X, hX, hxX, huX, hvX, hcX⟩

end Certificate
end CutQueryComplexity
