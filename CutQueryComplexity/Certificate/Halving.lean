import CutQueryComplexity.Certificate.SplittingOff
import CutQueryComplexity.Certificate.FlowCert

/-! # A flow to half the terminals (Lemma 8)

Let `λ = mincutValue G > 0` and `U` a set of at least two vertices.

* `exists_halving`: there is a nonempty `R ⊂ U` with `2 |R| ≤ |U|` and a feasible
  flow with net outflow `λ/2` on `U \ R`, `0` outside `U`, and `≤ 0` on `R`.
* `exists_halvingCert`: consequently `8 n` shores certify, in every consistent `G'`,
  `c_{G'}(S) ≥ (λ/2) |S ∩ U|` for every shore `S` disjoint from `R`.

Splitting off every non-terminal (`exists_splitOff`) gives a graph `J` on `U` whose
cuts are below those of `G` and whose degrees are at least `λ`. The smaller side `R`
of a maximum cut of `J` receives at least half of every outside degree, so every shore
avoiding `R` satisfies the cut condition in `G`. Max-flow/min-cut with source
capacities `λ/2` (`exists_maxFlow`) turns this cut condition into the flow. Unlike
the paper, no rational approximation is needed: splitting off is fractional.
-/

namespace CutQueryComplexity
namespace Certificate

open WeightedGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A graph with no weight outside `U` sees only the terminal part of a shore. -/
theorem cut_inter_of_support (J : WeightedGraph V) (U : Finset V)
    (hJ : ∀ x y, x ∉ U → J.w x y = 0) (S : Finset V) : J.cut S = J.cut (S ∩ U) := by
  simp only [cut_eq_sum_ite]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  by_cases hp : p ∈ U
  · by_cases hq : q ∈ U
    · simp [hp, hq]
    · have : J.w p q = 0 := by rw [J.symm]; exact hJ q p hq
      simp [this]
  · simp [hJ p q hp]

omit [Fintype V] [DecidableEq V] in
theorem cross_mono (G : WeightedGraph V) {A A' B B' : Finset V} (hA : A ⊆ A') (hB : B ⊆ B') :
    G.cross A B ≤ G.cross A' B' := by
  unfold cross
  refine (Finset.sum_le_sum fun u _ => Finset.sum_le_sum_of_subset_of_nonneg hB
    fun v _ _ => G.nonneg u v).trans ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg hA fun u _ _ =>
    Finset.sum_nonneg fun v _ => G.nonneg u v

omit [Fintype V] [DecidableEq V] in
theorem cross_eq_sum_cross_singleton (G : WeightedGraph V) (A B : Finset V) :
    G.cross A B = ∑ u ∈ A, G.cross {u} B := by
  simp [cross]

omit [Fintype V] in
theorem separates_singleton {U : Finset V} (hU : 2 ≤ U.card) {u : V} (hu : u ∈ U) :
    Separates U {u} := by
  refine ⟨⟨u, by simp [hu]⟩, fun h => ?_⟩
  have := Finset.card_le_card h
  simp at this; omega

/-- The cut condition of Lemma 8 in `G`, via splitting off and a maximum cut. -/
theorem exists_halving_cutCondition (G : WeightedGraph V) (U : Finset V) (hU : 2 ≤ U.card)
    (hlam : 0 < mincutValue G) :
    ∃ R ⊆ U, R.Nonempty ∧ R ≠ U ∧ 2 * R.card ≤ U.card ∧
      ∀ S, Disjoint S R → mincutValue G / 2 * (S ∩ U).card ≤ G.cut S := by
  set lam := mincutValue G
  have hconn : ∀ S, Separates U S → lam ≤ G.cut S := by
    intro S hS
    refine mincutValue_le G ⟨hS.1.mono Finset.inter_subset_left, fun h => hS.2 ?_⟩
    rw [h]; exact Finset.subset_univ _
  obtain ⟨J, hJU, hJG, hJconn⟩ := exists_splitOff G U lam hconn
  have hJcut := cut_inter_of_support J U hJU
  -- A maximum cut of `J` among subsets of `U`.
  obtain ⟨R₀, hR₀, hR₀max⟩ := Finset.exists_max_image U.powerset J.cut
    ⟨∅, Finset.empty_mem_powerset U⟩
  rw [Finset.mem_powerset] at hR₀
  have hcompl : J.cut (U \ R₀) = J.cut R₀ := by
    rw [← cut_compl, hJcut, hJcut R₀]
    congr 1; ext x; simp only [Finset.mem_inter, Finset.mem_compl, Finset.mem_sdiff]
    constructor
    · rintro ⟨h, hx⟩; exact ⟨by tauto, hx⟩
    · rintro ⟨h, hx⟩; exact ⟨fun h' => h'.2 h, hx⟩
  -- Choose the smaller side; both are maximum cuts.
  obtain ⟨R, hRU, hRcard, hRmax⟩ : ∃ R ⊆ U, 2 * R.card ≤ U.card ∧
      ∀ T ⊆ U, J.cut T ≤ J.cut R := by
    by_cases hsmall : 2 * R₀.card ≤ U.card
    · exact ⟨R₀, hR₀, hsmall, fun T hT => hR₀max T (Finset.mem_powerset.mpr hT)⟩
    · refine ⟨U \ R₀, Finset.sdiff_subset, ?_, fun T hT => ?_⟩
      · rw [Finset.card_sdiff_of_subset hR₀]; omega
      · rw [hcompl]; exact hR₀max T (Finset.mem_powerset.mpr hT)
  obtain ⟨u₀, hu₀⟩ : U.Nonempty := Finset.card_pos.mp (by omega)
  have hdeg : ∀ u ∈ U, lam ≤ J.degree u := fun u hu => by
    rw [← cut_singleton]; exact hJconn _ (separates_singleton hU hu)
  have hRpos : lam ≤ J.cut R := (hdeg u₀ hu₀).trans (by
    rw [← cut_singleton]; exact hRmax _ (Finset.singleton_subset_iff.mpr hu₀))
  have hRne : R.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, cut_empty] at hRpos; linarith
  have hRneU : R ≠ U := by
    rintro rfl
    have : J.cut R = 0 := by
      have he : Rᶜ ∩ R = ∅ := by ext; simp
      rw [← cut_compl, hJcut, he, cut_empty]
    linarith
  -- Every outside terminal sends half its degree into `R`.
  have hhalf : ∀ u ∈ U, u ∉ R → lam / 2 ≤ J.cross {u} R := by
    intro u hu huR
    have h1 := hRmax (insert u R) (Finset.insert_subset hu hRU)
    rw [cut_insert_eq J huR] at h1
    have := hdeg u hu
    linarith
  refine ⟨R, hRU, hRne, hRneU, hRcard, fun S hSR => ?_⟩
  have h1 : J.cross (S ∩ U) R ≤ J.cut S := by
    rw [← cross_compl]
    exact cross_mono J Finset.inter_subset_left fun x hx => Finset.mem_compl.mpr fun hxS =>
      Finset.disjoint_left.mp hSR hxS hx
  have h2 : lam / 2 * (S ∩ U).card ≤ J.cross (S ∩ U) R := by
    rw [cross_eq_sum_cross_singleton, mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun u hu => ?_
    rw [Finset.mem_inter] at hu
    exact hhalf u hu.2 fun huR => Finset.disjoint_left.mp hSR hu.1 huR
  linarith [hJG S]

/-- Lemma 8: a flow sending `λ/2` from every terminal outside `R`. -/
theorem exists_halving (G : WeightedGraph V) (U : Finset V) (hU : 2 ≤ U.card)
    (hlam : 0 < mincutValue G) :
    ∃ R ⊂ U, R.Nonempty ∧ 2 * R.card ≤ U.card ∧ ∃ f : V → V → ℝ, Feasible G f ∧
      (∀ u ∈ U \ R, netOut f u = mincutValue G / 2) ∧ (∀ v ∉ U, netOut f v = 0) ∧
      ∀ v ∈ R, netOut f v ≤ 0 := by
  obtain ⟨R, hRU, hRne, hRneU, hRcard, hcond⟩ := exists_halving_cutCondition G U hU hlam
  set lam := mincutValue G
  have hdisj : Disjoint (U \ R) R := Finset.sdiff_disjoint
  obtain ⟨f, S₀, hf, hcons, hsrc, hsink, hS₀R, hval⟩ :=
    exists_maxFlow G (U \ R) R hdisj (fun _ => lam / 2) (fun _ => by linarith)
  refine ⟨R, Finset.ssubset_iff_subset_ne.mpr ⟨hRU, hRneU⟩, hRne, hRcard, f, hf, ?_,
    fun v hv => hcons v (fun h => hv (Finset.mem_sdiff.mp h).1) (fun h => hv (hRU h)),
    hsink⟩
  -- The value is at least `(λ/2) |U \ R|`, so every source is saturated.
  have hge : lam / 2 * (U \ R).card ≤ ∑ x ∈ U \ R, netOut f x := by
    rw [hval, Finset.sum_const, nsmul_eq_mul]
    have h1 := hcond S₀ hS₀R
    have h2 : ((U \ R) ∩ S₀).card ≤ (S₀ ∩ U).card :=
      Finset.card_le_card fun x hx => by
        simp only [Finset.mem_inter, Finset.mem_sdiff] at hx ⊢; exact ⟨hx.2, hx.1.1⟩
    have h3 := Finset.card_inter_add_card_sdiff (U \ R) S₀
    have hl : 0 ≤ lam / 2 := by linarith
    have h4 : (((U \ R) ∩ S₀).card : ℝ) + (((U \ R) \ S₀).card : ℝ) = ((U \ R).card : ℝ) := by
      exact_mod_cast h3
    have h5 : (((U \ R) ∩ S₀).card : ℝ) ≤ ((S₀ ∩ U).card : ℝ) := by exact_mod_cast h2
    nlinarith
  have hzero : ∑ x ∈ U \ R, (lam / 2 - netOut f x) = 0 := by
    refine le_antisymm ?_ (Finset.sum_nonneg fun x hx => by linarith [hsrc x hx])
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    linarith
  intro u hu
  have := (Finset.sum_eq_zero_iff_of_nonneg fun x hx => by linarith [hsrc x hx]).mp hzero u hu
  linarith

/-- Lemma 8, certificate form: `8 n` shores certify the halving inequalities. -/
theorem exists_halvingCert (G : WeightedGraph V) (U : Finset V) (hU : 2 ≤ U.card)
    (hlam : 0 < mincutValue G) :
    ∃ R ⊂ U, R.Nonempty ∧ 2 * R.card ≤ U.card ∧ ∃ Q : Finset (Finset V),
      Q.card ≤ 8 * Fintype.card V ∧ ∀ G' : WeightedGraph V, Consistent G G' Q →
        ∀ S, Disjoint S R → mincutValue G / 2 * (S ∩ U).card ≤ G'.cut S := by
  obtain ⟨R, hRU, hRne, hRcard, f, hf, hsrc, hout, -⟩ := exists_halving G U hU hlam
  obtain ⟨Q, hQ, hcert⟩ := exists_flowCert G Finset.univ hf
  refine ⟨R, hRU, hRne, hRcard, Q, by simpa using hQ, fun G' hG' S hSR => ?_⟩
  obtain ⟨f', hf', hnet'⟩ := hcert G' hG'
  have hsum : ∑ x ∈ S, netOut f' x = mincutValue G / 2 * (S ∩ U).card := by
    rw [Finset.sum_congr rfl fun x _ => hnet' x (Finset.mem_univ x)]
    rw [← Finset.sum_filter_add_sum_filter_not S (· ∈ U)]
    have h1 : ∑ x ∈ S.filter (· ∈ U), netOut f x = ∑ x ∈ S.filter (· ∈ U), mincutValue G / 2 :=
      Finset.sum_congr rfl fun x hx => by
        rw [Finset.mem_filter] at hx
        exact hsrc x (Finset.mem_sdiff.mpr ⟨hx.2, fun hR => Finset.disjoint_left.mp hSR hx.1 hR⟩)
    have h2 : ∑ x ∈ S.filter (· ∉ U), netOut f x = 0 :=
      Finset.sum_eq_zero fun x hx => hout x (Finset.mem_filter.mp hx).2
    rw [h1, h2, Finset.sum_const, nsmul_eq_mul, add_zero, Finset.filter_mem_eq_inter, mul_comm]
  have := sum_netOut_le_cut hf' S
  linarith

end Certificate
end CutQueryComplexity
