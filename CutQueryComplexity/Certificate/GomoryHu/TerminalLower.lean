import CutQueryComplexity.Certificate.Main
import Mathlib.Tactic

set_option autoImplicit false

/-! # Certificates for arbitrary terminal-connectivity lower bounds

The threshold `a` need only lower-bound cuts separating the specified terminals.
Cuts isolating nonterminals can have value zero. The construction generalizes
actual splitting, halving flows, isolating certificates and finite thinning;
no certificate oracle or global-mincut premise is assumed.
-/

namespace CutQueryComplexity.Certificate.GomoryHu

open WeightedGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A cut separating a subset of the terminals also separates the original set. -/
theorem separates_mono {R U S : Finset V} (hRU : R ⊆ U)
    (hS : Separates R S) : Separates U S := by
  refine ⟨hS.1.mono (fun v hv => ?_), fun h => hS.2 (hRU.trans h)⟩
  exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv).1, hRU (Finset.mem_inter.mp hv).2⟩

/-- The cut condition of Lemma 8 in `G`, via splitting off and a maximum cut. -/
theorem exists_halving_cutCondition_of_terminal_lower (G : WeightedGraph V) (U : Finset V) (hU : 2 ≤ U.card)
    (lam : ℝ) (hlam : 0 < lam)
    (hconn : ∀ S, Separates U S → lam ≤ G.cut S) :
    ∃ R ⊆ U, R.Nonempty ∧ R ≠ U ∧ 2 * R.card ≤ U.card ∧
      ∀ S, Disjoint S R → lam / 2 * (S ∩ U).card ≤ G.cut S := by
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
theorem exists_halving_of_terminal_lower (G : WeightedGraph V) (U : Finset V) (hU : 2 ≤ U.card)
    (lam : ℝ) (hlam : 0 < lam)
    (hconn : ∀ S, Separates U S → lam ≤ G.cut S) :
    ∃ R ⊂ U, R.Nonempty ∧ 2 * R.card ≤ U.card ∧ ∃ f : V → V → ℝ, Feasible G f ∧
      (∀ u ∈ U \ R, netOut f u = lam / 2) ∧ (∀ v ∉ U, netOut f v = 0) ∧
      ∀ v ∈ R, netOut f v ≤ 0 := by
  obtain ⟨R, hRU, hRne, hRneU, hRcard, hcond⟩ := exists_halving_cutCondition_of_terminal_lower G U hU lam hlam hconn
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
theorem exists_halvingCert_of_terminal_lower (G : WeightedGraph V) (U : Finset V) (hU : 2 ≤ U.card)
    (lam : ℝ) (hlam : 0 < lam)
    (hconn : ∀ S, Separates U S → lam ≤ G.cut S) :
    ∃ R ⊂ U, R.Nonempty ∧ 2 * R.card ≤ U.card ∧ ∃ Q : Finset (Finset V),
      Q.card ≤ 8 * Fintype.card V ∧ ∀ G' : WeightedGraph V, Consistent G G' Q →
        ∀ S, Disjoint S R → lam / 2 * (S ∩ U).card ≤ G'.cut S := by
  obtain ⟨R, hRU, hRne, hRcard, f, hf, hsrc, hout, -⟩ := exists_halving_of_terminal_lower G U hU lam hlam hconn
  obtain ⟨Q, hQ, hcert⟩ := exists_flowCert G Finset.univ hf
  refine ⟨R, hRU, hRne, hRcard, Q, by simpa using hQ, fun G' hG' S hSR => ?_⟩
  obtain ⟨f', hf', hnet'⟩ := hcert G' hG'
  have hsum : ∑ x ∈ S, netOut f' x = lam / 2 * (S ∩ U).card := by
    rw [Finset.sum_congr rfl fun x _ => hnet' x (Finset.mem_univ x)]
    rw [← Finset.sum_filter_add_sum_filter_not S (· ∈ U)]
    have h1 : ∑ x ∈ S.filter (· ∈ U), netOut f x = ∑ x ∈ S.filter (· ∈ U), lam / 2 :=
      Finset.sum_congr rfl fun x hx => by
        rw [Finset.mem_filter] at hx
        exact hsrc x (Finset.mem_sdiff.mpr ⟨hx.2, fun hR => Finset.disjoint_left.mp hSR hx.1 hR⟩)
    have h2 : ∑ x ∈ S.filter (· ∉ U), netOut f x = 0 :=
      Finset.sum_eq_zero fun x hx => hout x (Finset.mem_filter.mp hx).2
    rw [h1, h2, Finset.sum_const, nsmul_eq_mul, add_zero, Finset.filter_mem_eq_inter, mul_comm]
  have := sum_netOut_le_cut hf' S
  linarith

/-- Certified lower bound `λ` for all cuts separating `U`, by recursion on `|U|`. -/
private theorem terminal_lower_main (G : WeightedGraph V) {lam : ℝ} (hlam : 0 < lam) :
    ∀ U : Finset V, (∀ S, Separates U S → lam ≤ G.cut S) →
      ∃ Q : Finset (Finset V),
      Q.card ≤ 17 * Fintype.card V * (Nat.clog 2 (2 * U.card)) ^ 2 ∧
      ∀ G' : WeightedGraph V, Consistent G G' Q →
        ∀ S, Separates U S → lam ≤ G'.cut S := by
  set n := Fintype.card V
  intro U
  induction U using Finset.strongInduction with
  | H U ih =>
  intro hconn
  by_cases hU : U.card < 2
  · -- No shore separates at most one terminal.
    refine ⟨∅, by simp, fun G' _ S hS => ?_⟩
    obtain ⟨⟨a, ha⟩, hsub⟩ := hS
    rw [Finset.mem_inter] at ha
    exact absurd (fun b hb => by
      have := Finset.card_le_one.mp (by omega) b hb a ha.2
      exact this ▸ ha.1) hsub
  push Not at hU
  obtain ⟨Qi, hQi, hiso⟩ := exists_isoCert G U
  obtain ⟨R, hRU, hRne, hRcard, Qh, hQh, hhalf⟩ := exists_halvingCert_of_terminal_lower G U hU lam hlam hconn
  obtain ⟨QR, hQR, hrec⟩ := ih R hRU
    (fun S hS => hconn S (separates_mono hRU.subset hS))
  refine ⟨Qi ∪ Qh ∪ QR, ?_, fun G' hG' S hS => ?_⟩
  · -- counting
    have hK := clog_two_mul (m := U.card) (by omega)
    have hR1 : Nat.clog 2 (2 * R.card) ≤ Nat.clog 2 U.card := Nat.clog_mono_right 2 hRcard
    set K := Nat.clog 2 U.card
    have hsq : (Nat.clog 2 (2 * R.card)) ^ 2 ≤ K ^ 2 := Nat.pow_le_pow_left hR1 2
    have c1 := Finset.card_union_le (Qi ∪ Qh) QR
    have c2 := Finset.card_union_le Qi Qh
    have h3 : 17 * n * Nat.clog 2 (2 * R.card) ^ 2 ≤ 17 * n * K ^ 2 :=
      Nat.mul_le_mul_left _ hsq
    rw [hK]
    have hQi' : Qi.card ≤ 9 * n * (K + 1) := hQi
    have hQh' : Qh.card ≤ 8 * n := hQh
    have : 9 * n * (K + 1) + 8 * n + 17 * n * K ^ 2 ≤ 17 * n * (K + 1) ^ 2 := by
      nlinarith [Nat.zero_le n, Nat.zero_le K, Nat.zero_le (n * K)]
    omega
  · have hGi := hG'.mono (Q := Qi) (fun T hT => Finset.mem_union_left _
      (Finset.mem_union_left _ hT))
    have hGh := hG'.mono (Q := Qh) (fun T hT => Finset.mem_union_left _
      (Finset.mem_union_right _ hT))
    have hGR := hG'.mono (Q := QR) (fun T hT => Finset.mem_union_right _ hT)
    -- A side with one terminal, or with none of `R`, has cut at least `λ`.
    have key : ∀ T, Separates U T → ((T ∩ U).card = 1 ∨ Disjoint T R) →
        lam ≤ G'.cut T := by
      intro T hT hcase
      by_cases h1 : (T ∩ U).card = 1
      · obtain ⟨v, hv⟩ := Finset.card_eq_one.mp h1
        have hvU : v ∈ U := (Finset.mem_inter.mp (hv ▸ Finset.mem_singleton_self v)).2
        obtain ⟨S₀, hS₀, hS₀c, -⟩ := exists_isoMinimal G hvU
        have hS₀sep : Separates U S₀ := ⟨⟨v, by rw [hS₀]; exact Finset.mem_singleton_self v⟩,
          fun h => by
            have := Finset.card_le_card (Finset.subset_inter h (le_refl U))
            rw [hS₀, Finset.card_singleton] at this; omega⟩
        have h2 := isoValue_le G' hv
        rw [hiso G' hGi v hvU, ← hS₀c] at h2
        exact (hconn S₀ hS₀sep).trans h2
      · have hdisj : Disjoint T R := hcase.resolve_left h1
        have h2 : 2 ≤ (T ∩ U).card := by
          have := Finset.card_pos.mpr hT.1; omega
        have := hhalf G' hGh T hdisj
        have h3 : (2 : ℝ) ≤ ((T ∩ U).card : ℝ) := by exact_mod_cast h2
        nlinarith
    by_cases h1 : Disjoint S R
    · exact key S hS (Or.inr h1)
    by_cases h2 : Disjoint Sᶜ R
    · rw [← cut_compl]; exact key Sᶜ hS.compl (Or.inr h2)
    obtain ⟨a, haS, haR⟩ := Finset.not_disjoint_iff.mp h1
    obtain ⟨b, hbS, hbR⟩ := Finset.not_disjoint_iff.mp h2
    exact hrec G' hGR S ⟨⟨a, Finset.mem_inter.mpr ⟨haS, haR⟩⟩,
      fun h => Finset.mem_compl.mp hbS (h hbR)⟩

/-- An arbitrary positive terminal lower bound has one certificate before all
unrestricted competitors. The literal constant is inherited from the proved
halving/isolating recursion, not supplied as a hypothesis. -/
theorem exists_terminal_lower_certificate (G : WeightedGraph V) (R : Finset V)
    {a : ℝ} (ha : 0 < a) (hconn : ∀ S, Separates R S → a ≤ G.cut S) :
    ∃ Q : Finset (Finset V),
      Q.card ≤ 17 * Fintype.card V * (Nat.clog 2 (2 * R.card)) ^ 2 ∧
      ∀ H : WeightedGraph V, Consistent G H Q →
        ∀ S, Separates R S → a ≤ H.cut S :=
  terminal_lower_main G ha R hconn

end CutQueryComplexity.Certificate.GomoryHu

#print axioms CutQueryComplexity.Certificate.GomoryHu.exists_halving_cutCondition_of_terminal_lower
#print axioms CutQueryComplexity.Certificate.GomoryHu.exists_halving_of_terminal_lower
#print axioms CutQueryComplexity.Certificate.GomoryHu.exists_halvingCert_of_terminal_lower
#print axioms CutQueryComplexity.Certificate.GomoryHu.exists_terminal_lower_certificate
