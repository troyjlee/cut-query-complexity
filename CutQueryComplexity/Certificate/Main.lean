import CutQueryComplexity.Certificate.Isolating
import CutQueryComplexity.Certificate.Halving

/-! # Near-linear minimum-cut certificates (Theorem 2)

* `exists_separationCert`: for `λ = mincutValue G > 0` and a terminal set `U`,
  at most `17 n ⌈log₂ (2|U|)⌉²` shores certify `c_{G'}(S) ≥ λ` for every shore `S`
  separating `U`, in every consistent graph `G'`.
* `exists_minCut_certificate`: every weighted graph on `n ≥ 2` vertices has a
  certificate of at most `18 n ⌈log₂ (2n)⌉²` shores containing a shore that is a
  minimum cut of every consistent graph.
* `exists_minCut_value_certificate`: the same queries certify the minimum-cut value.

The separation certificate is built by strong induction on `|U|`: certify all isolating
values for `U` (Lemma 7), choose `R` by Lemma 8 and certify its halving inequalities,
and recurse on `R`. A cut of `G'` separating `U` either has one terminal of `U` on a
side (isolating bound), or a side with at least two terminals of `U` and none of `R`
(halving bound), or it separates `R`.
-/

namespace CutQueryComplexity
namespace Certificate

open WeightedGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem clog_two_mul {m : ℕ} (hm : 1 ≤ m) : Nat.clog 2 (2 * m) = Nat.clog 2 m + 1 := by
  rw [Nat.clog_of_two_le (by norm_num) (by omega)]
  congr 2
  omega

/-- A separating shore of `G` has cut at least the global minimum. -/
theorem mincutValue_le_of_separates (G : WeightedGraph V) {U S : Finset V}
    (hS : Separates U S) : mincutValue G ≤ G.cut S := by
  refine mincutValue_le G ⟨hS.1.mono Finset.inter_subset_left, fun h => hS.2 ?_⟩
  rw [h]; exact Finset.subset_univ _

/-- Certified lower bound `λ` for all cuts separating `U`, by recursion on `|U|`. -/
theorem exists_separationCert (G : WeightedGraph V) (hlam : 0 < mincutValue G) :
    ∀ U : Finset V, ∃ Q : Finset (Finset V),
      Q.card ≤ 17 * Fintype.card V * (Nat.clog 2 (2 * U.card)) ^ 2 ∧
      ∀ G' : WeightedGraph V, Consistent G G' Q →
        ∀ S, Separates U S → mincutValue G ≤ G'.cut S := by
  set n := Fintype.card V
  set lam := mincutValue G
  intro U
  induction U using Finset.strongInduction with
  | H U ih =>
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
  obtain ⟨R, hRU, hRne, hRcard, Qh, hQh, hhalf⟩ := exists_halvingCert G U hU hlam
  obtain ⟨QR, hQR, hrec⟩ := ih R hRU
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
        exact (mincutValue_le_of_separates G hS₀sep).trans h2
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

/-- A minimum cut of every consistent graph, certified by `18 n ⌈log₂ (2n)⌉²` shores. -/
theorem exists_minCut_witnessCertificate (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V) :
    ∃ Q S, Q.card ≤ 18 * Fintype.card V * (Nat.clog 2 (2 * Fintype.card V)) ^ 2 ∧
      IsMinCutWitnessCertificate G Q S := by
  set n := Fintype.card V
  have hK : 1 ≤ Nat.clog 2 (2 * n) := Nat.clog_pos (by norm_num) (by omega)
  have hK2 : 1 ≤ (Nat.clog 2 (2 * n)) ^ 2 := Nat.one_le_pow _ _ hK
  have hnK : n ≤ n * (Nat.clog 2 (2 * n)) ^ 2 := Nat.le_mul_of_pos_right n hK2
  obtain ⟨S, hS⟩ := exists_isMinCut_of_two_le_card G hn
  have hSval : G.cut S = mincutValue G := by
    refine le_antisymm ?_ (mincutValue_le G hS.1)
    obtain ⟨T, hT, hTv⟩ := exists_isMinCut G ⟨S, (mem_properShores S).mpr hS.1⟩
    rw [← hTv]; exact hS.2 T hT.1
  rcases (mincutValue_nonneg G).eq_or_lt with h0 | hpos
  · -- A zero cut: one query suffices.
    refine ⟨{S}, S, ?_, Finset.mem_singleton_self S, fun G' hG' => ⟨hS.1, fun T _ => ?_⟩⟩
    · rw [Finset.card_singleton]; nlinarith
    · rw [hG' S (Finset.mem_singleton_self S), hSval, ← h0]; exact G'.cut_nonneg T
  · obtain ⟨Q, hQ, hcert⟩ := exists_separationCert G hpos Finset.univ
    rw [Finset.card_univ] at hQ
    refine ⟨insert S Q, S, ?_, Finset.mem_insert_self S Q, fun G' hG' => ⟨hS.1, fun T hT => ?_⟩⟩
    · refine (Finset.card_insert_le _ _).trans ?_
      nlinarith
    · have hT' : Separates Finset.univ T := ⟨by simpa using hT.1, fun h => hT.2
        (Finset.eq_univ_of_forall fun x => h (Finset.mem_univ x))⟩
      rw [hG' S (Finset.mem_insert_self S Q), hSval]
      exact hcert G' (hG'.mono (Finset.subset_insert S Q)) T hT'

/-- A witness certificate also certifies the minimum-cut value. -/
theorem IsMinCutWitnessCertificate.isMinCutCertificate {G : WeightedGraph V}
    {Q : Finset (Finset V)} {S : Finset V} (h : IsMinCutWitnessCertificate G Q S) :
    IsMinCutCertificate G Q := by
  have hval : ∀ H : WeightedGraph V, IsMinCut H S → mincutValue H = H.cut S := by
    intro H hH
    refine le_antisymm (mincutValue_le H hH.1) ?_
    obtain ⟨T, hT, hTv⟩ := exists_isMinCut H ⟨S, (mem_properShores S).mpr hH.1⟩
    rw [← hTv]; exact hH.2 T hT.1
  intro G' hG'
  rw [hval G' (h.2 G' hG'), hval G (h.2 G (fun _ _ => rfl)), hG' S h.1]

/-- Theorem 2: near-linear minimum-cut certificates. -/
theorem exists_minCut_certificate :
    ∃ C : ℕ, ∀ n (G : WeightedGraph (Fin n)), 2 ≤ n →
      ∃ Q S, Q.card ≤ C * n * (Nat.clog 2 (2 * n)) ^ 2 ∧ IsMinCutWitnessCertificate G Q S := by
  refine ⟨18, fun n G hn => ?_⟩
  have := exists_minCut_witnessCertificate G (by simpa using hn)
  simpa using this

/-- Theorem 2, value form. -/
theorem exists_minCut_value_certificate :
    ∃ C : ℕ, ∀ n (G : WeightedGraph (Fin n)), 2 ≤ n →
      ∃ Q, Q.card ≤ C * n * (Nat.clog 2 (2 * n)) ^ 2 ∧ IsMinCutCertificate G Q := by
  obtain ⟨C, hC⟩ := exists_minCut_certificate
  exact ⟨C, fun n G hn => by
    obtain ⟨Q, S, hQ, hS⟩ := hC n G hn
    exact ⟨Q, hQ, hS.isMinCutCertificate⟩⟩

/-! ## Certificate complexity

`cert(G)` of the paper: the least number of shores whose answers force the minimum-cut
value in every nonnegative weighted competitor on the same vertex set. The full family of
shores is a certificate, so the infimum is over a nonempty set and is attained.
-/

/-- The family of all shores certifies the minimum-cut value. -/
theorem isMinCutCertificate_univ (G : WeightedGraph V) :
    IsMinCutCertificate G Finset.univ := by
  intro G' hG'
  have hcut : G'.cut = G.cut := funext fun S => hG' S (Finset.mem_univ S)
  simp only [mincutValue, hcut]

/-- `cert(G)`: the minimum size of a family of shores certifying the minimum-cut value of
`G` against every nonnegative weighted graph on the same vertex set. -/
noncomputable def certificateComplexity (G : WeightedGraph V) : ℕ :=
  sInf {m | ∃ Q : Finset (Finset V), Q.card = m ∧ IsMinCutCertificate G Q}

theorem certificateComplexity_le {G : WeightedGraph V} {Q : Finset (Finset V)}
    (h : IsMinCutCertificate G Q) : certificateComplexity G ≤ Q.card :=
  Nat.sInf_le ⟨Q, rfl, h⟩

/-- The minimum is attained by some certificate. -/
theorem exists_certificate_card_eq (G : WeightedGraph V) :
    ∃ Q : Finset (Finset V), IsMinCutCertificate G Q ∧ Q.card = certificateComplexity G := by
  have hne : {m | ∃ Q : Finset (Finset V), Q.card = m ∧ IsMinCutCertificate G Q}.Nonempty :=
    ⟨_, Finset.univ, rfl, isMinCutCertificate_univ G⟩
  obtain ⟨Q, hQ, hc⟩ := Nat.sInf_mem hne
  exact ⟨Q, hc, hQ⟩

/-- Theorem 1 as a bound on `cert(G)`: `cert(G) ≤ 18 n ⌈log₂(2n)⌉²` for `n ≥ 2`. -/
theorem certificateComplexity_le_bound (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V) :
    certificateComplexity G ≤ 18 * Fintype.card V * (Nat.clog 2 (2 * Fintype.card V)) ^ 2 := by
  obtain ⟨Q, _, hQ, hS⟩ := exists_minCut_witnessCertificate G hn
  exact (certificateComplexity_le hS.isMinCutCertificate).trans hQ

/-- `cert(G) = O(n log²(2n))`, with the vertex set `Fin n`. -/
theorem certificateComplexity_near_linear :
    ∃ C : ℕ, ∀ n (G : WeightedGraph (Fin n)), 2 ≤ n →
      certificateComplexity G ≤ C * n * (Nat.clog 2 (2 * n)) ^ 2 :=
  ⟨18, fun n G hn => by simpa using certificateComplexity_le_bound G (by simpa using hn)⟩

/-- A zero optimum is certified by the single shore that attains it. -/
theorem certificateComplexity_le_one (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V)
    (h0 : mincutValue G = 0) : certificateComplexity G ≤ 1 := by
  obtain ⟨S, hS⟩ := exists_isMinCut_of_two_le_card G hn
  have hSval : G.cut S = 0 := by
    refine le_antisymm ?_ (G.cut_nonneg S)
    obtain ⟨T, hT, hTv⟩ := exists_isMinCut G ⟨S, (mem_properShores S).mpr hS.1⟩
    rw [← h0, ← hTv]; exact hS.2 T hT.1
  refine (certificateComplexity_le (Q := {S}) ?_).trans (by simp)
  intro G' hG'
  rw [h0]
  refine le_antisymm ?_ (mincutValue_nonneg G')
  rw [← hSval, ← hG' S (Finset.mem_singleton_self S)]
  exact mincutValue_le G' hS.1

/-- The complete graph with unit weights, a competitor with a positive minimum cut. -/
def unitComplete (V : Type*) [DecidableEq V] : WeightedGraph V where
  w u v := if u = v then 0 else 1
  symm u v := by simp only [eq_comm]
  nonneg u v := by split_ifs <;> norm_num
  diag v := by simp

theorem unitComplete_cut (S : Finset V) :
    (unitComplete V).cut S = (S.card : ℝ) * Sᶜ.card := by
  have hw : ∀ u ∈ S, ∀ v ∈ Sᶜ, (unitComplete V).w u v = 1 := fun u hu v hv => by
    have huv : u ≠ v := fun h => Finset.mem_compl.mp hv (h ▸ hu)
    simp [unitComplete, huv]
  rw [WeightedGraph.cut, Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl (hw u hu)]
  simp

theorem one_le_mincutValue_unitComplete (hn : 2 ≤ Fintype.card V) :
    1 ≤ mincutValue (unitComplete V) := by
  have hpos : 0 < Fintype.card V := by omega
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp hpos
  obtain ⟨S, hS, hval⟩ := exists_isMinCut (unitComplete V)
    ⟨{v}, (mem_properShores _).mpr (properShore_singleton v hn)⟩
  rw [← hval, unitComplete_cut]
  have h1 : 1 ≤ S.card := hS.1.1.card_pos
  have h2 : 1 ≤ Sᶜ.card :=
    Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr
      (mt (Finset.compl_eq_empty_iff S).mp hS.1.2))
  exact_mod_cast Nat.mul_le_mul h1 h2

/-- The definition is not vacuous: for `n ≥ 2` the empty family certifies nothing, since the
zero graph and the unit complete graph are both consistent with it and have different
minimum-cut values. -/
theorem one_le_certificateComplexity (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V) :
    1 ≤ certificateComplexity G := by
  obtain ⟨Q, hQ, hcard⟩ := exists_certificate_card_eq G
  rw [← hcard]
  rcases Nat.eq_zero_or_pos Q.card with h | h
  · exfalso
    rw [Finset.card_eq_zero] at h
    subst h
    have hpos : 0 < Fintype.card V := by omega
    obtain ⟨v⟩ := Fintype.card_pos_iff.mp hpos
    have h0 : mincutValue (0 : WeightedGraph V) = 0 :=
      le_antisymm ((mincutValue_le 0 (properShore_singleton v hn)).trans_eq
        (WeightedGraph.cut_zero _)) (mincutValue_nonneg 0)
    have hz := hQ 0 fun S hS => by simp at hS
    have hu := hQ (unitComplete V) fun S hS => by simp at hS
    linarith [one_le_mincutValue_unitComplete (V := V) hn]
  · exact h

/-- A zero optimum has certificate complexity exactly one. -/
theorem certificateComplexity_eq_one (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V)
    (h0 : mincutValue G = 0) : certificateComplexity G = 1 :=
  le_antisymm (certificateComplexity_le_one G hn h0) (one_le_certificateComplexity G hn)

end Certificate
end CutQueryComplexity
