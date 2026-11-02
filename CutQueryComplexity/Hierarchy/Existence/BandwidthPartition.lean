import CutQueryComplexity.Hierarchy.Existence.Majority
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Partitions with the bandwidth property (hierarchy plan, Milestones 2–3)

`IsPart R 𝒫`: the parts of `𝒫` are nonempty, pairwise disjoint, and cover `R`.

`exists_bandwidth_partition`: if `λ ≥ 1` and `4 β(|V|) ≤ λ`, where `β(s) = log s / log(4/3)`,
then every `R` has a partition into parts with bandwidth `λ` whose total boundary is at most
`2 out(R)`. The process splits a part `P` along a violating `U` (`4|U| ≤ 3|P|` and
`λ cross(U, P ∖ U) < out(U)`). Instead of a charging trace we use the potential
`Φ(𝒫) = ∑_P out(P) β(|P|)`: a split raises `∑_P out(P)` by `2z`, `z = cross(U, P ∖ U)`, and
lowers `Φ` by more than `(λ − 2β(|V|)) z`, because `β(|U|) ≤ β(|P|) − 1`. Strong induction on
the number of parts gives the bound for arbitrary nonnegative real weights.
-/

namespace CutQueryComplexity
namespace Hierarchy

open WeightedGraph Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A partition of `R` into nonempty parts. -/
structure IsPart (R : Finset V) (Ps : Finset (Finset V)) : Prop where
  nonempty : ∀ P ∈ Ps, P.Nonempty
  disj : (Ps : Set (Finset V)).PairwiseDisjoint id
  union : Ps.biUnion id = R

namespace IsPart

variable {R : Finset V} {Ps : Finset (Finset V)}

omit [Fintype V] in
theorem subset (h : IsPart R Ps) {P : Finset V} (hP : P ∈ Ps) : P ⊆ R := by
  rw [← h.union]; exact subset_biUnion_of_mem id hP

omit [Fintype V] in
theorem card_le (h : IsPart R Ps) : Ps.card ≤ R.card := by
  rw [← h.union, card_biUnion h.disj]
  calc Ps.card = ∑ _P ∈ Ps, 1 := by simp
    _ ≤ ∑ P ∈ Ps, (id P).card := sum_le_sum fun P hP => (h.nonempty P hP).card_pos

omit [Fintype V] in
theorem eq_of_mem_of_inter {h : IsPart R Ps} {P Q : Finset V} (hP : P ∈ Ps) (hQ : Q ∈ Ps)
    {v : V} (hvP : v ∈ P) (hvQ : v ∈ Q) : P = Q := by
  by_contra hne
  exact disjoint_left.mp (h.disj hP hQ hne) hvP hvQ

omit [Fintype V] in
/-- The empty partition of `∅` and the trivial partition of a nonempty set. -/
theorem single (hR : R.Nonempty) : IsPart R {R} :=
  ⟨by simpa using hR, by simp, by simp⟩

omit [Fintype V] in
theorem empty : IsPart (∅ : Finset V) ∅ := ⟨by simp, by simp, by simp⟩

omit [Fintype V] in
/-- Splitting a part into two nonempty pieces. -/
theorem split (h : IsPart R Ps) {P U : Finset V} (hP : P ∈ Ps) (hU : U ⊆ P) (hU0 : U.Nonempty)
    (hUP : U ≠ P) : IsPart R ((Ps.erase P) ∪ {U, P \ U}) := by
  have hPU0 : (P \ U).Nonempty := by
    by_contra h0
    rw [not_nonempty_iff_eq_empty, sdiff_eq_empty_iff_subset] at h0
    exact hUP (subset_antisymm hU h0)
  refine ⟨?_, ?_, ?_⟩
  · intro Q hQ
    rcases mem_union.mp hQ with hQ | hQ
    · exact h.nonempty Q (mem_of_mem_erase hQ)
    · rcases mem_insert.mp hQ with rfl | hQ
      · exact hU0
      · rw [mem_singleton.mp hQ]; exact hPU0
  · intro Q hQ Q' hQ' hne
    have hsub : ∀ {X}, X ∈ ({U, P \ U} : Finset (Finset V)) → X ⊆ P := by
      intro X hX
      rcases mem_insert.mp hX with rfl | hX
      · exact hU
      · rw [mem_singleton.mp hX]; exact sdiff_subset
    have hfar : ∀ {X Y}, X ∈ Ps.erase P → Y ∈ ({U, P \ U} : Finset (Finset V)) →
        Disjoint (id X) (id Y) := by
      intro X Y hX hY
      exact (h.disj (mem_of_mem_erase hX) hP (ne_of_mem_erase hX)).mono_right (hsub hY)
    rcases mem_union.mp hQ with hQ | hQ <;> rcases mem_union.mp hQ' with hQ' | hQ'
    · exact h.disj (mem_of_mem_erase hQ) (mem_of_mem_erase hQ') hne
    · exact hfar hQ hQ'
    · exact (hfar hQ' hQ).symm
    · rcases mem_insert.mp hQ with rfl | hQ <;> rcases mem_insert.mp hQ' with rfl | hQ'
      · exact absurd rfl hne
      · rw [mem_singleton.mp hQ']; exact disjoint_sdiff
      · rw [mem_singleton.mp hQ]; exact disjoint_sdiff.symm
      · rw [mem_singleton.mp hQ, mem_singleton.mp hQ'] at hne; exact absurd rfl hne
  · rw [← h.union]
    ext v
    simp only [mem_biUnion, mem_union, mem_insert, mem_singleton, id, mem_erase]
    constructor
    · rintro ⟨Q, hQ, hv⟩
      rcases hQ with ⟨_, hQ⟩ | rfl | rfl
      · exact ⟨Q, hQ, hv⟩
      · exact ⟨P, hP, hU hv⟩
      · exact ⟨P, hP, (mem_sdiff.mp hv).1⟩
    · rintro ⟨Q, hQ, hv⟩
      by_cases hQP : Q = P
      · subst hQP
        by_cases hvU : v ∈ U
        · exact ⟨U, Or.inr (Or.inl rfl), hvU⟩
        · exact ⟨Q \ U, Or.inr (Or.inr rfl), mem_sdiff.mpr ⟨hv, hvU⟩⟩
      · exact ⟨Q, Or.inl ⟨hQP, hQ⟩, hv⟩

omit [Fintype V] in
/-- Sums over a split partition. -/
theorem sum_split (h : IsPart R Ps) {P U : Finset V} (hP : P ∈ Ps) (hU : U ⊆ P)
    (hU0 : U.Nonempty) (hUP : U ≠ P) (f : Finset V → ℝ) :
    ∑ Q ∈ (Ps.erase P) ∪ {U, P \ U}, f Q = ∑ Q ∈ Ps, f Q - f P + f U + f (P \ U) := by
  have hPU0 : (P \ U).Nonempty := by
    by_contra h0
    rw [not_nonempty_iff_eq_empty, sdiff_eq_empty_iff_subset] at h0
    exact hUP (subset_antisymm hU h0)
  have hnot : ∀ {X}, X ⊆ P → X.Nonempty → X ≠ P → X ∉ Ps.erase P := by
    intro X hX hX0 hXP hmem
    obtain ⟨v, hv⟩ := hX0
    exact hXP (eq_of_mem_of_inter (h := h) (mem_of_mem_erase hmem) hP hv (hX hv))
  have hdisj : Disjoint (Ps.erase P) {U, P \ U} := by
    rw [disjoint_right]
    intro X hX
    rcases mem_insert.mp hX with rfl | hX
    · exact hnot hU hU0 hUP
    · rw [mem_singleton.mp hX]
      refine hnot sdiff_subset hPU0 fun he => ?_
      obtain ⟨v, hv⟩ := hU0
      have := he ▸ hU hv
      exact (mem_sdiff.mp this).2 hv
  have hUne : U ≠ P \ U := by
    intro he
    obtain ⟨v, hv⟩ := hU0
    have := he ▸ hv
    exact (mem_sdiff.mp this).2 hv
  rw [sum_union hdisj, sum_pair hUne, ← add_sum_erase Ps f hP]
  ring

end IsPart

/-! ## The potential argument -/

/-- `β(s) = log s / log (4/3)`. -/
noncomputable def beta (s : ℕ) : ℝ := Real.log s / Real.log (4 / 3)

theorem log43_pos : 0 < Real.log (4 / 3 : ℝ) := Real.log_pos (by norm_num)

theorem beta_nonneg {s : ℕ} (hs : 1 ≤ s) : 0 ≤ beta s :=
  div_nonneg (Real.log_nonneg (by exact_mod_cast hs)) log43_pos.le

theorem beta_mono {s t : ℕ} (hs : 1 ≤ s) (hst : s ≤ t) : beta s ≤ beta t := by
  unfold beta
  apply div_le_div_of_nonneg_right _ log43_pos.le
  exact Real.log_le_log (by exact_mod_cast hs) (by exact_mod_cast hst)

/-- Shrinking by `3/4` lowers `β` by one. -/
theorem beta_shrink {s t : ℕ} (hs : 1 ≤ s) (hst : 4 * s ≤ 3 * t) : beta s ≤ beta t - 1 := by
  unfold beta
  have hl := log43_pos
  have ht : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  rw [div_le_iff₀ hl, sub_mul, one_mul, div_mul_cancel₀ _ hl.ne']
  have : (s : ℝ) * (4 / 3) ≤ t := by
    have : ((4 * s : ℕ) : ℝ) ≤ ((3 * t : ℕ) : ℝ) := by exact_mod_cast hst
    push_cast at this; linarith
  calc Real.log s = Real.log (s * (4 / 3)) - Real.log (4 / 3) := by
        rw [Real.log_mul (by positivity) (by norm_num)]; ring
    _ ≤ Real.log t - Real.log (4 / 3) := by
        gcongr

/-- The potential. -/
noncomputable def Phi (J : WeightedGraph V) (Ps : Finset (Finset V)) : ℝ :=
  ∑ P ∈ Ps, J.cut P * beta P.card

/-- The total boundary. -/
noncomputable def F (J : WeightedGraph V) (Ps : Finset (Finset V)) : ℝ := ∑ P ∈ Ps, J.cut P

theorem Phi_nonneg (J : WeightedGraph V) {R : Finset V} {Ps : Finset (Finset V)}
    (h : IsPart R Ps) : 0 ≤ Phi J Ps :=
  sum_nonneg fun P hP => mul_nonneg (J.cut_nonneg P) (beta_nonneg (h.nonempty P hP).card_pos)

/-- The boundary identity of a split: `out(U) + out(P ∖ U) = out(P) + 2 cross(U, P ∖ U)`. -/
theorem cut_split (J : WeightedGraph V) {P U : Finset V} (hU : U ⊆ P) :
    J.cut U + J.cut (P \ U) = J.cut P + 2 * J.cross U (P \ U) := by
  have h := J.cross_eq_three_cuts (disjoint_sdiff : Disjoint U (P \ U))
  rw [union_sdiff_of_subset hU] at h
  linarith

/-- **Milestone 3.** Every `R` has a partition into parts of bandwidth `λ` with total
boundary at most `2 out(R)`, provided `λ ≥ 1` and `4 β(|V|) ≤ λ`. -/
theorem exists_bandwidth_partition (J : WeightedGraph V) {lam : ℝ} (hlam1 : 1 ≤ lam)
    (hlamB : 4 * beta (Fintype.card V) ≤ lam) (R : Finset V) :
    ∃ Ps, IsPart R Ps ∧ (∀ P ∈ Ps, Bandwidth J P lam) ∧ F J Ps ≤ 2 * J.cut R := by
  set B := beta (Fintype.card V)
  have hbeta : ∀ P : Finset V, P.Nonempty → beta P.card ≤ B :=
    fun P hP => beta_mono hP.card_pos (card_le_univ P)
  -- the invariant, by strong induction on the number of parts still possible
  have key : ∀ m (Ps : Finset (Finset V)), IsPart R Ps → R.card - Ps.card ≤ m →
      ∃ Qs, IsPart R Qs ∧ (∀ P ∈ Qs, Bandwidth J P lam) ∧
        (lam - 2 * B) * (F J Qs - F J Ps) ≤ 2 * (Phi J Ps - Phi J Qs) := by
    intro m
    induction m with
    | zero =>
        intro Ps hPs hm
        refine ⟨Ps, hPs, ?_, by simp⟩
        intro P hP U hUP hUcard
        by_contra hviol
        push Not at hviol
        -- a violation would split `P`, making more parts than vertices
        have hU0 : U.Nonempty := by
          by_contra h0
          rw [not_nonempty_iff_eq_empty] at h0
          subst h0; simp at hviol
        have hUP' : U ≠ P := by
          rintro rfl
          have := (hPs.nonempty U hP).card_pos; omega
        have h' := hPs.split hP hUP hU0 hUP'
        have hc := h'.card_le
        have hcard : ((Ps.erase P) ∪ {U, P \ U}).card = Ps.card + 1 := by
          have := IsPart.sum_split hPs hP hUP hU0 hUP' (fun _ => (1 : ℝ))
          simp only [sum_const, nsmul_eq_mul, mul_one] at this
          have : (((Ps.erase P) ∪ {U, P \ U}).card : ℝ) = Ps.card + 1 := by linarith
          exact_mod_cast this
        omega
    | succ m ih =>
        intro Ps hPs hm
        by_cases hall : ∀ P ∈ Ps, Bandwidth J P lam
        · exact ⟨Ps, hPs, hall, by simp⟩
        push Not at hall
        obtain ⟨P, hP, hPb⟩ := hall
        unfold Bandwidth at hPb
        push Not at hPb
        obtain ⟨U, hUP, hUcard, hviol⟩ := hPb
        have hU0 : U.Nonempty := by
          by_contra h0
          rw [not_nonempty_iff_eq_empty] at h0
          subst h0; simp at hviol
        have hP0 := hPs.nonempty P hP
        have hUP' : U ≠ P := by
          rintro rfl
          have := hP0.card_pos; omega
        have h' := hPs.split hP hUP hU0 hUP'
        have hcard : ((Ps.erase P) ∪ {U, P \ U}).card = Ps.card + 1 := by
          have := IsPart.sum_split hPs hP hUP hU0 hUP' (fun _ => (1 : ℝ))
          simp only [sum_const, nsmul_eq_mul, mul_one] at this
          have : (((Ps.erase P) ∪ {U, P \ U}).card : ℝ) = Ps.card + 1 := by linarith
          exact_mod_cast this
        obtain ⟨Qs, hQs, hband, hineq⟩ := ih _ h' (by omega)
        refine ⟨Qs, hQs, hband, ?_⟩
        -- one split
        set z := J.cross U (P \ U)
        have hz0 : 0 ≤ z := J.cross_nonneg _ _
        have hF : F J ((Ps.erase P) ∪ {U, P \ U}) = F J Ps + 2 * z := by
          unfold F
          rw [IsPart.sum_split hPs hP hUP hU0 hUP' J.cut]
          have := cut_split J hUP
          linarith
        have hPU0 : (P \ U).Nonempty := by
          by_contra h0
          rw [not_nonempty_iff_eq_empty, sdiff_eq_empty_iff_subset] at h0
          exact hUP' (subset_antisymm hUP h0)
        have hβU : beta U.card ≤ beta P.card - 1 := beta_shrink hU0.card_pos hUcard
        have hβP' : beta (P \ U).card ≤ beta P.card :=
          beta_mono hPU0.card_pos (card_le_card sdiff_subset)
        have hβP := hbeta P hP0
        have hβP0 := beta_nonneg hP0.card_pos
        have hPhi : Phi J ((Ps.erase P) ∪ {U, P \ U}) ≤ Phi J Ps - (lam - 2 * B) * z := by
          unfold Phi
          rw [IsPart.sum_split hPs hP hUP hU0 hUP' fun Q => J.cut Q * beta Q.card]
          have hsplit := cut_split J hUP
          have hcu0 := J.cut_nonneg U
          have hcp0 := J.cut_nonneg (P \ U)
          have h1 : J.cut U * beta U.card ≤ J.cut U * (beta P.card - 1) :=
            mul_le_mul_of_nonneg_left hβU hcu0
          have h2 : J.cut (P \ U) * beta (P \ U).card ≤ J.cut (P \ U) * beta P.card :=
            mul_le_mul_of_nonneg_left hβP' hcp0
          have h3 : 2 * z * beta P.card ≤ 2 * z * B := by gcongr
          -- `ΔΦ ≤ 2 z β(P) − out(U) < 2 z B − λ z`
          nlinarith
        rw [hF] at hineq
        nlinarith
  rcases R.eq_empty_or_nonempty with hR | hR
  · subst hR
    exact ⟨∅, IsPart.empty, by simp, by simp [F]⟩
  obtain ⟨Qs, hQs, hband, hineq⟩ := key R.card {R} (IsPart.single hR) (by omega)
  refine ⟨Qs, hQs, hband, ?_⟩
  have hF0 : F J {R} = J.cut R := by simp [F]
  have hPhi0 : Phi J {R} ≤ B * J.cut R := by
    simp only [Phi, sum_singleton]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hbeta R hR) (J.cut_nonneg R)
  have hPhiQ := Phi_nonneg J hQs
  rw [hF0] at hineq
  have hB0 : 0 ≤ B := beta_nonneg (hR.card_pos.trans_le (card_le_univ R))
  have hcut0 := J.cut_nonneg R
  -- `(λ − 2B)(F − out R) ≤ 2 B out R` with `λ − 2B ≥ 2B` and `λ − 2B ≥ 1/2`
  by_contra hcon
  push Not at hcon
  have hpos : 0 < F J Qs - J.cut R - J.cut R := by linarith
  nlinarith

end Hierarchy
end CutQueryComplexity
