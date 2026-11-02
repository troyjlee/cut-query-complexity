import CutQueryComplexity.AllPairsAudit.CutAlgebra

/-!
# Corrected Lemma 3.4 and the choice of terminal shore

The only graph hypotheses for the final lemma are unit weights and minimum
degree at least two. In particular, degree-two vertices are allowed.
-/

set_option autoImplicit false

namespace CutQueryComplexity.AllPairsAudit

open WeightedGraph
noncomputable section
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

def MinimalST (G : WeightedGraph V) (s t : V) (S : Finset V) : Prop :=
  IsSTMinCut G s t S ∧ ∀ T, T ⊂ S → s ∈ T → G.cut S < G.cut T

theorem exists_st_minimum (G : WeightedGraph V) {s t : V} (hst : s ≠ t) :
    ∃ S, IsSTMinCut G s t S := by
  let C := Finset.univ.filter (fun S : Finset V => s ∈ S ∧ t ∉ S)
  have hne : C.Nonempty := ⟨{s}, by simp [C, Ne.symm hst]⟩
  obtain ⟨S, hS, hm⟩ := Finset.exists_min_image C G.cut hne
  obtain ⟨hs, ht⟩ := (Finset.mem_filter.mp hS).2
  exact ⟨S, hs, ht, fun T hs ht => hm T (by simp [C, hs, ht])⟩

/-- Shrink the specified terminal side, without changing its optimal value. -/
theorem exists_minimal_inside (G : WeightedGraph V) {s t : V} {S : Finset V}
    (hS : IsSTMinCut G s t S) :
    ∃ T, T ⊆ S ∧ MinimalST G s t T ∧ G.cut T = G.cut S := by
  let M := Finset.univ.filter (fun T : Finset V => T ⊆ S ∧ IsSTMinCut G s t T)
  have hne : M.Nonempty := ⟨S, by simp [M, hS]⟩
  obtain ⟨T, hT, hm⟩ := Finset.exists_min_image M Finset.card hne
  obtain ⟨hTS, hTmin⟩ := (Finset.mem_filter.mp hT).2
  refine ⟨T, hTS, ⟨hTmin, ?_⟩, le_antisymm
    (hTmin.2.2 S hS.1 hS.2.1) (hS.2.2 T hTmin.1 hTmin.2.1)⟩
  intro U hUT hsU
  by_contra hn
  have htU' : t ∉ U := fun h => hTmin.2.1 (hUT.subset h)
  have he : G.cut U = G.cut T := le_antisymm (not_lt.mp hn)
    (hTmin.2.2 U hsU htU')
  have hUmin : IsSTMinCut G s t U :=
    ⟨hsU, htU', fun W hsW htW => he.trans_le (hTmin.2.2 W hsW htW)⟩
  have hc := hm U (by simp [M, hUT.subset.trans hTS, hUmin])
  have := Finset.card_lt_card hUT
  omega

/-- Shrinking the shore containing `s` can only increase `s`'s crossing degree. -/
theorem crossing_shrink_terminal (G : WeightedGraph V) {s : V} {S T : Finset V}
    (hTS : T ⊆ S) (hsT : s ∈ T) : crossing G S s ≤ crossing G T s := by
  simp only [crossing, hsT, hTS hsT, ite_true]
  exact incident_mono G s (Finset.compl_subset_compl.mpr hTS)

/-- Identify the unfriendly terminal first, then minimize its own shore. -/
theorem exists_minimal_unfriendly_inside (G : WeightedGraph V) {s t : V} {S : Finset V}
    (hS : IsSTMinCut G s t S) (hbad : 5 * G.degree s < 6 * crossing G S s) :
    ∃ T, T ⊆ S ∧ MinimalST G s t T ∧
      5 * G.degree s < 6 * crossing G T s := by
  obtain ⟨T, hTS, hT, -⟩ := exists_minimal_inside G hS
  have := crossing_shrink_terminal G hTS hT.1.1
  exact ⟨T, hTS, hT, by linarith⟩

theorem minimal_strict_half (G : WeightedGraph V) {s t x : V} {S : Finset V}
    (hS : MinimalST G s t S) (hx : x ∈ S) (hxs : x ≠ s) :
    2 * crossing G S x < G.degree x := by
  have hc := hS.2 (S.erase x) (Finset.erase_ssubset hx)
    (Finset.mem_erase.mpr ⟨Ne.symm hxs, hS.1.1⟩)
  rw [cut_erase G hx] at hc
  linarith

/-- The missing degree-two case in the paper: all its incident edges stay inside. -/
theorem degree_two_crossing_zero {G : WeightedGraph V} (hG : Unweighted G)
    {s t x : V} {S : Finset V} (hS : MinimalST G s t S)
    (hx : x ∈ S) (hxs : x ≠ s) (hd : G.degree x = 2) : crossing G S x = 0 := by
  have h := minimal_strict_half G hS hx hxs
  obtain ⟨c, hc⟩ := crossing_integral hG S x
  rw [hd, hc] at h
  have hc1 : (c : ℝ) < 1 := by linarith
  have : c < 1 := by exact_mod_cast hc1
  have : c = 0 := by omega
  simp [hc, this]

/-- The integral strict margin handles every degree at least two, including degree two. -/
theorem minimal_erase_inside_friendly {G : WeightedGraph V} (hG : Unweighted G)
    {s t x : V} {S : Finset V} (hS : MinimalST G s t S)
    (hx : x ∈ S) (hxs : x ≠ s) (hd : 2 ≤ G.degree x) :
    6 * crossing G (S.erase s) x ≤ 5 * G.degree x := by
  have hstrict := minimal_strict_half G hS hx hxs
  obtain ⟨d, hdd⟩ := degree_integral hG x
  obtain ⟨c, hcc⟩ := crossing_integral hG S x
  have hnat : 2 * c < d := by exact_mod_cast (hdd ▸ hcc ▸ hstrict)
  have hmargin : 2 * crossing G S x + 1 ≤ G.degree x := by
    rw [hdd, hcc]
    exact_mod_cast (show 2 * c + 1 ≤ d by omega)
  rw [crossing_erase_inside G hS.1.1 hx hxs]
  have := unweighted_edge_le_one hG x s
  linarith

/-- The two terminal stars overlap in at most their single common edge. -/
theorem terminal_crossing_sum (G : WeightedGraph V) {s t : V} {S : Finset V}
    (hs : s ∈ S) (ht : t ∉ S) :
    crossing G S s + crossing G S t ≤ G.cut S + G.w s t := by
  have hcut : (∑ x ∈ S.erase s, incident G x Sᶜ) + incident G s Sᶜ = G.cut S :=
    Finset.sum_erase_add _ _ hs
  have ht' := incident_erase_add G t hs
  have hrest : incident G t (S.erase s) ≤ ∑ x ∈ S.erase s, incident G x Sᶜ := by
    apply Finset.sum_le_sum
    intro x _
    rw [G.symm t x]
    exact Finset.single_le_sum (fun y _ => G.nonneg x y) (Finset.mem_compl.mpr ht)
  simp only [crossing, hs, ht, ite_true, ite_false]
  rw [G.symm t s] at ht'
  linarith

/-- An unfriendly minimum cut cannot have both terminals unfriendly. -/
theorem other_terminal_friendly {G : WeightedGraph V} (hG : Unweighted G)
    {s t : V} {S : Finset V} (hS : IsSTMinCut G s t S)
    (hd : 2 ≤ G.degree s) (hbad : 5 * G.degree s < 6 * crossing G S s) :
    6 * crossing G S t ≤ 5 * G.degree t := by
  have hsum := terminal_crossing_sum G hS.1 hS.2.1
  have hs := st_cut_le_degree G hS
  have ht := st_cut_le_degree G (st_compl G hS)
  simp only [G.cut_compl] at ht
  have hcr := crossing_le_cut G S s
  have hw := unweighted_edge_le_one hG s t
  by_contra h
  have := lt_of_not_ge h
  linarith

/-- Corrected Lemma 3.4, with a genuine graph-cut proof and degree-two vertices allowed. -/
theorem lemma34 {G : WeightedGraph V} (hG : Unweighted G)
    (hdeg : ∀ v, 2 ≤ G.degree v) {s t : V} {S : Finset V}
    (hS : MinimalST G s t S) (hbad : 5 * G.degree s < 6 * crossing G S s) :
    Friendly G (S.erase s) ∧ G.cut (S.erase s) ≤ 2 * G.degree s := by
  constructor
  · intro x
    by_cases hxs : x = s
    · subst x
      rw [crossing_erase_self G hS.1.1]
      have := degree_nonneg G s
      linarith
    · by_cases hx : x ∈ S
      · exact minimal_erase_inside_friendly hG hS hx hxs (hdeg x)
      · have hmono := crossing_erase_outside G (s := s) hx
        by_cases hxt : x = t
        · subst x
          have := other_terminal_friendly hG hS.1 (hdeg s) hbad
          linarith
        · have := nonterminal_half G hS.1 hxs hxt
          have := degree_nonneg G x
          linarith
  · rw [cut_erase G hS.1.1]
    have := st_cut_le_degree G hS.1
    have := crossing_nonneg G S s
    linarith

/-- For every pair, choose the correct terminal orientation before shrinking.
The useful minimum is either friendly or becomes friendly after removing its terminal. -/
theorem exists_structured_minimum {G : WeightedGraph V} (hG : Unweighted G)
    (hdeg : ∀ v, 2 ≤ G.degree v) {s t : V} (hst : s ≠ t) :
    ∃ r q S, ((r = s ∧ q = t) ∨ (r = t ∧ q = s)) ∧ IsSTMinCut G r q S ∧
      ((Friendly G S ∧ G.cut S ≤ 2 * Fintype.card V) ∨
       (Friendly G (S.erase r) ∧ G.cut (S.erase r) ≤ 2 * Fintype.card V)) := by
  obtain ⟨S, hS⟩ := exists_st_minimum G hst
  by_cases hf : Friendly G S
  · refine ⟨s, t, S, Or.inl ⟨rfl, rfl⟩, hS, Or.inl ⟨hf, ?_⟩⟩
    have := st_cut_le_degree G hS
    have := unweighted_degree_le_card hG s
    have := Nat.cast_nonneg (α := ℝ) (Fintype.card V)
    linarith
  · obtain ⟨x, hx⟩ : ∃ x, 5 * G.degree x < 6 * crossing G S x := by
      simpa only [Friendly, not_forall, not_le] using hf
    have hxterm : x = s ∨ x = t := by
      by_contra h
      push Not at h
      have := nonterminal_half G hS h.1 h.2
      have := degree_nonneg G x
      linarith
    have aux {r q : V} {U : Finset V} (hU : IsSTMinCut G r q U)
        (hbad : 5 * G.degree r < 6 * crossing G U r) :
        ∃ T, IsSTMinCut G r q T ∧ Friendly G (T.erase r) ∧
          G.cut (T.erase r) ≤ 2 * Fintype.card V := by
      obtain ⟨T, -, hT, hbadT⟩ := exists_minimal_unfriendly_inside G hU hbad
      obtain ⟨hfT, hbT⟩ := lemma34 hG hdeg hT hbadT
      have := unweighted_degree_le_card hG r
      exact ⟨T, hT.1, hfT, by linarith⟩
    rcases hxterm with hxs | hxt
    · subst x
      obtain ⟨T, hT, hfT, hbT⟩ := aux hS hx
      exact ⟨s, t, T, Or.inl ⟨rfl, rfl⟩, hT, Or.inr ⟨hfT, hbT⟩⟩
    · subst x
      obtain ⟨T, hT, hfT, hbT⟩ := aux (st_compl G hS) (by simpa using hx)
      exact ⟨t, s, T, Or.inr ⟨rfl, rfl⟩, hT, Or.inr ⟨hfT, hbT⟩⟩

end
end CutQueryComplexity.AllPairsAudit
