import CutQueryComplexity.Graph.Operations
import CutQueryComplexity.Search.Comp
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith

/-! # Degree normalization (Lemmas 27 and 28)

`heavyNeighbor v d` is the query step of degree normalization. Given the degree
`d = d_v` of a vertex with `d_v > (N - 1) U`, it repeatedly halves a candidate
list, keeping the half of larger average weight to `v`. The mass of one half is
`w(v, X) = (d_v + c(X) - c(X ∪ {v})) / 2`; the other is obtained by subtraction.
`heavyNeighbor_spec` proves that the output `u` has `w(v, u) > U`, using at most
`2 ⌈log₂ (N - 1)⌉` cut queries.

The remaining statements are offline. An edge heavier than `U` crosses no cut of
value at most `U`, so a contraction identifying only endpoints of such edges keeps
every such cut (`exists_contract_cut_eq`). Degrees of contracted classes are free
(`contract_degree_pair`, `contract_degree_singleton`). Finally,
`normalization_halves` is Lemma 28 for any final state of normalization: if all
old degrees are at least `U` and the final bound is below `U / (4N)`, every final
class contains at least two old vertices, so at most half of the vertices remain.
-/

namespace CutQueryComplexity
namespace Discovery

open Search Search.Comp WeightedGraph Finset

variable {V : Type} [Fintype V] [DecidableEq V]

section Search

/-- Halving search for a neighbor of `v` of above-average weight. The candidate list is `W`,
its known mass to `v` is `m`, and `d` is the degree of `v`. -/
noncomputable def heavySearch (v : V) (d : ℝ) (W : List V) (m : ℝ) : Comp (Finset V) ℝ V :=
  if W.length ≤ 1 then Comp.pure (W.headD v) else
    (ask (W.take (W.length / 2)).toFinset).bind fun a =>
      (ask (insert v (W.take (W.length / 2)).toFinset)).bind fun b =>
        if (m - (d + a - b) / 2) * (W.take (W.length / 2)).length ≤
            (d + a - b) / 2 * (W.drop (W.length / 2)).length then
          heavySearch v d (W.take (W.length / 2)) ((d + a - b) / 2)
        else heavySearch v d (W.drop (W.length / 2)) (m - (d + a - b) / 2)
termination_by W.length
decreasing_by all_goals simp only [List.length_take, List.length_drop]; omega

/-- Find a neighbor `u` of `v` with `w(v, u) > U`, given `d = d_v > (N - 1) U`. -/
noncomputable def heavyNeighbor (v : V) (d : ℝ) : Comp (Finset V) ℝ V :=
  heavySearch v d (Finset.univ.erase v).toList d

omit [Fintype V] in
theorem clog_half_succ_le {L l : ℕ} (hL : 2 ≤ L) (hl : l ≤ (L + 1) / 2) :
    Nat.clog 2 l + 1 ≤ Nat.clog 2 L := by
  rw [Nat.clog_of_two_le (by decide) hL, show L + 2 - 1 = L + 1 by omega]
  have := Nat.clog_mono_right 2 hl
  omega

/-- The halving invariant: the candidates are distinct non-neighbors of `v` itself,
`m` is their exact mass, and their average mass exceeds `U`. -/
theorem heavySearch_spec (G : WeightedGraph V) (v : V) (U : ℝ) :
    ∀ (n : ℕ) (W : List V) (m : ℝ), W.length ≤ n → W.Nodup → v ∉ W →
      m = G.cross {v} W.toFinset → U * W.length < m →
      (heavySearch v (G.degree v) W m).eval G.cut ∈ W ∧
      U < G.w v ((heavySearch v (G.degree v) W m).eval G.cut) ∧
      (heavySearch v (G.degree v) W m).cost G.cut ≤ 2 * Nat.clog 2 W.length := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W m hn hnd hv hm hU
    rw [heavySearch]
    by_cases hW : W.length ≤ 1
    · simp only [hW, ↓reduceIte]
      match W, hW with
      | [], _ => simp [hm] at hU
      | [u], _ => simp_all [cross]
    simp only [hW, ↓reduceIte]
    simp only [eval_bind, cost_bind, eval_ask, cost_ask]
    set L := W.length
    set W₁ := W.take (L / 2)
    set W₂ := W.drop (L / 2)
    have hl₁ : W₁.length = L / 2 := by simp only [W₁, List.length_take, L]; omega
    have hl₂ : W₂.length = L - L / 2 := by simp only [W₂, List.length_drop, L]
    have hsplit : W = W₁ ++ W₂ := (List.take_append_drop _ _).symm
    have hnd' := hsplit ▸ hnd
    rw [List.nodup_append] at hnd'
    have hdisj : Disjoint W₁.toFinset W₂.toFinset :=
      List.disjoint_toFinset_iff_disjoint.mpr fun a h₁ h₂ => hnd'.2.2 a h₁ a h₂ rfl
    have hv₁ : v ∉ W₁ := fun h => hv (hsplit ▸ List.mem_append_left _ h)
    have hv₂ : v ∉ W₂ := fun h => hv (hsplit ▸ List.mem_append_right _ h)
    -- The queried mass of the first half and the subtracted mass of the second.
    set m₁ := (G.degree v + G.cut W₁.toFinset - G.cut (insert v W₁.toFinset)) / 2
    have hm₁ : m₁ = G.cross {v} W₁.toFinset := by
      rw [G.cross_eq_three_cuts (by simpa using hv₁), cut_singleton, ← Finset.insert_eq]
    have hm₂ : m - m₁ = G.cross {v} W₂.toFinset := by
      rw [hm, hm₁, hsplit, List.toFinset_append, G.cross_union_right _ _ _ hdisj]
      ring
    have hl₁pos : (1 : ℝ) ≤ W₁.length := by rw [hl₁]; exact_mod_cast (by omega : 1 ≤ L / 2)
    have hl₂pos : (1 : ℝ) ≤ W₂.length := by rw [hl₂]; exact_mod_cast (by omega : 1 ≤ L - L / 2)
    have hLsum : (L : ℝ) = W₁.length + W₂.length := by
      have : W₁.length + W₂.length = L := by omega
      exact_mod_cast this.symm
    rw [hLsum] at hU
    by_cases hcmp : (m - m₁) * (W₁.length : ℝ) ≤ m₁ * W₂.length
    · have hcmp' := hcmp
      simp only [m₁] at hcmp'
      simp only [hcmp', ↓reduceIte]
      have hU₁ : U * W₁.length < m₁ := by
        by_contra hcon
        push Not at hcon
        have h1 : m₁ * W₂.length ≤ U * W₁.length * W₂.length :=
          mul_le_mul_of_nonneg_right hcon (by linarith)
        have h2 : (m - m₁) * W₁.length ≤ U * W₂.length * W₁.length := by linarith
        have h3 : m - m₁ ≤ U * W₂.length := by
          by_contra h
          push Not at h
          have := mul_lt_mul_of_pos_right h (by linarith : (0 : ℝ) < W₁.length)
          linarith
        linarith
      obtain ⟨hmem, hw, hc⟩ := ih (L / 2) (by omega) W₁ m₁ (by omega) hnd'.1 hv₁ hm₁ hU₁
      simp only [m₁] at hmem hw hc
      refine ⟨List.mem_of_mem_take hmem, hw, ?_⟩
      have := clog_half_succ_le (L := L) (l := W₁.length) (by omega) (by omega)
      omega
    · have hcmp' := hcmp
      simp only [m₁] at hcmp'
      simp only [hcmp', ↓reduceIte]
      push Not at hcmp
      have hU₂ : U * W₂.length < m - m₁ := by
        by_contra hcon
        push Not at hcon
        have h1 : (m - m₁) * W₁.length ≤ U * W₂.length * W₁.length :=
          mul_le_mul_of_nonneg_right hcon (by linarith)
        have h2 : m₁ * W₂.length < U * W₁.length * W₂.length := by linarith
        have h3 : m₁ < U * W₁.length := by
          by_contra h
          push Not at h
          have := mul_le_mul_of_nonneg_right h (by linarith : (0 : ℝ) ≤ W₂.length)
          linarith
        linarith
      obtain ⟨hmem, hw, hc⟩ := ih (L - L / 2) (by omega) W₂ (m - m₁) (by omega) hnd'.2.1 hv₂
        hm₂ hU₂
      simp only [m₁] at hmem hw hc
      refine ⟨List.mem_of_mem_drop hmem, hw, ?_⟩
      have := clog_half_succ_le (L := L) (l := W₂.length) (by omega) (by omega)
      omega

/-- Lemma 27, query step: if `d_v > (N - 1) U`, the search returns `u ≠ v` with
`w(v, u) > U`, using at most `2 ⌈log₂ (N - 1)⌉` cut queries. -/
theorem heavyNeighbor_spec (G : WeightedGraph V) (v : V) {U : ℝ}
    (hdeg : ((Fintype.card V : ℝ) - 1) * U < G.degree v) :
    (heavyNeighbor v (G.degree v)).eval G.cut ≠ v ∧
      U < G.w v ((heavyNeighbor v (G.degree v)).eval G.cut) ∧
      (heavyNeighbor v (G.degree v)).cost G.cut ≤ 2 * Nat.clog 2 (Fintype.card V - 1) := by
  have hlen : (Finset.univ.erase v).toList.length = Fintype.card V - 1 := by
    rw [Finset.length_toList, Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]
  have hmass : G.degree v = G.cross {v} (Finset.univ.erase v).toList.toFinset := by
    rw [Finset.toList_toFinset, cross, Finset.sum_singleton, degree,
      Finset.sum_erase _ (G.diag v)]
  have hcard : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  unfold heavyNeighbor
  obtain ⟨hmem, hw, hc⟩ := heavySearch_spec G v U _ _ _ le_rfl (Finset.nodup_toList _)
    (by simp) hmass (by rw [hlen]; push_cast [hcard]; linarith)
  refine ⟨fun h => by rw [h] at hmem; simp at hmem, hw, ?_⟩
  rw [hlen] at hc
  exact hc

end Search

section Contraction

/-- An edge heavier than `U` crosses no cut of value at most `U`. -/
theorem not_separated_of_heavy (G : WeightedGraph V) {S : Finset V} {U : ℝ} {x y : V}
    (hS : G.cut S ≤ U) (hxy : U < G.w x y) : x ∈ S ↔ y ∈ S := by
  have key : ∀ a b, a ∈ S → b ∉ S → G.w a b ≤ G.cut S := fun a b ha hb =>
    calc G.w a b ≤ ∑ c ∈ Sᶜ, G.w a c :=
          Finset.single_le_sum (fun c _ => G.nonneg a c) (Finset.mem_compl.mpr hb)
      _ ≤ G.cut S := Finset.single_le_sum (f := fun a => ∑ c ∈ Sᶜ, G.w a c)
          (fun _ _ => Finset.sum_nonneg fun _ _ => G.nonneg _ _) ha
  constructor
  · intro hx; by_contra hy; linarith [key x y hx hy]
  · intro hy; by_contra hx; linarith [key y x hy hx, G.symm x y]

variable {B : Type} [Fintype B] [DecidableEq B]

/-- A shore that is a union of fibers is the pullback of its image. -/
theorem pull_image_of_saturated (π : V → B) {S : Finset V}
    (hS : ∀ x y, π x = π y → (x ∈ S ↔ y ∈ S)) : pull π (S.image π) = S := by
  ext x
  simp only [mem_pull, Finset.mem_image]
  exact ⟨fun ⟨y, hy, hyx⟩ => (hS y x hyx).mp hy, fun hx => ⟨x, hx, rfl⟩⟩

/-- Safe contraction: if `π` identifies only endpoints of edges heavier than `U`, every cut
of value at most `U` (in particular every minimum cut and the witness of `U`) survives in
the contracted graph with the same value. -/
theorem exists_contract_cut_eq (G : WeightedGraph V) (π : V → B) {U : ℝ}
    (hπ : ∀ x y, π x = π y → x = y ∨ U < G.w x y) {S : Finset V} (hS : G.cut S ≤ U) :
    ∃ T : Finset B, pull π T = S ∧ (G.contract π).cut T = G.cut S := by
  have hsat : ∀ x y, π x = π y → (x ∈ S ↔ y ∈ S) := by
    intro x y hxy
    rcases hπ x y hxy with rfl | h
    · exact Iff.rfl
    · exact not_separated_of_heavy G hS h
  refine ⟨S.image π, pull_image_of_saturated π hsat, ?_⟩
  rw [cut_contract, pull_image_of_saturated π hsat]

/-- The degree of a contracted vertex is one original cut. -/
theorem contract_degree (G : WeightedGraph V) (π : V → B) (b : B) :
    (G.contract π).degree b = G.cut (fiber π b) := by
  rw [← cut_singleton, cut_contract]; rfl

/-- Free degree update: a class `{u, v}` has degree `d_u + d_v - 2 w(u, v)`. -/
theorem contract_degree_pair (G : WeightedGraph V) (π : V → B) {b : B} {u v : V}
    (huv : u ≠ v) (hb : fiber π b = {u, v}) :
    (G.contract π).degree b = G.degree u + G.degree v - 2 * G.w u v := by
  rw [contract_degree, hb, G.edge_eq_three_cuts huv, cut_singleton, cut_singleton]
  ring

/-- Uncontracted vertices keep their degrees. -/
theorem contract_degree_singleton (G : WeightedGraph V) (π : V → B) {b : B} {x : V}
    (hb : fiber π b = {x}) : (G.contract π).degree b = G.degree x := by
  rw [contract_degree, hb, cut_singleton]

/-- Lemma 28, for any final state of normalization started from a graph whose degrees are at
least `U > 0`. The final quotient is `G.contract π` with `N' = |B|` classes, final bound
`0 ≤ U' ≤ u < U / (4N)`, and stopping condition `d'_b ≤ (N' - 1) U'`. Then every class has
at least two old vertices, so `2 N' ≤ N`. -/
theorem normalization_halves (G : WeightedGraph V) (π : V → B) (hπ : Function.Surjective π)
    {U u U' : ℝ} (hU : 0 < U) (hdeg : ∀ x, U ≤ G.degree x) (hU'0 : 0 ≤ U') (hU'u : U' ≤ u)
    (hu : u < U / (4 * Fintype.card V))
    (hstop : ∀ b, (G.contract π).degree b ≤ ((Fintype.card B : ℝ) - 1) * U') :
    (∀ b, 2 ≤ (fiber π b).card) ∧ 2 * Fintype.card B ≤ Fintype.card V := by
  have hBV : Fintype.card B ≤ Fintype.card V := Fintype.card_le_of_surjective π hπ
  have hfib : ∀ b, 2 ≤ (fiber π b).card := by
    intro b
    obtain ⟨x, hx⟩ := hπ b
    by_contra hlt
    have hone : fiber π b = {x} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨by simp [hx], fun y hy => ?_⟩
      exact Finset.card_le_one.mp (by omega) y hy x (by simp [hx])
    have h1 := hstop b
    rw [contract_degree_singleton G π hone] at h1
    have hN : (0 : ℝ) < Fintype.card V := by
      exact_mod_cast Fintype.card_pos_iff.mpr ⟨x⟩
    have hBV' : (Fintype.card B : ℝ) ≤ Fintype.card V := by exact_mod_cast hBV
    have hB1 : (1 : ℝ) ≤ Fintype.card B := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨b⟩
    -- `(N' - 1) U' ≤ N u < U / 4`.
    have h2 : ((Fintype.card B : ℝ) - 1) * U' ≤ Fintype.card V * u := by
      calc ((Fintype.card B : ℝ) - 1) * U' ≤ Fintype.card V * U' :=
            mul_le_mul_of_nonneg_right (by linarith) hU'0
        _ ≤ _ := mul_le_mul_of_nonneg_left hU'u hN.le
    have h3 : Fintype.card V * u < U / 4 := by
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * Fintype.card V)] at hu
      rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
      linarith
    linarith [hdeg x]
  refine ⟨hfib, ?_⟩
  have hsum : Fintype.card V = ∑ b : B, (fiber π b).card := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (π x))
      |>.trans (Finset.sum_congr rfl fun b _ => by congr 1; ext; simp)
  rw [hsum]
  calc 2 * Fintype.card B = ∑ _b : B, 2 := by simp [mul_comm]
    _ ≤ _ := Finset.sum_le_sum fun b _ => hfib b

end Contraction

end Discovery
end CutQueryComplexity
