import CutQueryComplexity.FractionalForest.Potential
import CutQueryComplexity.FractionalForest.RootedCover
import CutQueryComplexity.Graph.ArborescencePacking
import CutQueryComplexity.DirectedCertificate.Flow

/-! # Logarithm-free deletion progress (W4, progress half)

Source: Lemmas 16 and 19, Theorem 20, and the unit-progress step of Corollary 21 of
paper P3 (`papers/P3/directed-cut-certificates.pdf`).

* `Dpot_supermodular`, `gain_mono` : supermodularity of `D` and `Δ_v(W) ≥ Δ_v(K)`.
* `exists_densest`, `densest_core` : a densest `K ⊆ W` and its localization facts.
* `exists_orientation` : orientation with out-degree exactly `ρ` (flow to an auxiliary sink).
* `uniform_roots` : a mixture of rooted forests with exact pair marginals and root marginal
  `1 - ρ`, via W3 packing toward an auxiliary root.
* `loss_eq` : the deletion-loss identity `g(K) - g(K∖T) = y(δ⁻(T)) + h|T|`.
* `deletion_progress`, `exists_gain_ge_div` : the stronger and multiplicative progress bounds.
* `unit_progress` : the frozen interface.
-/

namespace CutQueryComplexity

open Finset

namespace FractionalForest

/-! ## Supermodularity of the potential and gain monotonicity -/

section Potential

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem gfun_supermodular (x : WeightedGraph V) (ε : ℝ) (S T : Finset V) :
    gfun x ε S + gfun x ε T ≤ gfun x ε (S ∪ T) + gfun x ε (S ∩ T) := by
  have hm := mass_supermodular x S T
  have hc : ((S ∪ T).card : ℝ) + (S ∩ T).card = S.card + T.card := by
    exact_mod_cast card_union_add_card_inter S T
  have hc' : (1 - ε) * ((S ∪ T).card : ℝ) + (1 - ε) * (S ∩ T).card =
      (1 - ε) * S.card + (1 - ε) * T.card := by rw [← mul_add, ← mul_add, hc]
  unfold gfun
  linarith

/-- Supermodularity of `D`. -/
theorem Dpot_supermodular (x : WeightedGraph V) (ε : ℝ) (A B : Finset V) :
    Dpot x ε A + Dpot x ε B ≤ Dpot x ε (A ∪ B) + Dpot x ε (A ∩ B) := by
  obtain ⟨S, hSA, hS⟩ := exists_Dpot_eq x ε A
  obtain ⟨T, hTB, hT⟩ := exists_Dpot_eq x ε B
  rw [← hS, ← hT]
  calc gfun x ε S + gfun x ε T ≤ gfun x ε (S ∪ T) + gfun x ε (S ∩ T) :=
        gfun_supermodular x ε S T
    _ ≤ _ := add_le_add (gfun_le_Dpot x ε (union_subset_union hSA hTB))
        (gfun_le_Dpot x ε (inter_subset_inter hSA hTB))

/-- Gain monotonicity: `Δ_v(W) ≥ Δ_v(K)` for `v ∈ K ⊆ W`. -/
theorem gain_mono (x : WeightedGraph V) (ε : ℝ) {K W : Finset V} (hKW : K ⊆ W) {v : V}
    (hv : v ∈ K) : gain x ε K v ≤ gain x ε W v := by
  have h := Dpot_supermodular x ε K (W.erase v)
  have h1 : K ∪ W.erase v = W := by
    ext u
    by_cases huv : u = v
    · subst huv; simp [hKW hv, hv]
    · simp only [mem_union, mem_erase, huv, ne_eq, not_false_eq_true, true_and]
      exact ⟨fun h => h.elim (fun h => hKW h) id, Or.inr⟩
  have h2 : K ∩ W.erase v = K.erase v := by
    ext u
    simp only [mem_inter, mem_erase]
    exact ⟨fun ⟨h1, h2, _⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1, hKW h2⟩⟩
  rw [h1, h2] at h
  unfold gain
  linarith

end Potential

/-! ## The densest set and localization (`lem:densest-deletion-core`) -/

section Densest

variable {V : Type*}

/-- Density of a set. -/
noncomputable def dens (x : WeightedGraph V) (S : Finset V) : ℝ := mass x S / S.card

/-- `K` is a densest nonempty subset of `W`. -/
def IsDensest (x : WeightedGraph V) (W K : Finset V) : Prop :=
  K ⊆ W ∧ K.Nonempty ∧ ∀ S ⊆ W, S.Nonempty → dens x S ≤ dens x K

theorem exists_densest (x : WeightedGraph V) {W : Finset V} (hW : W.Nonempty) :
    ∃ K, IsDensest x W K := by
  have hne : (W.powerset.filter Finset.Nonempty).Nonempty :=
    ⟨W, mem_filter.2 ⟨mem_powerset_self W, hW⟩⟩
  obtain ⟨K, hK, hmax⟩ := exists_max_image _ (dens x) hne
  obtain ⟨hKW, hKne⟩ := mem_filter.1 hK
  exact ⟨K, mem_powerset.1 hKW, hKne, fun S hS hSne =>
    hmax S (mem_filter.2 ⟨mem_powerset.2 hS, hSne⟩)⟩

theorem mass_le_dens_mul {x : WeightedGraph V} {W K : Finset V} (hK : IsDensest x W K)
    {S : Finset V} (hS : S ⊆ W) : mass x S ≤ dens x K * S.card := by
  rcases S.eq_empty_or_nonempty with rfl | hSne
  · simp
  · have h := hK.2.2 S hS hSne
    have hc : (0 : ℝ) < S.card := by exact_mod_cast hSne.card_pos
    unfold dens at h
    rwa [div_le_iff₀ hc] at h

theorem mass_eq_dens_mul (x : WeightedGraph V) {K : Finset V} (hK : K.Nonempty) :
    mass x K = dens x K * K.card := by
  have hc : (0 : ℝ) < K.card := by exact_mod_cast hK.card_pos
  unfold dens; field_simp

/-- The densest set of a fractional forest has density below one: `δ = 1 - ρ > 0`. -/
theorem dens_lt_one {x : WeightedGraph V} (hx : IsFractionalForest x) {K : Finset V}
    (hK : K.Nonempty) : dens x K < 1 := by
  have h := hx K hK
  have hc : (0 : ℝ) < K.card := by exact_mod_cast hK.card_pos
  unfold dens
  rw [div_lt_one hc]
  linarith

/-- `g(S) ≤ h|S|` on subsets of `W`, with `h = ρ - (1 - ε)`. -/
theorem gfun_le_h_mul {x : WeightedGraph V} {ε : ℝ} {W K : Finset V} (hK : IsDensest x W K)
    {S : Finset V} (hS : S ⊆ W) : gfun x ε S ≤ (dens x K - (1 - ε)) * S.card := by
  have := mass_le_dens_mul hK hS
  unfold gfun; nlinarith

/-- **Localization** (`lem:densest-deletion-core`). If `D(W) > 0` and `K` is densest in `W`,
then `h > 0`, `δ > 0`, `D(K) = g(K) = h|K|`, and `h ≥ D(W)/|W|`. -/
theorem densest_core {x : WeightedGraph V} (hx : IsFractionalForest x) {ε : ℝ}
    {W K : Finset V} (hK : IsDensest x W K) (hD : 0 < Dpot x ε W) :
    0 < dens x K - (1 - ε) ∧ 0 < 1 - dens x K ∧
      Dpot x ε K = gfun x ε K ∧ gfun x ε K = (dens x K - (1 - ε)) * K.card ∧
      Dpot x ε W / W.card ≤ dens x K - (1 - ε) := by
  set h := dens x K - (1 - ε) with hh
  obtain ⟨S, hSW, hS⟩ := exists_Dpot_eq x ε W
  have hSne : S.Nonempty := by
    rcases S.eq_empty_or_nonempty with rfl | h'
    · rw [gfun_empty] at hS; linarith
    · exact h'
  have hgS := gfun_le_h_mul (ε := ε) hK hSW
  have hScard : (0 : ℝ) < S.card := by exact_mod_cast hSne.card_pos
  have hpos : 0 < h := by
    by_contra hneg
    have hneg' : h ≤ 0 := not_lt.1 hneg
    nlinarith
  have hgK : gfun x ε K = h * K.card := by
    unfold gfun; rw [mass_eq_dens_mul x hK.2.1]; ring
  have hDK : Dpot x ε K = gfun x ε K := by
    apply le_antisymm _ (gfun_le_Dpot x ε (subset_refl K))
    rw [Dpot_le_iff]
    intro T hT
    have := gfun_le_h_mul (ε := ε) hK (hT.trans hK.1)
    have hTK : (T.card : ℝ) ≤ K.card := by exact_mod_cast card_le_card hT
    rw [hgK]; nlinarith
  have hWcard : (0 : ℝ) < W.card := by
    exact_mod_cast (hSne.mono hSW).card_pos
  refine ⟨hpos, sub_pos.2 (dens_lt_one hx hK.2.1), hDK, hgK, ?_⟩
  rw [div_le_iff₀ hWcard, ← hS]
  have : (S.card : ℝ) ≤ W.card := by exact_mod_cast card_le_card hSW
  nlinarith

end Densest

/-! ## Sums over a vertex type with one auxiliary vertex -/

section OptionSums

variable {U : Type*} [Fintype U] [DecidableEq U]

theorem sum_finset_option {S : Finset (Option U)} (hS : none ∉ S) (F : Option U → ℝ) :
    ∑ a ∈ S, F a = ∑ u ∈ univ.filter (fun u => some u ∈ S), F (some u) := by
  have h1 : ∑ a ∈ S, F a = ∑ a, if a ∈ S then F a else 0 := by
    rw [← sum_filter]; congr 1; ext; simp
  rw [h1, Fintype.sum_option, sum_filter]
  simp [hS]

theorem sum_compl_option {S : Finset (Option U)} (hS : none ∉ S) (F : Option U → ℝ) :
    ∑ a ∈ Sᶜ, F a = F none + ∑ u ∈ univ.filter (fun u => some u ∉ S), F (some u) := by
  have h1 : ∑ a ∈ Sᶜ, F a = ∑ a, if a ∉ S then F a else 0 := by
    rw [← sum_filter]; congr 1; ext; simp
  rw [h1, Fintype.sum_option, sum_filter]
  simp [hS]

theorem nonempty_filter_some {S : Finset (Option U)} (hS : none ∉ S) (hne : S.Nonempty) :
    (univ.filter (fun u => some u ∈ S)).Nonempty := by
  obtain ⟨a, ha⟩ := hne
  cases a with
  | none => exact absurd ha hS
  | some u => exact ⟨u, by simp [ha]⟩

end OptionSums

/-! ## Orientation with uniform out-degree -/

section Orientation

open DirectedCertificate Certificate

variable {U : Type*} [Fintype U] [DecidableEq U]

omit [Fintype U] [DecidableEq U] in
/-- Twice the internal mass, split by rows. -/
theorem mass_eq_sum_half (x : WeightedGraph U) (A : Finset U) :
    mass x A = ∑ u ∈ A, ∑ v ∈ A, x.w u v / 2 := by
  unfold mass; rw [sum_div]; exact sum_congr rfl fun u _ => by rw [sum_div]

/-- The orientation network: arcs `u → v` of capacity `x_{uv}/2` and arcs `u → t` of
capacity `ρ` to an auxiliary sink `t = none`. -/
noncomputable def orientNet (x : WeightedGraph U) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    WeightedDiGraph (Option U) where
  c a b := match a, b with
    | some u, some v => x.w u v / 2
    | some _, none => ρ
    | none, _ => 0
  nonneg a b := by
    rcases a with _ | u <;> rcases b with _ | v
    · exact le_refl 0
    · exact le_refl 0
    · exact hρ
    · exact div_nonneg (x.nonneg u v) zero_le_two
  diag a := by
    rcases a with _ | u
    · rfl
    · show x.w u u / 2 = 0; rw [x.diag, zero_div]

/-- **Orientation with out-degree exactly `ρ`.** If `x(E(S)) ≤ ρ|S|` for every `S` and
`x(E(U)) = ρ|U|`, the pair weights split as `y_{uv} + y_{vu} = x_{uv}` with `y ≥ 0` and
`d⁺_y(u) = ρ` at every vertex. -/
theorem exists_orientation (x : WeightedGraph U) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hdens : ∀ S : Finset U, mass x S ≤ ρ * S.card)
    (htot : mass x univ = ρ * Fintype.card U) :
    ∃ y : U → U → ℝ, (∀ u v, 0 ≤ y u v) ∧ (∀ u v, y u v + y v u = x.w u v) ∧
      ∀ u, ∑ v, y u v = ρ := by
  set G := orientNet x ρ hρ with hG
  let b : Option U → ℝ := fun a => match a with
    | some u => ∑ v, x.w u v / 2
    | none => 0
  have hb : ∀ a, 0 ≤ b a := by
    rintro (_ | u)
    · exact le_refl 0
    · exact sum_nonneg fun v _ => div_nonneg (x.nonneg u v) zero_le_two
  have hcut : ∀ S : Finset (Option U), Disjoint S {none} → ∑ a ∈ S, b a ≤ G.out S := by
    intro S hS
    have hnS : none ∉ S := fun h => disjoint_left.1 hS h (mem_singleton_self _)
    set A := univ.filter (fun u => some u ∈ S) with hA
    have hAc : univ.filter (fun u => some u ∉ S) = Aᶜ := by ext; simp [hA]
    have hout : G.out S = ∑ u ∈ A, (ρ + ∑ v ∈ Aᶜ, x.w u v / 2) := by
      unfold WeightedDiGraph.out
      rw [sum_finset_option hnS, ← hA]
      refine sum_congr rfl fun u _ => ?_
      rw [sum_compl_option hnS, hAc]
      rfl
    rw [hout, sum_finset_option hnS, ← hA]
    have hrow : ∀ u ∈ A, b (some u) = ∑ v ∈ A, x.w u v / 2 + ∑ v ∈ Aᶜ, x.w u v / 2 :=
      fun u _ => (sum_add_sum_compl A _).symm
    rw [sum_congr rfl hrow, sum_add_distrib, sum_add_distrib, ← mass_eq_sum_half]
    have := hdens A
    rw [sum_const, nsmul_eq_mul]
    linarith
  obtain ⟨f, ⟨hflow, hcap⟩, hsup, -⟩ := (G.supply_iff b hb {none}).1 hcut
  refine ⟨fun u v => x.w u v / 2 - f (some u) (some v), ?_, ?_, ?_⟩
  · intro u v
    have := hcap (some u) (some v)
    exact sub_nonneg.2 this
  · intro u v
    have := hflow (some u) (some v)
    simp only
    rw [this, x.symm v u]; ring
  · -- out-degree equals the flow into the sink
    have hφ : ∀ u, ∑ v, (x.w u v / 2 - f (some u) (some v)) = f (some u) none := by
      intro u
      have h := hsup (some u) (by simp)
      unfold netOut at h
      rw [Fintype.sum_option] at h
      rw [sum_sub_distrib]
      simp only [b] at h
      linarith
    have hle : ∀ u ∈ (univ : Finset U), f (some u) none ≤ ρ := fun u _ => hcap (some u) none
    have hsum : ∑ u, f (some u) none = ∑ _u : U, ρ := by
      rw [← sum_congr rfl fun u _ => hφ u, sum_const, card_univ, nsmul_eq_mul, mul_comm,
        ← htot, mass_eq_sum_half]
      simp only [sum_sub_distrib]
      have hzero : ∑ u, ∑ v, f (some u) (some v) = 0 := by
        have h2 : ∑ u, ∑ v, f (some u) (some v) = ∑ u, ∑ v, f (some v) (some u) :=
          sum_comm
        have h3 : ∑ u, ∑ v, f (some v) (some u) = -∑ u, ∑ v, f (some u) (some v) := by
          rw [← sum_neg_distrib]
          exact sum_congr rfl fun u _ => by
            rw [← sum_neg_distrib]; exact sum_congr rfl fun v _ => hflow (some u) (some v)
        linarith
      rw [hzero, sub_zero]
    intro u
    rw [hφ u]
    exact (sum_eq_sum_iff_of_le hle).1 hsum u (mem_univ u)

end Orientation

/-! ## Uniform roots (`lem:uniform-roots`) -/

section UniformRoots

open DirectedCertificate Certificate

variable {U : Type*} [Fintype U] [DecidableEq U]

omit [Fintype U] [DecidableEq U] in
/-- An orientation of `x` has internal arc mass `x(E(A))` on every `A`. -/
theorem sum_orient_eq_mass {x : WeightedGraph U} {y : U → U → ℝ}
    (hy : ∀ u v, y u v + y v u = x.w u v) (A : Finset U) :
    ∑ u ∈ A, ∑ v ∈ A, y u v = mass x A := by
  have h : ∑ u ∈ A, ∑ v ∈ A, x.w u v =
      ∑ u ∈ A, ∑ v ∈ A, y u v + ∑ u ∈ A, ∑ v ∈ A, y v u := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun u _ => by rw [← sum_add_distrib]; exact sum_congr rfl fun v _ => (hy u v).symm
  have h2 : ∑ u ∈ A, ∑ v ∈ A, y v u = ∑ u ∈ A, ∑ v ∈ A, y u v := sum_comm
  unfold mass
  linarith

/-- **Deletion-loss identity on the core** (in-arc form). For an orientation `y` of `x` with
out-degree `ρ`, `x(E(U)) - x(E(U ∖ T)) = y(δ⁻(T)) + ρ|T|`. -/
theorem mass_sub_mass_compl {x : WeightedGraph U} {y : U → U → ℝ} {ρ : ℝ}
    (hy : ∀ u v, y u v + y v u = x.w u v) (hdeg : ∀ u, ∑ v, y u v = ρ) (T : Finset U) :
    mass x univ - mass x Tᶜ = inWeight y T + ρ * T.card := by
  rw [← sum_orient_eq_mass hy, ← sum_orient_eq_mass hy, inWeight]
  rw [← sum_add_sum_compl T (fun u => ∑ v, y u v)]
  have h1 : ∑ u ∈ Tᶜ, ∑ v, y u v = ∑ u ∈ Tᶜ, ∑ v ∈ T, y u v + ∑ u ∈ Tᶜ, ∑ v ∈ Tᶜ, y u v := by
    rw [← sum_add_distrib]; exact sum_congr rfl fun u _ => (sum_add_sum_compl T _).symm
  have h2 : ∑ u ∈ T, ∑ v, y u v = ρ * T.card := by
    rw [sum_congr rfl fun u _ => hdeg u, sum_const, nsmul_eq_mul, mul_comm]
  rw [h1, h2]; ring

/-- The rooted forest left after deleting the auxiliary root `none` from an in-arborescence
of `Option U` rooted at `none`. -/
def forestOf (T : InArb (none : Option U)) : RootedForest U where
  parent u := (T.1 (some u)).join
  acyclic u := by
    have hp := mem_inArbs.1 T.2
    set Q : Option U → Option U := fun o => o.bind fun u => (T.1 (some u)).join with hQ
    have claim : ∀ n (o : Option U), Q^[n] o = none ∨
        Option.map some (Q^[n] o) = (parentStep T.1)^[n] (Option.map some o) := by
      intro n o
      induction n with
      | zero => right; rfl
      | succ n ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        rcases ih with h | h
        · left; rw [h]; rfl
        · cases hq : Q^[n] o with
          | none => left; rfl
          | some w =>
            rw [hq] at h
            rw [← h]
            simp only [hQ, Option.bind_some, Option.map_some, parentStep]
            rcases T.1 (some w) with _ | _ | c <;> simp
    obtain ⟨n, hn⟩ := hp.acyclic (some u)
    refine ⟨n, ?_⟩
    rcases claim n (some u) with h | h
    · exact h
    · rw [Option.map_some, hn] at h
      exact Option.map_eq_none_iff.1 h

/-- **Uniform roots on a densest set** (`lem:uniform-roots`). On a nonempty vertex type, if
`x` is a fractional forest with `x(E(S)) ≤ ρ|S|` for all `S` and `x(E(U)) = ρ|U|`, there is a
probability distribution over rooted forests (arcs toward the roots) whose arc marginals
reproduce `x` exactly, with out-degree `ρ` and root marginal `1 - ρ` at every vertex. -/
theorem uniform_roots [Nonempty U] (x : WeightedGraph U) (hx : IsFractionalForest x) {ρ : ℝ}
    (hdens : ∀ S : Finset U, mass x S ≤ ρ * S.card)
    (htot : mass x univ = ρ * Fintype.card U) :
    ∃ (p : InArb (none : Option U) → ℝ),
      (∀ j, 0 ≤ p j) ∧ ∑ j, p j = 1 ∧
      (∀ u v, arcVec p forestOf u v + arcVec p forestOf v u = x.w u v) ∧
      (∀ u, ∑ v, arcVec p forestOf u v = ρ) ∧
      ∀ u, rootVec p forestOf u = 1 - ρ := by
  have hcard : (0 : ℝ) < Fintype.card U := by exact_mod_cast Fintype.card_pos
  have hρ0 : 0 ≤ ρ := by
    have := mass_nonneg x univ
    rw [htot] at this
    exact nonneg_of_mul_nonneg_left this hcard
  have hδ : 0 ≤ 1 - ρ := by
    have := hx univ univ_nonempty
    rw [htot, card_univ] at this
    nlinarith
  obtain ⟨y, hy0, hy, hdeg⟩ := exists_orientation x hρ0 hdens htot
  have hydiag : ∀ u, y u u = 0 := by
    intro u
    have := hy u u
    rw [x.diag] at this
    linarith [hy0 u u]
  -- the augmented network with the auxiliary root `none`
  let H : WeightedDiGraph (Option U) :=
    { c := fun a b => match a, b with
        | some u, some v => y u v
        | some _, none => 1 - ρ
        | none, _ => 0
      nonneg := by
        intro a b
        rcases a with _ | u <;> rcases b with _ | v
        · exact le_refl 0
        · exact le_refl 0
        · exact hδ
        · exact hy0 u v
      diag := by
        rintro (_ | u)
        · rfl
        · exact hydiag u }
  have hcut : ∀ S : Finset (Option U), S.Nonempty → none ∉ S → 1 ≤ H.out S := by
    intro S hSne hnS
    set A := univ.filter (fun u => some u ∈ S) with hA
    have hAc : univ.filter (fun u => some u ∉ S) = Aᶜ := by ext; simp [hA]
    have hout : H.out S = ∑ u ∈ A, ((1 - ρ) + ∑ v ∈ Aᶜ, y u v) := by
      unfold WeightedDiGraph.out
      rw [sum_finset_option hnS, ← hA]
      refine sum_congr rfl fun u _ => ?_
      rw [sum_compl_option hnS, hAc]
    have hrow : ∀ u ∈ A, ∑ v ∈ Aᶜ, y u v = ρ - ∑ v ∈ A, y u v := by
      intro u _
      have := sum_add_sum_compl A (y u)
      rw [hdeg u] at this
      linarith
    have hsum : ∑ u ∈ A, ((1 - ρ) + ∑ v ∈ Aᶜ, y u v) = ∑ u ∈ A, (1 - ∑ v ∈ A, y u v) :=
      sum_congr rfl fun u hu => by rw [hrow u hu]; ring
    rw [hout, hsum, sum_sub_distrib, sum_orient_eq_mass hy, sum_const, nsmul_eq_mul, mul_one]
    have := hx A (nonempty_filter_some hnS hSne)
    linarith
  obtain ⟨a, ha0, ha1, hload⟩ := exists_inArb_packing H none 1 zero_le_one hcut
  -- saturation of every arc capacity
  have hsat : ∀ (u : U) (c : Option U), load a (some u) c = H.c (some u) c := by
    intro u
    have hle : ∀ c ∈ (univ : Finset (Option U)), load a (some u) c ≤ H.c (some u) c :=
      fun c _ => hload _ _
    have hone : ∀ T : InArb (none : Option U),
        ∑ c, (if T.1 (some u) = some c then (1 : ℝ) else 0) = 1 := by
      intro T
      have hne : T.1 (some u) ≠ none := (mem_inArbs.1 T.2).nonroot (some u) (by simp)
      obtain ⟨c0, hc0⟩ := Option.ne_none_iff_exists'.1 hne
      simp [hc0]
    have hL : ∑ c, load a (some u) c = 1 := by
      unfold load
      rw [sum_comm]
      simp_rw [← mul_sum, hone, mul_one]
      exact ha1
    have hC : ∑ c, H.c (some u) c = 1 := by
      rw [Fintype.sum_option]
      show (1 - ρ) + ∑ v, y u v = 1
      rw [hdeg u]; ring
    intro c
    exact (sum_eq_sum_iff_of_le hle).1 (hL.trans hC.symm) c (mem_univ c)
  have harc : ∀ u w, arcVec a forestOf u w = y u w := by
    intro u w
    have : load a (some u) (some w) = y u w := hsat u (some w)
    unfold load at this
    unfold arcVec
    rw [← this]
    refine sum_congr rfl fun T _ => ?_
    simp only [forestOf, Option.join_eq_some_iff]
  have hrootv : ∀ u, rootVec a forestOf u = 1 - ρ := by
    intro u
    have : load a (some u) none = 1 - ρ := hsat u none
    unfold load at this
    unfold rootVec
    refine (sum_congr rfl fun T _ => ?_).trans this
    have hne : T.1 (some u) ≠ none := (mem_inArbs.1 T.2).nonroot (some u) (by simp)
    obtain ⟨c0, hc0⟩ := Option.ne_none_iff_exists'.1 hne
    cases c0 <;> simp [forestOf, hc0]
  refine ⟨a, ha0, ha1, fun u v => by rw [harc, harc, hy], fun u => ?_, hrootv⟩
  simp_rw [harc]; exact hdeg u

end UniformRoots

/-! ## Deletion progress (`thm:deletion-progress`) -/

section Progress

open DirectedCertificate

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The weighting restricted to the vertex subtype of `K` (the repository's `onVertices`
lives in `Type`; this is the universe-polymorphic copy used here). -/
def restrictTo (x : WeightedGraph V) (K : Finset V) : WeightedGraph K where
  w u v := x.w u.1 v.1
  symm _ _ := x.symm _ _
  nonneg _ _ := x.nonneg _ _
  diag _ := x.diag _

omit [Fintype V] [DecidableEq V] in
/-- Ambient/restricted internal-mass conversion. -/
theorem mass_restrictTo (x : WeightedGraph V) (K : Finset V) (S : Finset K) :
    mass (restrictTo x K) S = mass x (S.map (Function.Embedding.subtype (· ∈ K))) := by
  unfold mass
  rw [sum_map]
  simp_rw [sum_map]
  rfl

omit [Fintype V] [DecidableEq V] in
theorem map_filter_subtype (K : Finset V) (P : V → Prop) [DecidablePred P] :
    (univ.filter (fun u : K => P u.1)).map (Function.Embedding.subtype (· ∈ K)) =
      K.filter P := by
  ext v
  simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨u, hu, rfl⟩; exact ⟨u.2, hu⟩
  · rintro ⟨hv, hP⟩; exact ⟨⟨v, hv⟩, hP, rfl⟩

omit [Fintype V] [DecidableEq V] in
theorem map_univ_subtype (K : Finset V) :
    (univ : Finset K).map (Function.Embedding.subtype (· ∈ K)) = K := by
  have := map_filter_subtype K (fun _ => True)
  simpa using this

/-- **Deletion-loss identity** (`g(K) − g(K ∖ T) = y(δ⁻(T)) + h|T|`), stated on the vertex
type of the core: for an orientation `y` of `x` with out-degree `ρ`. -/
theorem loss_eq {U : Type*} [Fintype U] [DecidableEq U] {x : WeightedGraph U}
    {y : U → U → ℝ} {ρ : ℝ} (ε : ℝ) (hy : ∀ u v, y u v + y v u = x.w u v)
    (hdeg : ∀ u, ∑ v, y u v = ρ) (T : Finset U) :
    gfun x ε univ - gfun x ε Tᶜ = inWeight y T + (ρ - (1 - ε)) * T.card := by
  have h := mass_sub_mass_compl hy hdeg T
  have hc : ((Tᶜ).card : ℝ) = (univ : Finset U).card - T.card := by
    rw [card_compl, card_univ, Nat.cast_sub (card_le_univ T)]
  unfold gfun
  rw [hc]
  linarith

omit [Fintype V] [DecidableEq V] in
/-- On a densest set with `h ≥ 0`, `D(K) = g(K)`. -/
theorem Dpot_densest_eq {x : WeightedGraph V} {ε : ℝ} {W K : Finset V}
    (hK : IsDensest x W K) (hh : 0 ≤ dens x K - (1 - ε)) : Dpot x ε K = gfun x ε K := by
  apply le_antisymm _ (gfun_le_Dpot x ε (subset_refl K))
  rw [Dpot_le_iff]
  intro T hT
  have h1 := gfun_le_h_mul (ε := ε) hK (hT.trans hK.1)
  have hTK : (T.card : ℝ) ≤ K.card := by exact_mod_cast card_le_card hT
  have hgK : gfun x ε K = (dens x K - (1 - ε)) * K.card := by
    unfold gfun; rw [mass_eq_dens_mul x hK.2.1]; ring
  rw [hgK]; nlinarith

/-- **Deletion progress, stronger form** (`thm:deletion-progress`). For a fractional forest
and a densest nonempty `K ⊆ W` with `h = ρ − (1 − ε) > 0` (`ρ = x(E(K))/|K|`,
`δ = 1 − ρ`), some `v ∈ K` has `Δ_v(W) ≥ Δ_v(K) ≥ min{1, h/δ}`. -/
theorem deletion_progress {x : WeightedGraph V} (hx : IsFractionalForest x) {ε : ℝ}
    {W K : Finset V} (hK : IsDensest x W K) (hh : 0 < dens x K - (1 - ε)) :
    ∃ v ∈ K, gain x ε K v ≤ gain x ε W v ∧
      min 1 ((dens x K - (1 - ε)) / (1 - dens x K)) ≤ gain x ε K v := by
  set ρ := dens x K with hρdef
  set h := ρ - (1 - ε) with hhdef
  have hδ : 0 < 1 - ρ := sub_pos.2 (dens_lt_one hx hK.2.1)
  have hγ : 0 < h / (1 - ρ) := div_pos hh hδ
  have : Nonempty K := hK.2.1.to_subtype
  set e := Function.Embedding.subtype (· ∈ K) with he
  have hsubK : ∀ S : Finset K, S.map e ⊆ K := by
    intro S v hv; obtain ⟨u, -, rfl⟩ := mem_map.1 hv; exact u.2
  have hxK : IsFractionalForest (restrictTo x K) := by
    intro S hS
    rw [mass_restrictTo, ← card_map e]
    exact hx _ (map_nonempty.2 hS)
  have hdK : ∀ S : Finset K, mass (restrictTo x K) S ≤ ρ * S.card := by
    intro S
    rw [mass_restrictTo, ← card_map e]
    exact mass_le_dens_mul hK ((hsubK S).trans hK.1)
  have htotK : mass (restrictTo x K) univ = ρ * Fintype.card K := by
    rw [mass_restrictTo, map_univ_subtype, Fintype.card_coe, mass_eq_dens_mul x hK.2.1]
  obtain ⟨p, hp0, hp1, hpair, hdeg, hroot⟩ := uniform_roots (restrictTo x K) hxK hdK htotK
  obtain ⟨v0, hv0⟩ := root_concentration p forestOf hp0 hp1 hγ
  refine ⟨v0.1, v0.2, gain_mono x ε hK.1 v0.2, ?_⟩
  have hDK : Dpot x ε K = gfun x ε K := Dpot_densest_eq hK hh.le
  obtain ⟨S, hS, hSeq⟩ := exists_Dpot_eq x ε (K.erase v0.1)
  have hSK : S ⊆ K := hS.trans (erase_subset _ _)
  set T' : Finset K := univ.filter (fun u : K => u.1 ∉ S) with hT'
  have hT'c : T'ᶜ = univ.filter (fun u : K => u.1 ∈ S) := by ext u; simp [hT']
  have hmapc : T'ᶜ.map e = S := by
    ext v
    simp only [hT'c, he, mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact hu
    · intro hv; exact ⟨⟨v, hSK hv⟩, hv, rfl⟩
  have hv0T : v0 ∈ T' := by
    simp only [hT', mem_filter, mem_univ, true_and]
    intro hv
    have := hS hv
    simp at this
  have hcardT : (T'.card : ℝ) = K.card - S.card := by
    have h1 := card_compl_add_card T'
    rw [← card_map e, hmapc, Fintype.card_coe] at h1
    have h2 : ((T'.card : ℕ) : ℝ) + S.card = K.card := by exact_mod_cast (by omega : T'.card + S.card = K.card)
    linarith
  have hloss := mass_sub_mass_compl (x := restrictTo x K) hpair hdeg T'
  rw [mass_restrictTo, mass_restrictTo, map_univ_subtype, hmapc] at hloss
  have hsw : setWeight (rootVec p forestOf) T' = (1 - ρ) * T'.card := by
    unfold setWeight
    rw [sum_congr rfl fun u _ => hroot u, sum_const, nsmul_eq_mul, mul_comm]
  have hconc := hv0 T' hv0T
  rw [hsw] at hconc
  have hcancel : h / (1 - ρ) * ((1 - ρ) * T'.card) = h * T'.card := by
    field_simp
  unfold gain
  rw [hDK, ← hSeq]
  unfold gfun
  rw [hcancel] at hconc
  rw [hcardT] at hconc hloss
  simp only [hhdef] at hconc
  nlinarith

omit [Fintype V] [DecidableEq V] in
/-- `D(W) > 0` forces `W` to be nonempty. -/
theorem nonempty_of_Dpot_pos {x : WeightedGraph V} {ε : ℝ} {W : Finset V}
    (hD : 0 < Dpot x ε W) : W.Nonempty := by
  rcases W.eq_empty_or_nonempty with rfl | h
  · have : Dpot x ε ∅ ≤ 0 := (Dpot_le_iff x ε ∅ 0).2 fun S hS => by
      rw [subset_empty.1 hS, gfun_empty]
    linarith
  · exact h

/-- **Multiplicative progress** (`eq:proved-deletion-progress`):
`max_{v ∈ W} Δ_v(W) ≥ D(W)/(ε|W|)` whenever `D(W) > 0`. -/
theorem exists_gain_ge_div {x : WeightedGraph V} (hx : IsFractionalForest x) {ε : ℝ}
    {W : Finset V} (hD : 0 < Dpot x ε W) :
    ∃ v ∈ W, Dpot x ε W / (ε * W.card) ≤ gain x ε W v := by
  obtain ⟨K, hK⟩ := exists_densest x (nonempty_of_Dpot_pos hD)
  obtain ⟨hh, hδ, -, -, hDW⟩ := densest_core hx hK hD
  obtain ⟨v, hvK, hmono, hmin⟩ := deletion_progress hx hK hh
  refine ⟨v, hK.1 hvK, ?_⟩
  set h := dens x K - (1 - ε)
  set δ := 1 - dens x K
  have hε : ε = h + δ := by simp only [h, δ]; ring
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hW : (0 : ℝ) < W.card := by exact_mod_cast (nonempty_of_Dpot_pos hD).card_pos
  have h1 : Dpot x ε W / (ε * W.card) ≤ h / ε := by
    rw [mul_comm, ← div_div]
    exact div_le_div_of_nonneg_right hDW hεpos.le
  have h2 : h / ε ≤ min 1 (h / δ) := by
    rw [hε]
    refine le_min ((div_le_one (by linarith)).2 (by linarith)) ?_
    exact div_le_div_of_nonneg_left hh.le hδ (by linarith)
  linarith

/-- **Unit progress** (W4 step 2; frozen interface). While the target
`x(E(S)) ≤ (1 − 1/k)|S|` fails inside `W`, some vertex of `W` decreases the potential
`D` at `ε = 2/k` by at least one. -/
theorem unit_progress {V : Type*} [Fintype V] [DecidableEq V] {x : WeightedGraph V}
    (hx : IsFractionalForest x) {k : ℕ} (hk : 3 ≤ k) {W : Finset V}
    (hviol : ∃ S ⊆ W, (1 - 1 / (k : ℝ)) * S.card < mass x S) :
    ∃ v ∈ W, 1 ≤ gain x (2 / k) W v := by
  obtain ⟨S, hSW, hS⟩ := hviol
  have hSne : S.Nonempty := by
    rcases S.eq_empty_or_nonempty with rfl | h
    · simp at hS
    · exact h
  obtain ⟨K, hK⟩ := exists_densest x (hSne.mono hSW)
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hScard : (0 : ℝ) < S.card := by exact_mod_cast hSne.card_pos
  have hρS : 1 - 1 / (k : ℝ) < dens x S := by
    unfold dens; rw [lt_div_iff₀ hScard]; exact hS
  have hρ : 1 - 1 / (k : ℝ) < dens x K := lt_of_lt_of_le hρS (hK.2.2 S hSW hSne)
  have hδpos : 0 < 1 - dens x K := sub_pos.2 (dens_lt_one hx hK.2.1)
  have hk1 : (0 : ℝ) < 1 / k := by positivity
  have hk2 : (2 : ℝ) / k = 2 * (1 / k) := by ring
  have hh : 0 < dens x K - (1 - 2 / (k : ℝ)) := by rw [hk2]; linarith
  have hhδ : 1 - dens x K < dens x K - (1 - 2 / (k : ℝ)) := by rw [hk2]; linarith
  obtain ⟨v, hvK, hmono, hmin⟩ := deletion_progress hx hK hh
  have hone : min 1 ((dens x K - (1 - 2 / (k : ℝ))) / (1 - dens x K)) = 1 :=
    min_eq_left ((one_le_div hδpos).2 hhδ.le)
  rw [hone] at hmin
  exact ⟨v, hK.1 hvK, hmin.trans hmono⟩

end Progress

end FractionalForest

end CutQueryComplexity
