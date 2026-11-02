import CutQueryComplexity.Spanner.Capped
import CutQueryComplexity.Spectral.OneRound
import CutQueryComplexity.Primitive.DirectedReductions

/-! # A bundle of capped spanners (D4; source `lem:leverage`, recursion step 1–2)

`bundleQ`: run `t` amplified spanner calls (`Spanner.amp`). Call `j + 1` uses the public
predicate with every pair selected by calls `1, …, j` deleted (`delP`). It returns the list of
spanners (newest first), or `none` if any call fails.

* `bundleQ_fail_le`: failure has probability at most `t · 2^{-J}` (adaptive union bound).
* `bundleQ_valid`: every returned list is a valid bundle (`ValidBundle`). Each spanner is
  supported in the residual support of its call, has at most `capH` pairs, and has stretch `α`
  there.
* `ValidBundle.dominated`: for every remaining pair `e` of the support, and conductances
  `ω_f = s c_f w_f` with exact multiplicities `1 ≤ c_f ≤ C`,
  `ω_e (x_u − x_v)² ≤ (C α / t) Σ_f ω_f (x_a − x_b)²`. This is `Spectral.pair_dominated`
  applied to the pair-disjoint spanners of the bundle; no coin history is reconstructed.
* `multQ`: learn the multiplicity of every selected pair with three queries each, within a
  public budget (`multQ_correct`).
-/

namespace CutQueryComplexity
namespace Sparsify

open Finset Probability Spanner Spectral
open scoped ENNReal

noncomputable section

attribute [local instance 10] Classical.propDecidable

variable {V : Type} [Fintype V] [DecidableEq V] {κ : Type} [LinearOrder κ]
variable {key : Sym2 V → κ}

/-- Delete a set of pairs from a public predicate. -/
def delP (P : Sym2 V → Bool) (B : Finset (Sym2 V)) : Sym2 V → Bool :=
  fun e => P e && decide (e ∉ B)

theorem support_delP (G : DiGraph V) (P : Sym2 V → Bool) (B : Finset (Sym2 V)) :
    support G (delP P B) = support G P \ B := by
  ext e; simp [support, delP, and_assoc]

/-- The union of the spanners of a bundle. -/
def bunion (L : List (Finset (Sym2 V))) : Finset (Sym2 V) := L.foldr (· ∪ ·) ∅

omit [Fintype V] in
@[simp] theorem bunion_nil : bunion ([] : List (Finset (Sym2 V))) = ∅ := rfl
omit [Fintype V] in
@[simp] theorem bunion_cons (H : Finset (Sym2 V)) (L : List (Finset (Sym2 V))) :
    bunion (H :: L) = H ∪ bunion L := rfl

omit [Fintype V] in
theorem mem_bunion {e : Sym2 V} {L : List (Finset (Sym2 V))} :
    e ∈ bunion L ↔ ∃ H ∈ L, e ∈ H := by
  induction L with
  | nil => simp
  | cons H L ih => simp [ih]

variable (key)

/-- **`t` successive spanners**, each on the support with earlier selections deleted. -/
def bundleQ (K kq J : ℕ) (P : Sym2 V → Bool) :
    (t : ℕ) → RTree (Finset V) ℕ (Option (List (Finset (Sym2 V)))) (t * (J * capQ V K kq))
  | 0 => RTree.pure (PMF.pure (some []))
  | t + 1 => ((bundleQ K kq J P t).bind fun o => match o with
      | none => RTree.pure (PMF.pure none)
      | some L => (amp key K kq (delP P (bunion L)) J).map fun h => h.map fun H => H :: L).cast
        (by ring)

variable {key}

/-- A good spanner of a support. -/
def GoodSp (ℓ : Sym2 V → ℝ) (α : ℕ) (cap : ℕ) (E H : Finset (Sym2 V)) : Prop :=
  H ⊆ E ∧ H.card ≤ cap ∧ ∀ a b, s(a, b) ∈ E → ∃ p : (pairGraph H).Walk a b,
    p.IsPath ∧ (p.edges.map ℓ).sum ≤ α * ℓ s(a, b)

/-- A valid bundle over a support `E`, newest spanner first. -/
def ValidBundle (ℓ : Sym2 V → ℝ) (α cap : ℕ) (E : Finset (Sym2 V)) :
    List (Finset (Sym2 V)) → Prop
  | [] => True
  | H :: L => ValidBundle ℓ α cap E L ∧ GoodSp ℓ α cap (E \ bunion L) H

/-- **Bundle failure is at most `t · 2^{-J}`.** -/
theorem bundleQ_fail_le (hinj : Function.Injective key) (G : DiGraph V) {K kq J : ℕ}
    (hk : Fintype.card V ≤ 2 ^ kq) (hK : Fintype.card V ≤ 2 ^ K) (P : Sym2 V → Bool) :
    ∀ t, mass ((bundleQ key K kq J P t).eval G.out) (fun o => o = none) ≤
      t * (2⁻¹ : ℝ≥0∞) ^ J
  | 0 => by simp [bundleQ]
  | t + 1 => by
      simp only [bundleQ, RTree.eval_cast, RTree.eval_bind]
      have := mass_bind_le_add ((bundleQ key K kq J P t).eval G.out)
        (fun o => (match o with
          | none => RTree.pure (PMF.pure none)
          | some L => (amp key K kq (delP P (bunion L)) J).map fun h => h.map fun H => H :: L :
            RTree (Finset V) ℕ (Option (List (Finset (Sym2 V)))) (J * capQ V K kq)).eval G.out)
        (fun o => o = none) (fun o => o = none) (bundleQ_fail_le hinj G hk hK P t)
        (fun o ho => by
          obtain ⟨L, rfl⟩ := Option.ne_none_iff_exists'.mp ho
          simp only [RTree.eval_map, mass_map]
          refine le_trans (mass_mono _ fun h hh => ?_) ((amp_spanner hinj (ℓ := fun _ => 0)
            (fun _ _ _ => le_rfl) (fun _ => le_rfl) G hk hK (delP P (bunion L)) J).1)
          cases h with
          | none => rfl
          | some H => simp at hh)
      refine this.trans (le_of_eq ?_)
      push_cast; ring

/-- **Every returned bundle is valid.** -/
theorem bundleQ_valid (hinj : Function.Injective key) {ℓ : Sym2 V → ℝ}
    (hmono : ∀ e f, key f ≤ key e → ℓ f ≤ ℓ e) (hℓ : ∀ e, 0 ≤ ℓ e) (G : DiGraph V)
    {K kq J : ℕ} (hk : Fintype.card V ≤ 2 ^ kq) (hK : Fintype.card V ≤ 2 ^ K)
    (P : Sym2 V → Bool) :
    ∀ t L, some L ∈ ((bundleQ key K kq J P t).eval G.out).support →
      L.length = t ∧ ValidBundle ℓ (2 * K + 1) (capH V K) (support G P) L
  | 0 => by
      intro L hL
      simp only [bundleQ, RTree.eval_pure, PMF.support_pure, Set.mem_singleton_iff,
        Option.some.injEq] at hL
      subst hL; exact ⟨rfl, trivial⟩
  | t + 1 => by
      intro L hL
      simp only [bundleQ, RTree.eval_cast, RTree.eval_bind, PMF.mem_support_bind_iff] at hL
      obtain ⟨o, ho, hL⟩ := hL
      cases o with
      | none => simp at hL
      | some L' =>
          simp only [RTree.eval_map, PMF.support_map, Set.mem_image] at hL
          obtain ⟨h, hh, hhL⟩ := hL
          cases h with
          | none => simp at hhL
          | some H =>
              simp only [Option.map_some, Option.some.injEq] at hhL
              subst hhL
              obtain ⟨hlen, hval⟩ := bundleQ_valid hinj hmono hℓ G hk hK P t L' ho
              obtain ⟨hsub, hcard, hstr⟩ :=
                (amp_spanner hinj hmono hℓ G hk hK (delP P (bunion L')) J).2 H hh
              rw [support_delP] at hsub hstr
              exact ⟨by simp [hlen], hval, hsub, hcard, hstr⟩

/-! ## Bundle domination -/

omit [Fintype V] in
theorem ValidBundle.subset {ℓ : Sym2 V → ℝ} {α cap : ℕ} {E : Finset (Sym2 V)} :
    ∀ {L : List (Finset (Sym2 V))}, ValidBundle ℓ α cap E L → ∀ H ∈ L, H ⊆ E
  | [], _, H, hH => by simp at hH
  | H' :: L, ⟨hL, hH', _⟩, H, hH => by
      rcases List.mem_cons.mp hH with rfl | hH
      · exact hH'.trans sdiff_subset
      · exact ValidBundle.subset hL H hH

omit [Fintype V] in
theorem ValidBundle.pairwise {ℓ : Sym2 V → ℝ} {α cap : ℕ} {E : Finset (Sym2 V)} :
    ∀ {L : List (Finset (Sym2 V))}, ValidBundle ℓ α cap E L → L.Pairwise Disjoint
  | [], _ => List.Pairwise.nil
  | H :: L, ⟨hL, hH, _⟩ => by
      refine List.Pairwise.cons (fun H' hH' => ?_) (ValidBundle.pairwise hL)
      refine disjoint_left.mpr fun e he he' => ?_
      have := hH he
      exact (mem_sdiff.mp this).2 (mem_bunion.mpr ⟨H', hH', he'⟩)

omit [Fintype V] in
theorem ValidBundle.paths {ℓ : Sym2 V → ℝ} {α cap : ℕ} {E : Finset (Sym2 V)} :
    ∀ {L : List (Finset (Sym2 V))}, ValidBundle ℓ α cap E L → ∀ {a b : V},
      s(a, b) ∈ E \ bunion L → ∀ H ∈ L, ∃ p : (pairGraph H).Walk a b,
        p.IsPath ∧ (p.edges.map ℓ).sum ≤ α * ℓ s(a, b)
  | [], _, _, _, _, H, hH => by simp at hH
  | H' :: L, ⟨hL, _, _, hstr⟩, a, b, he, H, hH => by
      have he' : s(a, b) ∈ E \ bunion L := by
        simp only [bunion_cons, mem_sdiff, mem_union, not_or] at he ⊢
        exact ⟨he.1, he.2.2⟩
      rcases List.mem_cons.mp hH with rfl | hH
      · exact hstr a b he'
      · exact ValidBundle.paths hL he' H hH

/-- **The bundle bound for every remaining pair.** -/
theorem ValidBundle.dominated {ℓ : Sym2 V → ℝ} {α cap : ℕ} {E : Finset (Sym2 V)}
    {L : List (Finset (Sym2 V))} (hL : ValidBundle (fun f => 1 / ℓ f) α cap E L)
    (hlen : 0 < L.length) {s : ℝ} (hs : 0 < s) {w c : Sym2 V → ℝ}
    (hw : ∀ f ∈ E, 0 < w f) (hc : ∀ f ∈ E, 1 ≤ c f) (hℓw : ℓ = w) {C : ℝ} {u v : V}
    (he : s(u, v) ∈ E \ bunion L) (hcC : c s(u, v) ≤ C) (x : V → ℝ) :
    s * c s(u, v) * w s(u, v) * pairSq x s(u, v) ≤
      C * α / L.length * energy (fun f => s * c f * w f) E x := by
  subst hℓw
  have hJ : (univ : Finset (Fin L.length)).Nonempty := univ_nonempty_iff.mpr ⟨⟨0, hlen⟩⟩
  have hdisj : ((univ : Finset (Fin L.length)) : Set (Fin L.length)).PairwiseDisjoint
      fun i => L.get i := by
    intro i _ j _ hij
    have hp := List.pairwise_iff_get.mp (ValidBundle.pairwise hL)
    rcases lt_or_gt_of_ne hij with h | h
    · exact hp i j h
    · exact (hp j i h).symm
  have := pair_dominated (univ : Finset (Fin L.length)) hJ (fun i => L.get i) hdisj
    (fun i _ => ValidBundle.subset hL _ (List.get_mem L i)) hs hw hc (mem_sdiff.mp he).1 hcC
    (α := α) (fun i _ => by
      obtain ⟨p, hp, hlenp⟩ := ValidBundle.paths hL he _ (List.get_mem L i)
      refine ⟨p, hp.isTrail, ?_⟩
      rw [div_eq_mul_one_div]; exact hlenp) x
  simpa using this

/-! ## Multiplicities of the selected pairs -/

/-- Learn the multiplicities of the listed pairs, three queries each. -/
def multList : (es : List (Sym2 V)) → DTree (Finset V) ℕ (Sym2 V → ℕ) (3 * es.length)
  | [] => DTree.pure fun _ => 0
  | e :: es => ((pairQuery {e.out.1} {e.out.2}).bind fun m =>
      (multList es).map fun f => Function.update f e m).cast
        (by simp only [List.length_cons]; ring)

theorem multList_correct (G : DiGraph V) (es : List (Sym2 V)) (hes : ∀ e ∈ es, ¬ e.IsDiag)
    {e : Sym2 V} (he : e ∈ es) : (multList es).eval G.out e = symS G e := by
  induction es with
  | nil => simp at he
  | cons e' es ih =>
      simp only [multList, DTree.eval_cast, DTree.eval_bind, DTree.eval_map]
      by_cases hee : e = e'
      · subst hee
        rw [Function.update_self]
        have hne : e.out.1 ≠ e.out.2 := fun h => hes e (List.mem_cons_self ..) (by
          rw [← Quot.out_eq e]; exact Sym2.mk_isDiag_iff.mpr h)
        rw [pairQuery_eval G (disjoint_singleton.mpr hne)]
        simp only [DiGraph.pairs, sum_singleton]
        conv_rhs => rw [← Quot.out_eq e]
        rfl
      · rw [Function.update_of_ne hee]
        exact ih (fun f hf => hes f (List.mem_cons_of_mem _ hf))
          ((List.mem_cons.mp he).resolve_left hee)

/-- Learn the multiplicities of a set of pairs within the public budget `3M`. -/
def multQ (M : ℕ) (B : Finset (Sym2 V)) : DTree (Finset V) ℕ (Sym2 V → ℕ) (3 * M) :=
  if h : B.card ≤ M then (multList B.toList).weaken (by rw [length_toList]; omega)
  else DTree.pure fun _ => 0

theorem multQ_correct (G : DiGraph V) {M : ℕ} {B : Finset (Sym2 V)} (hB : B.card ≤ M)
    (hdiag : ∀ e ∈ B, ¬ e.IsDiag) {e : Sym2 V} (he : e ∈ B) :
    (multQ M B).eval G.out e = symS G e := by
  simp only [multQ, hB, ↓reduceDIte]
  rw [DTree.eval, DTree.run_weaken, ← DTree.eval]
  exact multList_correct G _ (fun f hf => hdiag f (mem_toList.mp hf)) (mem_toList.mpr he)

end

end Sparsify
end CutQueryComplexity
