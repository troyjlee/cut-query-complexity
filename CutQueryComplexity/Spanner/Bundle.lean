import CutQueryComplexity.Spanner.Trial

/-! # A bundle of pair-disjoint spanners (D2; source `lem:leverage`)

Starting from the current support `E'`, spanner `j` is a completed trial on the residual
`resid j`, and `resid (j + 1) = resid j \ S_j`. Only the selected pairs are deleted between
calls; the block deletions inside a trial belong to that trial. The spanners are pair-disjoint
(`spanners_disjoint`), and a pair left after `t` calls was present for every call.

`bundle_dominated`: lengths are `ℓ_f = 1/w_f`, keys are ordered by length then a unique ID, and
conductances are `ω_f = s c_f w_f` with `1 ≤ c_f` on `E'`. For every remaining pair
`e = uv ∈ resid t` with `c_e ≤ C`, and every real vector,

  `ω_e (x_u − x_v)² ≤ (C (2k − 1) / t) Σ_{f∈E'} ω_f (x_a − x_b)²`.

This holds for every coin sequence, empty or disconnected supports, and zero public weights off
the support.
-/

namespace CutQueryComplexity
namespace Spanner

open Finset Spectral

noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V] {κ : Type} [LinearOrder κ] (key : Sym2 V → κ)

/-- The residual support before spanner call `j`. -/
def resid (coinSeq : ℕ → ℕ → V → Bool) (E' : Finset (Sym2 V)) (k : ℕ) : ℕ → Finset (Sym2 V)
  | 0 => E'
  | j + 1 => resid coinSeq E' k j \ (trial key (coinSeq j) (resid coinSeq E' k j) k).H

/-- Spanner call `j`. -/
def spanner (coinSeq : ℕ → ℕ → V → Bool) (E' : Finset (Sym2 V)) (k j : ℕ) : Finset (Sym2 V) :=
  (trial key (coinSeq j) (resid key coinSeq E' k j) k).H

variable {key}

theorem resid_succ (coinSeq : ℕ → ℕ → V → Bool) (E' : Finset (Sym2 V)) (k j : ℕ) :
    resid key coinSeq E' k (j + 1) = resid key coinSeq E' k j \ spanner key coinSeq E' k j := rfl

theorem resid_anti (coinSeq : ℕ → ℕ → V → Bool) (E' : Finset (Sym2 V)) (k : ℕ) {i j : ℕ}
    (h : i ≤ j) : resid key coinSeq E' k j ⊆ resid key coinSeq E' k i := by
  induction h with
  | refl => exact subset_rfl
  | step _ ih => rw [resid_succ]; exact sdiff_subset.trans ih

theorem resid_subset (coinSeq : ℕ → ℕ → V → Bool) (E' : Finset (Sym2 V)) (k j : ℕ) :
    resid key coinSeq E' k j ⊆ E' := resid_anti coinSeq E' k (Nat.zero_le j)

variable {ℓ : Sym2 V → ℝ}

theorem spanner_subset_resid (hinj : Function.Injective key)
    (hmono : ∀ e f, key f ≤ key e → ℓ f ≤ ℓ e) {E' : Finset (Sym2 V)}
    (hE' : ∀ a b, s(a, b) ∈ E' → a ≠ b) (coinSeq : ℕ → ℕ → V → Bool) {k : ℕ} (hk : 1 ≤ k)
    (j : ℕ) : spanner key coinSeq E' k j ⊆ resid key coinSeq E' k j :=
  (trial_stretch (ℓ := ℓ) hinj hmono
    (fun a b h => hE' a b (resid_subset coinSeq E' k j h)) (coinSeq j) hk).1

theorem spanners_disjoint (hinj : Function.Injective key)
    (hmono : ∀ e f, key f ≤ key e → ℓ f ≤ ℓ e) {E' : Finset (Sym2 V)}
    (hE' : ∀ a b, s(a, b) ∈ E' → a ≠ b) (coinSeq : ℕ → ℕ → V → Bool) {k : ℕ} (hk : 1 ≤ k)
    (J : Finset ℕ) : (J : Set ℕ).PairwiseDisjoint (spanner key coinSeq E' k) := by
  have key_lemma : ∀ i j, i < j →
      Disjoint (spanner key coinSeq E' k i) (spanner key coinSeq E' k j) := by
    intro i j hij
    have hj : spanner key coinSeq E' k j ⊆ resid key coinSeq E' k (i + 1) :=
      (spanner_subset_resid (ℓ := ℓ) hinj hmono hE' coinSeq hk j).trans
        (resid_anti coinSeq E' k hij)
    rw [resid_succ] at hj
    exact disjoint_of_subset_right hj disjoint_sdiff
  intro i _ j _ hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact key_lemma i j h
  · exact (key_lemma j i h).symm

/-- **Bundle domination for the remaining pairs**, for every coin sequence. -/
theorem bundle_dominated (hinj : Function.Injective key) {w c : Sym2 V → ℝ}
    (hmono : ∀ e f, key f ≤ key e → 1 / w f ≤ 1 / w e) (hw0 : ∀ f, 0 ≤ w f)
    {E' : Finset (Sym2 V)} (hE' : ∀ a b, s(a, b) ∈ E' → a ≠ b) (hw : ∀ f ∈ E', 0 < w f)
    (hc : ∀ f ∈ E', 1 ≤ c f) {s : ℝ} (hs : 0 < s) (coinSeq : ℕ → ℕ → V → Bool)
    {k t : ℕ} (hk : 1 ≤ k) (ht : 1 ≤ t) {C : ℝ} {u v : V}
    (he : s(u, v) ∈ resid key coinSeq E' k t) (hcC : c s(u, v) ≤ C) (x : V → ℝ) :
    s * c s(u, v) * w s(u, v) * pairSq x s(u, v) ≤
      C * (2 * k - 1 : ℕ) / t * energy (fun f => s * c f * w f) E' x := by
  have hJ : (range t).Nonempty := nonempty_range_iff.mpr (by omega)
  have hcard : ((range t).card : ℝ) = t := by simp
  have := pair_dominated (range t) hJ (spanner key coinSeq E' k)
    (spanners_disjoint (ℓ := fun f => 1 / w f) hinj hmono hE' coinSeq hk _)
    (fun j _ => (spanner_subset_resid (ℓ := fun f => 1 / w f) hinj hmono hE' coinSeq hk j).trans
      (resid_subset coinSeq E' k j))
    hs hw hc (resid_subset coinSeq E' k t he) hcC (α := ((2 * k - 1 : ℕ) : ℝ)) (fun j hj => by
      have hej : s(u, v) ∈ resid key coinSeq E' k j :=
        resid_anti coinSeq E' k (mem_range.mp hj).le he
      obtain ⟨p, hp, hsum⟩ := trial_path (ℓ := fun f => 1 / w f) hinj hmono
        (fun f => one_div_nonneg.mpr (hw0 f))
        (fun a b h => hE' a b (resid_subset coinSeq E' k j h)) (coinSeq j) hk hej
      refine ⟨p, hp.isTrail, ?_⟩
      rw [div_eq_mul_one_div]; exact hsum) x
  rwa [hcard] at this

end

end Spanner
end CutQueryComplexity
