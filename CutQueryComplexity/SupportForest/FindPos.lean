import CutQueryComplexity.Discovery.Normalization

/-! # Positive-mass search

`findPos dflt W m` halves a list `W` of known positive total mass `m` under a subset-sum
oracle: it queries the mass of the first half, keeps that half when its mass is positive and
otherwise the second half with the subtracted mass, and returns the surviving element with its
mass. `findPos_spec` proves, against an abstract nonnegative subset-sum oracle, that the
returned element lies in `W`, has positive mass, is returned with its exact mass, and that at
most `⌈log₂ |W|⌉` oracle calls are made. The default `dflt` is only returned on the empty list,
which cannot have positive mass.
-/

namespace CutQueryComplexity
namespace SupportForest

open Search Search.Comp Discovery Finset

variable {V : Type} [DecidableEq V]

/-- On a list `W` of known positive total mass `m`, halve repeatedly, querying the first half
and deducing the second, and return an element of positive mass with its mass. -/
noncomputable def findPos (dflt : V) (W : List V) (m : ℝ) : Comp (Finset V) ℝ (V × ℝ) :=
  if W.length ≤ 1 then Comp.pure (W.headD dflt, m) else
    (ask (W.take ((W.length + 1) / 2)).toFinset).bind fun a =>
      if 0 < a then findPos dflt (W.take ((W.length + 1) / 2)) a
      else findPos dflt (W.drop ((W.length + 1) / 2)) (m - a)
termination_by W.length
decreasing_by all_goals simp only [List.length_take, List.length_drop]; omega

/-- `findPos` against the subset-sum oracle of a nonnegative vector `x`: on a duplicate-free
list `W` of positive total mass `m`, it returns an element of `W` of positive mass with its
exact mass, after at most `⌈log₂ |W|⌉` oracle calls. -/
theorem findPos_spec (x : V → ℝ) (hx : ∀ u, 0 ≤ x u) (dflt : V) :
    ∀ (n : ℕ) (W : List V) (m : ℝ), W.length ≤ n → W.Nodup →
      m = ∑ u ∈ W.toFinset, x u → 0 < m →
      ((findPos dflt W m).eval (fun S => ∑ u ∈ S, x u)).1 ∈ W ∧
      0 < x ((findPos dflt W m).eval (fun S => ∑ u ∈ S, x u)).1 ∧
      ((findPos dflt W m).eval (fun S => ∑ u ∈ S, x u)).2 =
        x ((findPos dflt W m).eval (fun S => ∑ u ∈ S, x u)).1 ∧
      (findPos dflt W m).cost (fun S => ∑ u ∈ S, x u) ≤ Nat.clog 2 W.length := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W m hn hnd hm hpos
    rw [findPos]
    by_cases hW : W.length ≤ 1
    · simp only [hW, ↓reduceIte, eval_pure, cost_pure]
      match W, hW with
      | [], _ => simp [hm] at hpos
      | [u], _ => simp_all
    simp only [hW, ↓reduceIte, eval_bind, cost_bind, eval_ask, cost_ask]
    set L := W.length
    set W₁ := W.take ((L + 1) / 2)
    set W₂ := W.drop ((L + 1) / 2)
    have hl₁ : W₁.length = (L + 1) / 2 := by simp only [W₁, List.length_take, L]; omega
    have hl₂ : W₂.length = L - (L + 1) / 2 := by simp only [W₂, List.length_drop, L]
    have hsplit : W = W₁ ++ W₂ := (List.take_append_drop _ _).symm
    have hnd' := hsplit ▸ hnd
    rw [List.nodup_append] at hnd'
    have hdisj : Disjoint W₁.toFinset W₂.toFinset :=
      List.disjoint_toFinset_iff_disjoint.mpr fun a h₁ h₂ => hnd'.2.2 a h₁ a h₂ rfl
    have hsum : m = ∑ u ∈ W₁.toFinset, x u + ∑ u ∈ W₂.toFinset, x u := by
      rw [hm, hsplit, List.toFinset_append, sum_union hdisj]
    by_cases ha : 0 < ∑ u ∈ W₁.toFinset, x u
    · simp only [ha, ↓reduceIte]
      obtain ⟨hmem, hpos', heq, hc⟩ :=
        ih ((L + 1) / 2) (by omega) W₁ _ (by omega) hnd'.1 rfl ha
      refine ⟨List.mem_of_mem_take hmem, hpos', heq, ?_⟩
      have := clog_half_succ_le (L := L) (l := W₁.length) (by omega) (by omega)
      omega
    · simp only [ha, ↓reduceIte]
      have ha0 : ∑ u ∈ W₁.toFinset, x u = 0 :=
        le_antisymm (not_lt.mp ha) (sum_nonneg fun u _ => hx u)
      have hb : 0 < m - ∑ u ∈ W₁.toFinset, x u := by rw [ha0]; linarith
      obtain ⟨hmem, hpos', heq, hc⟩ :=
        ih (L - (L + 1) / 2) (by omega) W₂ _ (by omega) hnd'.2.1 (by rw [hsum]; ring) hb
      refine ⟨List.mem_of_mem_drop hmem, hpos', heq, ?_⟩
      have := clog_half_succ_le (L := L) (l := W₂.length) (by omega) (by omega)
      omega

end SupportForest
end CutQueryComplexity
