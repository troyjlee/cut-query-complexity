import CutQueryComplexity.Graph.InducedCut
import CutQueryComplexity.AllPairsAudit.CutAlgebra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Tauto

/-!
# Additive expansion certificates

These predicates are proof invariants of a query algorithm. They are never
arguments used to choose a query. The final algorithm must construct the
partition; the supplied-partition adapter is only an intermediate theorem.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion

open Finset WeightedGraph
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Denominator-free expansion for the revised approximate-flow plan.
Each round contributes at most `2*β*b` fake edges. -/
def AdditiveExpands (G : WeightedGraph V) (W : Finset V) (b R β : ℕ) : Prop :=
  ∀ T : Finset V, T ⊆ W →
    (b : ℝ) * min (T.card : ℝ) ((W \ T).card : ℝ) ≤
      (R : ℝ) * G.localCut W T + 2 * (R : ℝ) * β * b

/-- Every fiber of the public representative map has the certificate. -/
def AdditivePartition (G : WeightedGraph V) (p : V → V) (b R β : ℕ) : Prop :=
  ∀ v, AdditiveExpands G (fiber p v) b R β

/-- The natural shaving threshold. Positivity is proved separately. -/
def shavingScale (R β : ℕ) : ℕ := 4 * R * β

theorem shavingScale_pos {R β : ℕ} (hR : 0 < R) (hβ : 0 < β) :
    0 < shavingScale R β := by
  unfold shavingScale
  positivity

theorem localCut_le_cut (G : WeightedGraph V) (W S : Finset V) :
    G.localCut W S ≤ G.cut S := by
  simpa only [G.localCut_univ] using G.localCut_mono (subset_univ W) S

/-- Small leaves require no separate recovery routine: they obey the same
additive certificate using only nonnegativity of cut values. -/
theorem additiveExpands_of_small (G : WeightedGraph V) (W : Finset V)
    (b R β : ℕ) (hR : 2 ≤ R) (hW : W.card ≤ 4 * β) :
    AdditiveExpands G W b R β := by
  intro T hT
  have hc : ((W \ T).card : ℝ) + (T.card : ℝ) = (W.card : ℝ) := by
    exact_mod_cast (card_sdiff_add_card_eq_card hT)
  have hw : (W.card : ℝ) ≤ 4 * (β : ℝ) := by exact_mod_cast hW
  have hm : min (T.card : ℝ) ((W \ T).card : ℝ) ≤ 2 * (β : ℝ) := by
    have hl := min_le_left (T.card : ℝ) ((W \ T).card : ℝ)
    have hr := min_le_right (T.card : ℝ) ((W \ T).card : ℝ)
    linarith
  have hr : (2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hm' : min (T.card : ℝ) ((W \ T).card : ℝ) ≤ (R : ℝ) * β :=
    hm.trans (mul_le_mul_of_nonneg_right hr (by positivity))
  calc
    (b : ℝ) * min (T.card : ℝ) ((W \ T).card : ℝ) ≤
        (b : ℝ) * ((R : ℝ) * β) :=
      mul_le_mul_of_nonneg_left hm' (by positivity)
    _ ≤ (R : ℝ) * G.localCut W T + 2 * (R : ℝ) * β * b := by
      have hn := mul_nonneg (show (0 : ℝ) ≤ R by positivity) (G.localCut_nonneg W T)
      have herr : (0 : ℝ) ≤ (R : ℝ) * β * b := by positivity
      nlinarith

/-- The smaller induced side of a globally small cut is bounded by the
shaving scale. The vertex bound `N` may be larger than the current part. -/
theorem additive_small_cut_side {G : WeightedGraph V} {W S : Finset V}
    {b R β N : ℕ} (hb : 0 < b) (hN : N ≤ b * β)
    (hexpand : AdditiveExpands G W b R β) (hcut : G.cut S ≤ 2 * (N : ℝ)) :
    min ((W ∩ S).card : ℝ) ((W \ S).card : ℝ) ≤ (shavingScale R β : ℝ) := by
  have he := hexpand (W ∩ S) inter_subset_left
  have hdiff : W \ (W ∩ S) = W \ S := by
    ext v
    simp only [mem_sdiff, mem_inter]
    tauto
  have hlocal : G.localCut W (W ∩ S) = G.localCut W S := by
    rw [inter_comm W S, G.localCut_inter]
  rw [hdiff, hlocal] at he
  have hc : G.localCut W S ≤ 2 * (N : ℝ) :=
    (localCut_le_cut G W S).trans hcut
  have hr : (0 : ℝ) ≤ R := by positivity
  have hn : (N : ℝ) ≤ (b : ℝ) * β := by exact_mod_cast hN
  have hn' := mul_le_mul_of_nonneg_left hn hr
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hbound : (b : ℝ) * min ((W ∩ S).card : ℝ) ((W \ S).card : ℝ) ≤
      (b : ℝ) * (4 * (R : ℝ) * β) := by
    have hc' := mul_le_mul_of_nonneg_left hc hr
    nlinarith
  have h := le_of_mul_le_mul_left hbound hb'
  simpa only [shavingScale, Nat.cast_mul, Nat.cast_ofNat] using h

end
end CutQueryComplexity.DeterministicAPMCExpansion

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.additiveExpands_of_small
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.additive_small_cut_side
