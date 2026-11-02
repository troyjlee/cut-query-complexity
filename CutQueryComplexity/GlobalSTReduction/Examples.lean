import CutQueryComplexity.GlobalSTReduction.Randomized
import CutQueryComplexity.Reconstruction.WeightedUndirected

/-! # A non-canonical real-weight s-t family, and the reduction applied to it

`reconstructionFamily` learns the whole real-weighted graph on `Fin k` with
`k + C(k,2) ≤ k²` cut queries (`Reconstruction.WeightedUndirected.reconstruct`)
and returns the *inclusion-maximal* minimum s-t shore, the complement of the
canonical t-s shore. It is a `RealSTFamily (fun k => k ^ 2)`, and its charge is
size-regular at every `n`.

The family is genuinely non-canonical: on the edgeless graph on `Fin 3` it
returns `{0, 2}` for `s = 0`, `t = 1`, which is not the canonical shore `{0}`
(`reconstructionFamily_not_canonical`). So it satisfies the interface of this
reduction but not the `CanonicalSTFamily` interface of the Gomory–Hu
reduction. `exists_global_reconstruction` applies `exists_global_from_st` to it,
which exercises the endpoint on a family with noncanonical answers. The
resulting `O(n² log³ n)` bound is not competitive; the example only shows that
the hypotheses can be met.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GlobalSTReduction
noncomputable section
open scoped Classical ENNReal
open WeightedGraph GHReduction Probability
open Reconstruction.WeightedUndirected (reconstruct_eval queryBudget_le)

/-- The inclusion-maximal minimum s-t shore of an explicit graph, chosen offline. -/
def maximalShore {k : ℕ} (H : WeightedGraph (Fin k)) (s t : Fin k) : Finset (Fin k) :=
  if h : s = t then ∅ else (Classical.choose (exists_canonicalSTCut H (Ne.symm h)))ᶜ

theorem maximalShore_spec {k : ℕ} (H : WeightedGraph (Fin k)) {s t : Fin k} (hst : s ≠ t) :
    IsSTMinCut H s t (maximalShore H s t) := by
  rw [maximalShore, dite_eq_right hst]
  have h := Classical.choose_spec (exists_canonicalSTCut H (Ne.symm hst))
  simpa using stMinCut_compl H h.1

/-- Learn the graph, then return the maximal minimum shore. -/
def reconstructionFamily : RealSTFamily (fun k => k ^ 2) where
  program k s t :=
    ((reconstruct (V := Fin k)).map (fun H => maximalShore H s t)).weaken
      (by
        have h := queryBudget_le (V := Fin k)
        simpa [Reconstruction.WeightedUndirected.queryBudget] using h)
  correct k s t hst G := by
    simp only [DTree.eval, DTree.run_weaken, DTree.run_map]
    rw [show (DTree.run G.cut (reconstruct (V := Fin k))).1 = G from reconstruct_eval G]
    exact maximalShore_spec G hst

theorem reconstructionFamily_eval {k : ℕ} (s t : Fin k) (G : WeightedGraph (Fin k)) :
    (reconstructionFamily.program k s t).eval G.cut = maximalShore G s t := by
  simp only [reconstructionFamily, DTree.eval, DTree.run_weaken, DTree.run_map]
  rw [show (DTree.run G.cut (reconstruct (V := Fin k))).1 = G from reconstruct_eval G]

theorem sizeRegular_sq (n : ℕ) : SizeRegular n (fun k => k ^ 2) := by
  intro s _ hsn
  have := Nat.mul_le_mul_left (n * s) hsn
  nlinarith

@[simp] theorem zero_cut {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) :
    (0 : WeightedGraph V).cut S = 0 := by
  simp [WeightedGraph.cut]

/-- On the edgeless graph on `Fin 3`, the family's answer for `s = 0`, `t = 1` is
a minimum shore that is not the canonical one. -/
theorem reconstructionFamily_not_canonical :
    ¬IsCanonicalSTCut (0 : WeightedGraph (Fin 3)) 0 1
      ((reconstructionFamily.program 3 0 1).eval (0 : WeightedGraph (Fin 3)).cut) := by
  rw [reconstructionFamily_eval]
  intro hcan
  have hst : (0 : Fin 3) ≠ 1 := by decide
  -- The canonical `1`-`0` shore is `{1}`, so the maximal `0`-`1` shore contains `2`.
  have h2 : (2 : Fin 3) ∈ maximalShore (0 : WeightedGraph (Fin 3)) 0 1 := by
    rw [maximalShore, dite_eq_right hst, Finset.mem_compl]
    intro h2C
    have hC := Classical.choose_spec (exists_canonicalSTCut (0 : WeightedGraph (Fin 3))
      (Ne.symm hst))
    have hsingle : IsSTMinCut (0 : WeightedGraph (Fin 3)) 1 0 {1} :=
      ⟨by simp, by decide, fun T _ _ => by rw [zero_cut, zero_cut]⟩
    have := hC.2 {1} hsingle h2C
    simp at this
  -- The canonical `0`-`1` shore must lie inside the minimum shore `{0}`.
  have hzero : IsSTMinCut (0 : WeightedGraph (Fin 3)) 0 1 {0} :=
    ⟨by simp, by decide, fun T _ _ => by rw [zero_cut, zero_cut]⟩
  have := hcan.2 {0} hzero h2
  simp at this

/-- The reduction applied to the non-canonical reconstruction family. -/
theorem exists_global_reconstruction {n : ℕ} (hn : 2 ≤ n) (b : ℕ) :
    ∃ program : RTree (Finset (Fin n)) ℝ (Finset (Fin n) × ℝ)
        (detGlobalBudget n b (fun k => k ^ 2)),
      (∀ read, ∀ out ∈ (RTree.run read program).support,
        out.2 ≤ detGlobalBudget n b (fun k => k ^ 2)) ∧
      (∀ G : WeightedGraph (Fin n), ∀ out ∈ (program.eval G.cut).support,
        ValidOutput G out) ∧
      ∀ G : WeightedGraph (Fin n),
        mass (program.eval G.cut) (fun out => ¬GlobalSuccess G out) ≤
          (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ b :=
  exists_global_from_st reconstructionFamily (sizeRegular_sq n) hn b

end
end CutQueryComplexity.GlobalSTReduction
