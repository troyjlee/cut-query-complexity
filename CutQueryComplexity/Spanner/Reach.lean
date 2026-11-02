import CutQueryComplexity.Spectral.Bundle

/-! # Short walks through selected pairs (D2)

`Reach ℓ H L m x y`: `x` reaches `y` through at most `m` pairs of `H`, each of length at most `L`.
It is monotone in `m`, `H`, `L` (`mono`), reversible (`symm`), and composes with added counts
(`trans`). `exists_path` turns it into a Mathlib path in `pairGraph H` of total length at most
`m L`, which is the form used by bundle domination.
-/

namespace CutQueryComplexity
namespace Spanner

open Finset Spectral

variable {V : Type} (ℓ : Sym2 V → ℝ)

/-- `x` reaches `y` through at most `m` pairs of `H`, each of length at most `L`. -/
inductive Reach (H : Finset (Sym2 V)) (L : ℝ) : ℕ → V → V → Prop
  | refl (m : ℕ) (x : V) : Reach H L m x x
  | step {m : ℕ} {x y z : V} : x ≠ y → s(x, y) ∈ H → ℓ s(x, y) ≤ L → Reach H L m y z →
      Reach H L (m + 1) x z

variable {ℓ}

namespace Reach

theorem mono {H H' : Finset (Sym2 V)} {L L' : ℝ} {m m' : ℕ} {x y : V}
    (h : Reach ℓ H L m x y) (hH : H ⊆ H') (hL : L ≤ L') (hm : m ≤ m') :
    Reach ℓ H' L' m' x y := by
  induction h generalizing m' with
  | refl _ x => exact refl m' x
  | @step m x y z hxy hH' hl _ ih =>
      obtain ⟨m'', rfl⟩ : ∃ m'', m' = m'' + 1 := ⟨m' - 1, by omega⟩
      exact step hxy (hH hH') (hl.trans hL) (ih (by omega))

theorem single {H : Finset (Sym2 V)} {L : ℝ} {x y : V} (hxy : x ≠ y) (h : s(x, y) ∈ H)
    (hl : ℓ s(x, y) ≤ L) : Reach ℓ H L 1 x y :=
  step hxy h hl (refl 0 y)

theorem trans {H : Finset (Sym2 V)} {L : ℝ} {m m' : ℕ} {x y z : V}
    (h : Reach ℓ H L m x y) (h' : Reach ℓ H L m' y z) : Reach ℓ H L (m + m') x z := by
  induction h with
  | refl m x => exact h'.mono subset_rfl le_rfl (by omega)
  | @step m x y w hxy hH hl _ ih =>
      rw [show m + 1 + m' = (m + m') + 1 by omega]
      exact step hxy hH hl (ih h')

theorem symm {H : Finset (Sym2 V)} {L : ℝ} {m : ℕ} {x y : V} (h : Reach ℓ H L m x y) :
    Reach ℓ H L m y x := by
  induction h with
  | refl m x => exact refl m x
  | @step m x y z hxy hH hl _ ih =>
      have h1 : Reach ℓ H L 1 y x :=
        single (Ne.symm hxy) (by rwa [Sym2.eq_swap]) (by rwa [Sym2.eq_swap])
      exact ih.trans h1

/-- A walk of at most `m` edges, each in `H` with length at most `L`. -/
theorem exists_walk {H : Finset (Sym2 V)} {L : ℝ} {m : ℕ} {x y : V} (h : Reach ℓ H L m x y) :
    ∃ p : (pairGraph H).Walk x y, p.length ≤ m ∧ ∀ f ∈ p.edges, ℓ f ≤ L := by
  induction h with
  | refl m x => exact ⟨SimpleGraph.Walk.nil, by simp, by simp⟩
  | @step m x y z hxy hH hl _ ih =>
      obtain ⟨p, hp, hpe⟩ := ih
      have hadj : (pairGraph H).Adj x y := by
        rw [SimpleGraph.fromEdgeSet_adj]; exact ⟨hH, hxy⟩
      refine ⟨SimpleGraph.Walk.cons hadj p, by simp; omega, ?_⟩
      intro f hf
      rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at hf
      rcases hf with rfl | hf
      · exact hl
      · exact hpe f hf

/-- **A path of total length at most `m L`.** -/
theorem exists_path {H : Finset (Sym2 V)} {L : ℝ} (hL : 0 ≤ L) {m : ℕ} {x y : V}
    (h : Reach ℓ H L m x y) :
    ∃ p : (pairGraph H).Walk x y, p.IsPath ∧ (p.edges.map ℓ).sum ≤ m * L := by
  classical
  obtain ⟨p, hp, hpe⟩ := h.exists_walk
  refine ⟨p.bypass, p.bypass_isPath, ?_⟩
  have hle : ∀ f ∈ p.bypass.edges, ℓ f ≤ L := fun f hf => hpe f (p.edges_bypass_subset_edges hf)
  calc (p.bypass.edges.map ℓ).sum ≤ (p.bypass.edges.map fun _ => L).sum :=
        List.sum_le_sum fun f hf => hle f hf
    _ = p.bypass.length * L := by
        rw [List.map_const', List.sum_replicate, SimpleGraph.Walk.length_edges, nsmul_eq_mul]
    _ ≤ m * L := by
        have : (p.bypass.length : ℝ) ≤ m := by
          exact_mod_cast (p.length_bypass_le_length.trans hp)
        exact mul_le_mul_of_nonneg_right this hL

end Reach

end Spanner
end CutQueryComplexity
