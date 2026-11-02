import CutQueryComplexity.Graph.FractionalForest

/-! # The deletion potential (W4 shared base)

For a symmetric weighting `x` (a `WeightedGraph`) and `ε : ℝ`:
* `gfun x ε S = x(E(S)) − (1 − ε)|S|`;
* `Dpot x ε W = max_{S ⊆ W} gfun x ε S`, a maximum over the nonempty finite family
  `W.powerset`. The empty shore gives `Dpot x ε W ≥ 0`;
* `gain x ε W v = Dpot x ε W − Dpot x ε (W.erase v)`, the decrease from deleting `v`.
-/

namespace CutQueryComplexity

open Finset

namespace FractionalForest

variable {V : Type*}

/-- `g(S) = x(E(S)) − (1 − ε)|S|`. -/
noncomputable def gfun (x : WeightedGraph V) (ε : ℝ) (S : Finset V) : ℝ :=
  mass x S - (1 - ε) * S.card

/-- `D(W) = max_{S ⊆ W} g(S)`. -/
noncomputable def Dpot (x : WeightedGraph V) (ε : ℝ) (W : Finset V) : ℝ :=
  W.powerset.sup' ⟨∅, empty_mem_powerset W⟩ (gfun x ε)

/-- The gain `Δ_v(W) = D(W) − D(W ∖ {v})`. -/
noncomputable def gain [DecidableEq V] (x : WeightedGraph V) (ε : ℝ) (W : Finset V) (v : V) : ℝ :=
  Dpot x ε W - Dpot x ε (W.erase v)

@[simp] theorem gfun_empty (x : WeightedGraph V) (ε : ℝ) : gfun x ε ∅ = 0 := by
  simp [gfun]

theorem gfun_le_Dpot (x : WeightedGraph V) (ε : ℝ) {S W : Finset V} (h : S ⊆ W) :
    gfun x ε S ≤ Dpot x ε W :=
  le_sup' (gfun x ε) (mem_powerset.mpr h)

theorem Dpot_nonneg (x : WeightedGraph V) (ε : ℝ) (W : Finset V) : 0 ≤ Dpot x ε W := by
  simpa using gfun_le_Dpot x ε (empty_subset W)

theorem exists_Dpot_eq (x : WeightedGraph V) (ε : ℝ) (W : Finset V) :
    ∃ S ⊆ W, gfun x ε S = Dpot x ε W := by
  obtain ⟨S, hS, h⟩ := exists_mem_eq_sup' ⟨∅, empty_mem_powerset W⟩ (gfun x ε)
  exact ⟨S, mem_powerset.mp hS, h.symm⟩

theorem Dpot_le_iff (x : WeightedGraph V) (ε : ℝ) (W : Finset V) (c : ℝ) :
    Dpot x ε W ≤ c ↔ ∀ S ⊆ W, gfun x ε S ≤ c := by
  unfold Dpot
  exact (sup'_le_iff _ _).trans (by simp only [mem_powerset])

theorem Dpot_mono (x : WeightedGraph V) (ε : ℝ) {W W' : Finset V} (h : W ⊆ W') :
    Dpot x ε W ≤ Dpot x ε W' :=
  (Dpot_le_iff x ε W _).mpr fun _ hS => gfun_le_Dpot x ε (hS.trans h)

theorem gain_nonneg [DecidableEq V] (x : WeightedGraph V) (ε : ℝ) (W : Finset V) (v : V) :
    0 ≤ gain x ε W v :=
  sub_nonneg.mpr (Dpot_mono x ε (erase_subset v W))

end FractionalForest

end CutQueryComplexity
