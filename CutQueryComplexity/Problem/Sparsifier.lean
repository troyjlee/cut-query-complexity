import CutQueryComplexity.Problem.Basic

/-! # Composing cut sparsifiers

The weighted construction first learns a sparsifier and then compresses the
explicit result offline. These lemmas track both approximation errors and
original-edge support, including zero cuts and disconnected inputs.
-/

namespace CutQueryComplexity

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem IsCutSparsifier.mono {G H : WeightedGraph V} {ε δ : ℝ}
    (h : IsCutSparsifier ε G H) (he : ε ≤ δ) : IsCutSparsifier δ G H := by
  refine ⟨h.1, fun S => ⟨?_, ?_⟩⟩
  · exact (mul_le_mul_of_nonneg_right (by linarith) (G.cut_nonneg S)).trans (h.2 S).1
  · exact (h.2 S).2.trans (mul_le_mul_of_nonneg_right (by linarith) (G.cut_nonneg S))

/-- Multiplicative errors compose, with explicit nonnegativity hypotheses. -/
theorem IsCutSparsifier.trans {G H K : WeightedGraph V} {ε δ : ℝ}
    (h : IsCutSparsifier ε G H) (h' : IsCutSparsifier δ H K)
    (he : 0 ≤ ε) (hd : 0 ≤ δ) (hd1 : δ ≤ 1) :
    IsCutSparsifier (ε + δ + ε * δ) G K := by
  refine ⟨h'.1.trans h.1, fun S => ⟨?_, ?_⟩⟩
  · calc
      _ ≤ (1 - δ) * ((1 - ε) * G.cut S) := by
        have := mul_nonneg (mul_nonneg he hd) (G.cut_nonneg S)
        nlinarith
      _ ≤ (1 - δ) * H.cut S :=
        mul_le_mul_of_nonneg_left (h.2 S).1 (by linarith)
      _ ≤ _ := (h'.2 S).1
  · calc
      _ ≤ (1 + δ) * H.cut S := (h'.2 S).2
      _ ≤ (1 + δ) * ((1 + ε) * G.cut S) :=
        mul_le_mul_of_nonneg_left (h.2 S).2 (by linarith)
      _ = _ := by ring

/-- Two `ε/4` stages fit within the advertised `ε` error. -/
theorem IsCutSparsifier.trans_quarter {G H K : WeightedGraph V} {ε : ℝ}
    (h : IsCutSparsifier (ε / 4) G H) (h' : IsCutSparsifier (ε / 4) H K)
    (he : 0 ≤ ε) (he1 : ε ≤ 1) : IsCutSparsifier ε G K := by
  apply (h.trans h' (by positivity) (by positivity) (by linarith)).mono
  nlinarith [mul_nonneg he (sub_nonneg.mpr he1)]

theorem IsSparseCutSparsifier.trans_quarter {G H K : WeightedGraph V} {ε : ℝ} {m : ℕ}
    (h : IsCutSparsifier (ε / 4) G H) (h' : IsSparseCutSparsifier (ε / 4) m H K)
    (he : 0 ≤ ε) (he1 : ε ≤ 1) : IsSparseCutSparsifier ε m G K :=
  ⟨h.trans_quarter h'.1 he he1, h'.2⟩

/-- The sparsifier's minimum-cut value approximates the original minimum. -/
theorem IsCutSparsifier.mincut_bounds {G H : WeightedGraph V} {ε : ℝ}
    (h : IsCutSparsifier ε G H) (he : ε ≤ 1) (hn : 2 ≤ Fintype.card V) :
    (1 - ε) * mincutValue G ≤ mincutValue H ∧
      mincutValue H ≤ (1 + ε) * mincutValue G := by
  have hp : (properShores V).Nonempty := by
    obtain ⟨v⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
    exact ⟨{v}, (mem_properShores _).mpr (properShore_singleton v hn)⟩
  obtain ⟨S, hS, hGS⟩ := exists_isMinCut G hp
  obtain ⟨T, hT, hHT⟩ := exists_isMinCut H hp
  constructor
  · rw [← hHT]
    exact (mul_le_mul_of_nonneg_left (mincutValue_le G hT.1) (by linarith)).trans
      (h.2 T).1
  · rw [← hGS]
    exact (mincutValue_le H hS.1).trans (h.2 S).2

end CutQueryComplexity
