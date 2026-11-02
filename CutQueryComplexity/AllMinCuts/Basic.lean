import CutQueryComplexity.TreeCutSparsifier.Normalization

/-! # The complete family of global minimum cuts (all-minima plan, M0)

`Output` is a value together with a finite set of shores, and `Correct G out` says that the
value is `λ(G)` and that the shores are exactly the global minimum-cut shores of `G`. Both `S`
and `Sᶜ` belong to a correct family (`Correct.compl_mem`); a correct family is nonempty when
there are at least two vertices (`Correct.nonempty`). The family may be exponentially large:
when `λ(G) = 0` every proper union of positive-support components is a minimum cut.

`isMinCut_iff_exists_quot`: for a safe partition `r` of `G` (every minimum cut is a union of
classes) and at least two vertices, the minimum cuts of `G` are exactly the pull-backs of the
minimum cuts of the quotient `G/r`. Hence a correct family of the quotient pulls back to a
correct family of `G` (`Correct.pullOutput`), with no query.
-/

set_option autoImplicit false

namespace CutQueryComplexity.AllMinCuts

open WeightedGraph DetMinCut TreeCutSparsifier Finset

/-- A minimum-cut value and a finite family of shores. -/
structure Output (V : Type) where
  cuts : Finset (Finset V)
  value : ℝ

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The value is `λ(G)` and the family consists of exactly the global minimum-cut shores. -/
def Correct (G : WeightedGraph V) (out : Output V) : Prop :=
  out.value = mincutValue G ∧ ∀ S : Finset V, S ∈ out.cuts ↔ IsMinCut G S

/-! ## Minimum cuts as proper shores of minimum value -/

theorem isMinCut_iff (G : WeightedGraph V) (S : Finset V) :
    IsMinCut G S ↔ ProperShore S ∧ G.cut S = mincutValue G :=
  ⟨fun h => ⟨h.1, isMinCut_of_sat h⟩, fun h => ⟨h.1, fun _ hT => h.2 ▸ mincutValue_le G hT⟩⟩

theorem properShore_compl {S : Finset V} (hS : ProperShore S) : ProperShore Sᶜ := by
  refine ⟨?_, fun h => ?_⟩
  · by_contra hne
    rw [not_nonempty_iff_eq_empty, compl_eq_empty_iff] at hne
    exact hS.2 hne
  · rw [compl_eq_univ_iff] at h
    exact hS.1.ne_empty h

theorem IsMinCut.compl {G : WeightedGraph V} {S : Finset V} (h : IsMinCut G S) :
    IsMinCut G Sᶜ := by
  rw [isMinCut_iff] at h ⊢
  exact ⟨properShore_compl h.1, by rw [G.cut_compl]; exact h.2⟩

/-! ## Elementary consequences of correctness -/

theorem Correct.compl_mem {G : WeightedGraph V} {out : Output V} (h : Correct G out)
    {S : Finset V} (hS : S ∈ out.cuts) : Sᶜ ∈ out.cuts :=
  (h.2 _).mpr (IsMinCut.compl ((h.2 S).mp hS))

theorem Correct.cut_eq {G : WeightedGraph V} {out : Output V} (h : Correct G out)
    {S : Finset V} (hS : S ∈ out.cuts) : G.cut S = out.value := by
  rw [h.1]; exact isMinCut_of_sat ((h.2 S).mp hS)

theorem Correct.nonempty {G : WeightedGraph V} {out : Output V} (h : Correct G out)
    (hn : 2 ≤ Fintype.card V) : out.cuts.Nonempty := by
  obtain ⟨S, hS⟩ := exists_isMinCut_of_two_le_card G hn
  exact ⟨S, (h.2 S).mpr hS⟩

/-! ## The quotient correspondence -/

/-- **Exact correspondence of the minimum-cut families of a safe quotient.** -/
theorem isMinCut_iff_exists_quot (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V) {r : V → V}
    (hs : SafePartition G r) (S : Finset V) :
    IsMinCut G S ↔ ∃ T : Finset (Cls r), IsMinCut (quot G r) T ∧ pull (proj r) T = S := by
  have hval := safePartition_mincutValue G hn hs
  constructor
  · intro hS
    have hpull : pull (proj r) (S.image (proj r)) = S := pull_image_of_sat (hs S hS)
    refine ⟨S.image (proj r), ?_, hpull⟩
    refine ⟨⟨?_, fun h => ?_⟩, fun T hT => ?_⟩
    · obtain ⟨x, hx⟩ := hS.1.1
      exact ⟨_, mem_image_of_mem _ hx⟩
    · apply hS.1.2
      rw [← hpull, h]
      ext x; simp
    · rw [cut_contract, cut_contract, hpull]
      exact hS.2 _ (properShore_pull _ (proj_surjective r) hT)
  · rintro ⟨T, hT, rfl⟩
    rw [isMinCut_iff] at hT ⊢
    refine ⟨properShore_pull _ (proj_surjective r) hT.1, ?_⟩
    rw [← cut_contract, hT.2, hval]

/-- The family of a safe quotient, pulled back to the original vertices. -/
def pullOutput (r : V → V) (out : Output (Cls r)) : Output V :=
  ⟨out.cuts.image (pull (proj r)), out.value⟩

/-- A correct family of a safe quotient pulls back to a correct family of `G`. -/
theorem Correct.pullOutput {G : WeightedGraph V} (hn : 2 ≤ Fintype.card V) {r : V → V}
    (hs : SafePartition G r) {out : Output (Cls r)} (h : Correct (quot G r) out) :
    Correct G (AllMinCuts.pullOutput r out) := by
  refine ⟨h.1.trans (safePartition_mincutValue G hn hs), fun S => ?_⟩
  rw [isMinCut_iff_exists_quot G hn hs, AllMinCuts.pullOutput, mem_image]
  simp only [h.2]

end CutQueryComplexity.AllMinCuts
