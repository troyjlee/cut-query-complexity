import CutQueryComplexity.AllMinCuts.Skeleton
import CutQueryComplexity.TwoRespecting.AllMinima

/-! # The complete family of minimum cuts from a skeleton (all-minima plan, M5)

Given an explicit graph `H`, `coverReport H`:

1. runs the existing value search `skeletonMinCut H` and queries its shore once; when `H` is an
   `AllMinCutSkeleton` of `G` with `0 < λ(G)`, the answer is `ℓ = λ(G)`, an oracle answer;
2. reports, on every tree of the offline cover `coverTrees H`, all shores of value `ℓ` crossing
   one or two tree edges (`allTwoRespecting`);
3. returns the union of these families and of their complements, with the value `ℓ`.

`coverReport_spec`: `Correct G` on every such `G`. Soundness comes from the exact local
reports and from closure under complementation; completeness from the universal cover
(`AllMinCutSkeleton.covers`), including the complement alternative of `Covers`. The cost is at
most `reportBound n = skelBound n + 1 + coverSize n · 250 n (⌈log₂ n⌉ + 1) = O(n log² n)` on
every graph (`coverReport_cost`). Neither the value nor any family of cuts is an input: `H`
supplies the trees, and the hidden graph is queried for values.
-/

set_option autoImplicit false

namespace CutQueryComplexity.AllMinCuts

open WeightedGraph TwoRespecting Search Search.Comp DetMinCut Finset

variable {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- The union of a list of families. -/
def unionAll (L : List (Finset (Finset V))) : Finset (Finset V) := L.foldr (· ∪ ·) ∅

omit [Fintype V] [LinearOrder V] in
theorem mem_unionAll {L : List (Finset (Finset V))} {S : Finset V} :
    S ∈ unionAll L ↔ ∃ F ∈ L, S ∈ F := by
  induction L with
  | nil => simp [unionAll]
  | cons F L ih =>
      show S ∈ F ∪ unionAll L ↔ _
      rw [mem_union, ih]
      simp only [List.mem_cons, exists_eq_or_imp]

/-- **All minimum cuts from a skeleton.** -/
noncomputable def coverReport (H : WeightedGraph V) : Comp (Finset V) ℝ (Output V) :=
  (skeletonMinCut H).bind fun S₀ =>
    (ask S₀).bind fun ℓ =>
      (mapList (fun T => allTwoRespecting T ℓ) (coverTrees H)).map fun fams =>
        ⟨unionAll fams ∪ (unionAll fams).image compl, ℓ⟩

/-- The query cap of `coverReport` on `n` vertices. -/
def reportBound (n : ℕ) : ℕ :=
  skelBound n + 1 + coverSize n * (250 * n * (Nat.clog 2 n + 1))

theorem reportBound_mono {N n : ℕ} (h : N ≤ n) : reportBound N ≤ reportBound n := by
  unfold reportBound coverSize
  have := skelBound_mono h
  have := Nat.clog_mono_right 2 h
  gcongr

/-- The cost of `coverReport` on every graph. -/
theorem coverReport_cost (G H : WeightedGraph V) :
    (coverReport H).cost G.cut ≤ reportBound (Fintype.card V) := by
  simp only [coverReport, cost_bind, cost_ask, cost_map]
  have h1 := skeletonMinCut_cost G H
  have h2 := cost_mapList_le G.cut
    (fun T => allTwoRespecting T (G.cut ((skeletonMinCut H).eval G.cut))) (coverTrees H)
    (c := 250 * Fintype.card V * (Nat.clog 2 (Fintype.card V) + 1))
    fun T _ => allTwoRespecting_cost G _
  have h3 := Nat.mul_le_mul_left (250 * Fintype.card V * (Nat.clog 2 (Fintype.card V) + 1))
    (length_coverTrees H)
  unfold reportBound skelBound
  rw [Nat.mul_comm (coverSize _) (250 * _ * _)]
  simp only [eval_ask] at h2 ⊢
  omega

/-- **Correctness of the cover reporter.** For an `AllMinCutSkeleton` `H` of a graph `G` with
positive minimum cut on at least two vertices, the output is the value `λ(G)` and exactly the
set of all minimum-cut shores of `G`. -/
theorem coverReport_spec (G H : WeightedGraph V) (hn : 2 ≤ Fintype.card V)
    (hpos : 0 < mincutValue G) (hH : AllMinCutSkeleton G H) :
    Correct G ((coverReport H).eval G.cut) ∧
      (coverReport H).cost G.cut ≤ reportBound (Fintype.card V) := by
  refine ⟨?_, coverReport_cost G H⟩
  have hW := hH.isWeakSkeleton hn hpos
  set S₀ := (skeletonMinCut H).eval G.cut
  have hS₀ := skeletonMinCut_correct G H hn hW
  have hℓ : G.cut S₀ = mincutValue G := isMinCut_of_sat hS₀
  have hℓpos : 0 < G.cut S₀ := hℓ ▸ hpos
  set fams := (coverTrees H).map fun T => (allTwoRespecting T (G.cut S₀)).eval G.cut
  have heval : (coverReport H).eval G.cut =
      ⟨unionAll fams ∪ (unionAll fams).image compl, G.cut S₀⟩ := by
    simp only [coverReport, eval_bind, eval_ask, eval_map, eval_mapList, fams, S₀]
  rw [heval]
  have hmem : ∀ X, X ∈ unionAll fams ↔
      ∃ T ∈ coverTrees H, T.IsTwoRespShore X ∧ G.cut X = G.cut S₀ := by
    intro X
    rw [mem_unionAll]
    simp only [fams, List.mem_map]
    constructor
    · rintro ⟨F, ⟨T, hT, rfl⟩, hX⟩
      exact ⟨T, hT, (allTwoRespecting_correct G hℓ hℓpos X).mp hX⟩
    · rintro ⟨T, hT, hX⟩
      exact ⟨_, ⟨T, hT, rfl⟩, (allTwoRespecting_correct G hℓ hℓpos X).mpr hX⟩
  have hsound : ∀ X, X ∈ unionAll fams → IsMinCut G X := by
    intro X hX
    obtain ⟨T, -, hTX, hv⟩ := (hmem X).mp hX
    exact (isMinCut_iff G X).mpr ⟨isTwoRespShore_nonempty hTX, hv.trans hℓ⟩
  refine ⟨hℓ, fun S => ⟨fun hS => ?_, fun hS => ?_⟩⟩
  · rcases mem_union.mp hS with hS | hS
    · exact hsound S hS
    · obtain ⟨X, hX, rfl⟩ := mem_image.mp hS
      exact IsMinCut.compl (hsound X hX)
  · obtain ⟨T, hT, hcov⟩ := hH.covers hn hpos hS
    have hv : G.cut S = G.cut S₀ := (isMinCut_of_sat hS).trans hℓ.symm
    rcases hcov with h | h
    · exact mem_union_left _ ((hmem S).mpr ⟨T, hT, h, hv⟩)
    · refine mem_union_right _ (mem_image.mpr ⟨Sᶜ, (hmem _).mpr ⟨T, hT, h, ?_⟩, compl_compl S⟩)
      rw [G.cut_compl]; exact hv

end CutQueryComplexity.AllMinCuts
