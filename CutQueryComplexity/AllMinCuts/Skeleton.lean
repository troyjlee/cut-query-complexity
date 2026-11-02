import CutQueryComplexity.AllMinCuts.Basic
import CutQueryComplexity.UndirectedClosure.HierarchyBudgetLogLog
import CutQueryComplexity.TwoRespecting.TreeCover

/-! # A skeleton for every minimum cut at once (all-minima plan, M1)

`AllMinCutSkeleton G H`: `λ(G) ≤ λ(H)`, and every minimum cut `S` of `G` has
`c_H(S) ≤ (111/100) λ(G)`. With `0 < λ(G)` this makes every minimum cut of `G` a
`5/4`-near-minimum cut of `H` (`AllMinCutSkeleton.mem_nearMin`), so the offline tree cover
`coverTrees H` covers all of them (`AllMinCutSkeleton.covers`), and `H` is a weak skeleton in
the sense of the existing value search (`AllMinCutSkeleton.isWeakSkeleton`).

The existing supplied-hierarchy program already has this stronger contract. Its correctness proof
fixes one minimum cut `S` and follows the executed refinement; neither the program nor any
hierarchy selected during the refinement depends on `S` (`Hierarchy.refine` reads only the
oracle and the learned data). So the pointwise proof (`refine_preserves_cut`) applies to every
minimum cut of the same execution, and the existing cost theorem, used with one witness, gives
the unchanged budget (`suppliedHierarchyProgLL_allMinCuts`). Positivity of `λ(G)` stays a
separate hypothesis.
-/

set_option autoImplicit false

namespace CutQueryComplexity.AllMinCuts

open WeightedGraph Hierarchy TwoRespecting Search Search.Comp DetMinCut

/-- A lower bound on the skeleton minimum and an upper bound for every original minimum cut. -/
def AllMinCutSkeleton {V : Type} [Fintype V] [DecidableEq V] (G H : WeightedGraph V) : Prop :=
  mincutValue G ≤ mincutValue H ∧
    ∀ S, IsMinCut G S → H.cut S ≤ (111 / 100 : ℝ) * mincutValue G

section Supplied

variable {V N : Type} [Fintype V] [DecidableEq V]
    [Fintype N] [DecidableEq N] [LinearOrder N]

/-- The final supplied step keeps one fixed minimum cut light and bounds the skeleton minimum. -/
theorem supplied_cut_bounds (H : Hier V N) (G : WeightedGraph V)
    (hn : 2 ≤ Fintype.card V) {ρ B : ℝ} (hρ : 1 ≤ ρ) (hB : 1 ≤ B)
    (hg : H.GuardFor ρ) (hpos : 0 < mincutValue G) {S : Finset V}
    (hS : G.cut S = mincutValue G)
    (hRS : H.rep (H.canon G) S ≤ B * mincutValue G) :
    let F := (H.supplied hg (1 / (10 * ρ * B)) (by positivity)
      ⌈200 * ρ ^ 2 * B ^ 2⌉₊).eval G.cut
    mincutValue G ≤ mincutValue F ∧ F.cut S ≤ (111 / 100 : ℝ) * mincutValue G := by
  set q := ⌈200 * ρ ^ 2 * B ^ 2⌉₊
  have hq0 : (200 : ℝ) * ρ ^ 2 * B ^ 2 ≤ q := Nat.le_ceil _
  have hqpos : (0 : ℝ) < q := lt_of_lt_of_le (by positivity) hq0
  have hq : 1 ≤ q := by exact_mod_cast hqpos
  have hqs : 2 / (q : ℝ) ≤ (1 / (10 * ρ * B)) ^ 2 := by
    rw [div_le_iff₀ hqpos, div_pow, one_pow, mul_pow, mul_pow]
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    nlinarith
  refine ⟨le_mincutValue _ hn (fun T hT =>
    Hier.supplied_lower (H := H) G hg _ hq hqs hpos hT), ?_⟩
  exact Hier.supplied_upper (H := H) G hρ hB hg hq hqs hpos hRS hS

end Supplied

section Refinement

variable {V : Type} [Fintype V] [DecidableEq V] {a : ℕ → ℝ} {h : ℕ → ℕ}

/-- **Pointwise preservation through the actual refinement program.** For any fixed minimum
cut `S` whose representation cost is at most `B λ(G)` in the starting hierarchy, the output of
the executed `Hierarchy.refine` has minimum at least `λ(G)` and keeps `S` below
`(111/100) λ(G)`. The program does not depend on `S`. -/
theorem refine_preserves_cut (hb : HierarchyBound a h) (G : WeightedGraph V)
    (hn : 2 ≤ Fintype.card V) (hpos : 0 < mincutValue G)
    {ρ γ : ℝ} (hρ : 1 ≤ ρ) (hγ : 0 < γ)
    (hγdef : 100 * a (Fintype.card V) ^ 2 * ρ ^ 2 * γ ≤ 1)
    (ha : 1 ≤ a (Fintype.card V))
    (Good : Pkg V → Prop) (hgood : ∀ P, Good P → P.H.GuardFor ρ)
    (hsel : ∀ J : WeightedGraph V, Good (hbPkg hb J))
    (hfin : ∀ B : ℝ, 0 < B → 0 ≤ 1 / (10 * ρ * B))
    {S : Finset V} (hS : G.cut S = mincutValue G) :
    ∀ (fuel : ℕ) (B : ℝ) (P : Pkg V), 1 ≤ B → Good P →
      P.H.rep (P.H.canon G) S ≤ B * mincutValue G →
      let F := (refine hb ρ γ hγ.le hfin fuel B P).eval G.cut
      mincutValue G ≤ mincutValue F ∧ F.cut S ≤ (111 / 100 : ℝ) * mincutValue G := by
  have hγ100 : 100 * γ ≤ 1 := by
    have h1 : 1 ≤ a (Fintype.card V) ^ 2 * ρ ^ 2 := by
      have := one_le_mul_of_one_le_of_one_le ha hρ
      nlinarith
    nlinarith
  have hfinal : ∀ (B : ℝ) (P : Pkg V) (hB0 : 0 < B), 1 ≤ B → Good P →
      P.H.rep (P.H.canon G) S ≤ B * mincutValue G →
      let F := (finalProg ρ B (hfin B hB0) P).eval G.cut
      mincutValue G ≤ mincutValue F ∧ F.cut S ≤ (111 / 100 : ℝ) * mincutValue G := by
    intro B P hB0 hB hP hRS
    have hg := hgood P hP
    simpa only [finalProg, dite_eq_left hg, finalQ] using
      supplied_cut_bounds P.H G hn hρ hB hg hpos hS hRS
  intro fuel
  induction fuel with
  | zero =>
      intro B P hB hP hRS
      have hB0 : 0 < B := by linarith
      simpa only [refine, dite_eq_left hB0] using hfinal B P hB0 hB hP hRS
  | succ fuel ih =>
      intro B P hB hP hRS
      have hB0 : 0 < B := by linarith
      by_cases hsmall : γ * B < 1
      · simpa only [refine, ite_eq_left hsmall, dite_eq_left hB0] using
          hfinal B P hB0 hB hP hRS
      · push Not at hsmall
        have hg := hgood P hP
        simp only [refine, ite_eq_right (not_lt.mpr hsmall), roundProg,
          dite_eq_left hg, eval_bind]
        set q := roundQ γ B
        set H0 := (P.H.supplied hg γ hγ.le q).eval G.cut
        have hqge : 2 * B / γ ≤ q := Nat.le_ceil _
        have hqpos : (0 : ℝ) < q := lt_of_lt_of_le (by positivity) hqge
        have hq : 1 ≤ q := by exact_mod_cast hqpos
        have hqη : 2 / (q : ℝ) ≤ γ / B := by
          rw [div_le_div_iff₀ hqpos hB0]
          rw [div_le_iff₀ hγ] at hqge
          linarith
        have hnew := Hier.round_promise (H := P.H) G hρ hg ha hγ hγdef hsmall
          hq hqη hpos hS hRS (hbPkg hb H0).H (hbPkg_spec hb H0).2.2.2
        have hB2 : 1 ≤ B / 2 := by
          have : 1 / γ ≤ B := by rw [div_le_iff₀ hγ]; linarith
          have : 100 ≤ 1 / γ := by rw [le_div_iff₀ hγ]; linarith
          linarith
        exact ih (B / 2) (hbPkg hb H0) hB2 (hsel H0) hnew

end Refinement

section PublicProgram

open UndirectedClosure Hierarchy.RackeShah

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **The supplied-hierarchy program for all minimum cuts at once.** The existing public program
`suppliedHierarchyProgLL`, with its existing budget, returns an `AllMinCutSkeleton` whenever the
hierarchy approximates every minimum cut within `B λ(G)`. -/
theorem suppliedHierarchyProgLL_allMinCuts (P : Pkg V) (B : ℝ) (G : WeightedGraph V)
    (hn : 2 ≤ Fintype.card V) (hpos : 0 < mincutValue G) (hB : 1 ≤ B)
    (hlc : P.H.LeafChildless) (hm : P.m ≤ 2 * Fintype.card V + 1)
    (hprom : ∀ S, IsMinCut G S → P.H.rep (P.H.canon G) S ≤ B * mincutValue G) :
    AllMinCutSkeleton G ((suppliedHierarchyProgLL P B).eval G.cut) ∧
      ((suppliedHierarchyProgLL P B).cost G.cut : ℝ) ≤
        hierarchyConstantLL * Fintype.card V * B *
          ((logL (Fintype.card V) : ℝ) ^ 3 * (logL (logL (Fintype.card V)) : ℝ) ^ 2) := by
  have hpoint : ∀ S, IsMinCut G S →
      let F := (suppliedHierarchyProgLL P B).eval G.cut
      mincutValue G ≤ mincutValue F ∧ F.cut S ≤ (111 / 100 : ℝ) * mincutValue G := by
    intro S hS
    exact refine_preserves_cut rackeShah_hierarchyBound G hn hpos
      (by norm_num : (1 : ℝ) ≤ 42) (hierarchyGammaLL_pos (Fintype.card V))
      (hierarchyGammaLL_calibration (Fintype.card V)) (one_le_aLK' (Fintype.card V))
      (fun P : Pkg V => P.H.LeafChildless)
      (fun _ hP => Hier.ConstantCutGuard.guardFor constantCutGuard_42 hP)
      (fun J => (hbPkg_spec rackeShah_hierarchyBound J).2.1)
      (fun _ hB => by positivity) (isMinCut_of_sat hS)
      ⌈hierarchyGammaLL (Fintype.card V) * B⌉₊ B P hB hlc (hprom S hS)
  obtain ⟨S, hS⟩ := exists_isMinCut_of_two_le_card G hn
  have hs := suppliedHierarchyProgLL_spec P B G hn hpos hB hlc hm ⟨S, hS, hprom S hS⟩
  exact ⟨⟨(hpoint S hS).1, fun T hT => (hpoint T hT).2⟩, hs.2⟩

/-- The capped public tree of the same program, with its existing budget, for all minimum
cuts at once. -/
theorem suppliedHierarchyTreeLL_allMinCuts (P : Pkg V) (B : ℝ)
    (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V) (hpos : 0 < mincutValue G)
    (hB : 1 ≤ B) (hlc : P.H.LeafChildless) (hm : P.m ≤ 2 * Fintype.card V + 1)
    (hprom : ∀ S, IsMinCut G S → P.H.rep (P.H.canon G) S ≤ B * mincutValue G) :
    (∀ read, (suppliedHierarchyTreeLL P B).cost read ≤
        hierarchyBudgetLL (Fintype.card V) B) ∧
    ∃ F, (suppliedHierarchyTreeLL P B).eval G.cut = some F ∧ AllMinCutSkeleton G F := by
  obtain ⟨hskel, hcost⟩ := suppliedHierarchyProgLL_allMinCuts P B G hn hpos hB hlc hm hprom
  refine ⟨fun read => DTree.cost_le _ read, (suppliedHierarchyProgLL P B).eval G.cut,
    ?_, hskel⟩
  apply toDTree_eval
  have hcost' : ((suppliedHierarchyProgLL P B).cost G.cut : ℝ) ≤
      (hierarchyBudgetLL (Fintype.card V) B : ℝ) := hcost.trans (Nat.le_ceil _)
  exact_mod_cast hcost'

end PublicProgram

section Cover

variable {V : Type} [Fintype V] [DecidableEq V]

theorem AllMinCutSkeleton.pos {G H : WeightedGraph V} (hH : AllMinCutSkeleton G H)
    (hpos : 0 < mincutValue G) : 0 < mincutValue H :=
  hpos.trans_le hH.1

/-- Every minimum cut of `G` is a `5/4`-near-minimum cut of `H`. -/
theorem AllMinCutSkeleton.mem_nearMin {G H : WeightedGraph V} (hH : AllMinCutSkeleton G H)
    (hpos : 0 < mincutValue G) {S : Finset V} (hS : IsMinCut G S) :
    4 * H.cut S ≤ 5 * mincutValue H := by
  have := hH.2 S hS
  have := hH.1
  linarith

/-- An all-minimum-cut skeleton is a weak skeleton. -/
theorem AllMinCutSkeleton.isWeakSkeleton [LinearOrder V] {G H : WeightedGraph V}
    (hH : AllMinCutSkeleton G H) (hn : 2 ≤ Fintype.card V) (hpos : 0 < mincutValue G) :
    IsWeakSkeleton G H := by
  obtain ⟨S, hS⟩ := exists_isMinCut_of_two_le_card G hn
  exact ⟨hH.pos hpos, S, hS, hH.mem_nearMin hpos hS⟩

/-- **The actual tree cover covers every minimum cut.** -/
theorem AllMinCutSkeleton.covers [LinearOrder V] {G H : WeightedGraph V}
    (hH : AllMinCutSkeleton G H) (hn : 2 ≤ Fintype.card V) (hpos : 0 < mincutValue G)
    {S : Finset V} (hS : IsMinCut G S) : ∃ T ∈ coverTrees H, Covers T S := by
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hlam := hH.pos hpos
  have hspec := Classical.choose_spec (exists_tree_cover H hlam)
  have htrees : coverTrees H = Classical.choose (exists_tree_cover H hlam) := by
    unfold coverTrees
    split_ifs with h
    · rfl
    · exact absurd ⟨hlam, inferInstance⟩ h
  rw [htrees]
  exact hspec.2 S (TwoRespecting.mem_nearMin.mpr ⟨hS.1.1, hS.1.2, hH.mem_nearMin hpos hS⟩)

end Cover

end CutQueryComplexity.AllMinCuts
