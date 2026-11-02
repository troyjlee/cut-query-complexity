import CutQueryComplexity.DetMinCut.Unconditional

/-! # A depth-independent public budget for a supplied hierarchy

This instantiates the existing refinement program with the proved guard
quality 42 and the proved quadratic hierarchy distortion.  The result is
linear in the supplied bound B, with log exponent five.  The public tree is
capped on every answer function; the hidden optimum is only a correctness
promise.  No new hierarchy or guard theorem is assumed.
-/

set_option autoImplicit false

namespace CutQueryComplexity.UndirectedClosure

noncomputable section
open Hierarchy Search Search.Comp DetMinCut TwoRespecting

def hierarchyGamma (n : ℕ) : ℝ :=
  1 / (100 * (1690 * (logL n : ℝ) ^ 2) ^ 2 * 42 ^ 2)

theorem hierarchyGamma_pos (n : ℕ) : 0 < hierarchyGamma n := by
  have hL : (0 : ℝ) < logL n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (one_le_logL' n))
  unfold hierarchyGamma
  positivity

theorem hierarchyGamma_le_one (n : ℕ) : hierarchyGamma n ≤ 1 := by
  have ha := one_le_aSq n
  have ha0 : 0 < 1690 * (logL n : ℝ) ^ 2 := lt_of_lt_of_le (by norm_num) ha
  have hden : (0 : ℝ) < 100 * (1690 * (logL n : ℝ) ^ 2) ^ 2 * 42 ^ 2 := by positivity
  unfold hierarchyGamma
  apply (div_le_one hden).mpr
  nlinarith [sq_nonneg (1690 * (logL n : ℝ) ^ 2 - 1)]

theorem hierarchyGamma_calibration (n : ℕ) :
    100 * (1690 * (logL n : ℝ) ^ 2) ^ 2 * 42 ^ 2 * hierarchyGamma n ≤ 1 := by
  have ha := one_le_aSq n
  have ha0 : 0 < 1690 * (logL n : ℝ) ^ 2 := lt_of_lt_of_le (by norm_num) ha
  have hden : (100 * (1690 * (logL n : ℝ) ^ 2) ^ 2 * 42 ^ 2) ≠ 0 := by positivity
  unfold hierarchyGamma
  rw [mul_one_div_cancel hden]

theorem hierarchyGamma_inverse (n : ℕ) :
    1 / hierarchyGamma n = (100 * 1690 ^ 2 * 42 ^ 2) * (logL n : ℝ) ^ 4 := by
  rw [hierarchyGamma, one_div_one_div]
  ring

def hierarchyConstant : ℝ := 9 + 12 * (16 + 800 * 42 ^ 2) * (100 * 1690 ^ 2 * 42 ^ 2)

theorem hierarchyConstant_pos : 0 < hierarchyConstant := by norm_num [hierarchyConstant]

/-- The explicit refined bound, before compilation to a uniformly capped tree. -/
def hierarchyRawBound (n : ℕ) (B : ℝ) : ℝ :=
  (2 * n + 1 : ℕ) * ((⌈hierarchyGamma n * B⌉₊ : ℝ) + 1) +
    (2 * n + 1 : ℕ) * ((Nat.log 2 n : ℝ) + 3) * (16 + 800 * 42 ^ 2) * B /
      hierarchyGamma n

/-- The refinement cost is linear in B and independent of the initial depth. -/
theorem hierarchyRawBound_le {n : ℕ} (hn : 2 ≤ n) {B : ℝ} (hB : 1 ≤ B) :
    hierarchyRawBound n B ≤ hierarchyConstant * n * B * (logL n : ℝ) ^ 5 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hL1 : (1 : ℝ) ≤ (logL n : ℝ) := by exact_mod_cast one_le_logL' n
  have hB0 : 0 ≤ B := by linarith
  have hceil := Nat.ceil_lt_add_one (mul_nonneg (hierarchyGamma_pos n).le hB0)
  have hgammaB : hierarchyGamma n * B ≤ B :=
    (mul_le_mul_of_nonneg_right (hierarchyGamma_le_one n) hB0).trans_eq (one_mul B)
  have hfuel : (⌈hierarchyGamma n * B⌉₊ : ℝ) + 1 ≤ 3 * B := by linarith
  have hM : ((2 * n + 1 : ℕ) : ℝ) ≤ 3 * n := by push_cast; linarith
  have hlog : (Nat.log 2 n : ℝ) + 3 ≤ 4 * (logL n : ℝ) := by
    have h := log_le_logL (le_refl n)
    have hr : (Nat.log 2 n : ℝ) ≤ logL n := by exact_mod_cast h
    linarith
  have hfirst : ((2 * n + 1 : ℕ) : ℝ) * ((⌈hierarchyGamma n * B⌉₊ : ℝ) + 1) ≤
      9 * n * B * (logL n : ℝ) ^ 5 := by
    calc
      _ ≤ (3 * n) * (3 * B) := mul_le_mul hM hfuel (by positivity) (by positivity)
      _ = 9 * n * B := by ring
      _ ≤ 9 * n * B * (logL n : ℝ) ^ 5 :=
        le_mul_of_one_le_right (by positivity) (one_le_pow₀ hL1)
  have hsecond : ((2 * n + 1 : ℕ) : ℝ) * ((Nat.log 2 n : ℝ) + 3) *
      (16 + 800 * 42 ^ 2) * B / hierarchyGamma n ≤
      (12 * (16 + 800 * 42 ^ 2) * (100 * 1690 ^ 2 * 42 ^ 2)) *
        n * B * (logL n : ℝ) ^ 5 := by
    calc
      _ = ((2 * n + 1 : ℕ) : ℝ) * ((Nat.log 2 n : ℝ) + 3) *
          (16 + 800 * 42 ^ 2) * B *
          ((100 * 1690 ^ 2 * 42 ^ 2) * (logL n : ℝ) ^ 4) := by
        rw [div_eq_mul_one_div, hierarchyGamma_inverse]
      _ ≤ (3 * n) * (4 * (logL n : ℝ)) * (16 + 800 * 42 ^ 2) * B *
          ((100 * 1690 ^ 2 * 42 ^ 2) * (logL n : ℝ) ^ 4) := by gcongr
      _ = _ := by ring
  unfold hierarchyRawBound hierarchyConstant
  linarith

def hierarchyBudget (n : ℕ) (B : ℝ) : ℕ :=
  ⌈hierarchyConstant * n * B * (logL n : ℝ) ^ 5⌉₊

theorem hierarchyBudget_le {n : ℕ} (hn : 2 ≤ n) {B : ℝ} (hB : 1 ≤ B) :
    (hierarchyBudget n B : ℝ) ≤
      (hierarchyConstant + 1) * n * B * (logL n : ℝ) ^ 5 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hL1 : (1 : ℝ) ≤ (logL n : ℝ) := by exact_mod_cast one_le_logL' n
  have hbase : (1 : ℝ) ≤ (n : ℝ) * B * (logL n : ℝ) ^ 5 :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hn1 hB)
      (one_le_pow₀ hL1)
  have hc := hierarchyConstant_pos
  have hceil := Nat.ceil_lt_add_one
    (show 0 ≤ hierarchyConstant * n * B * (logL n : ℝ) ^ 5 by positivity)
  unfold hierarchyBudget
  nlinarith

variable {V : Type} [Fintype V] [DecidableEq V]

/-- An actual public refinement program, with all mathematical infrastructure
instantiated by the repository's proved hierarchy and guard theorems. -/
def suppliedHierarchyProg (P : Pkg V) (B : ℝ) : Comp (Finset V) ℝ (WeightedGraph V) :=
  Hierarchy.refine exists_hierarchyBound_sq 42 (hierarchyGamma (Fintype.card V))
    (hierarchyGamma_pos _).le (fun _ hB => by positivity)
    ⌈hierarchyGamma (Fintype.card V) * B⌉₊ B P

theorem suppliedHierarchyProg_spec (P : Pkg V) (B : ℝ) (G : WeightedGraph V)
    (hn : 2 ≤ Fintype.card V) (hpos : 0 < mincutValue G) (hB : 1 ≤ B)
    (hlc : P.H.LeafChildless) (hm : P.m ≤ 2 * Fintype.card V + 1)
    (hprom : ∃ S, IsMinCut G S ∧ P.H.rep (P.H.canon G) S ≤ B * mincutValue G) :
    IsWeakSkeleton G ((suppliedHierarchyProg P B).eval G.cut) ∧
      ((suppliedHierarchyProg P B).cost G.cut : ℝ) ≤
        hierarchyConstant * Fintype.card V * B * (logL (Fintype.card V) : ℝ) ^ 5 := by
  have hs := refine_weakSkeleton_of_good exists_hierarchyBound_sq G hn hpos
    (by norm_num : (1 : ℝ) ≤ 42) (hierarchyGamma_pos (Fintype.card V))
    (hierarchyGamma_calibration (Fintype.card V)) (one_le_aSq (Fintype.card V))
    (fun P : Pkg V => P.H.LeafChildless)
    (fun _ hP => Hier.ConstantCutGuard.guardFor constantCutGuard_42 hP)
    (fun J => (hbPkg_spec exists_hierarchyBound_sq J).2.1) (le_refl _)
    (fun _ hB => by positivity) hB P hlc hm hprom
  refine ⟨hs.1, hs.2.trans ?_⟩
  exact hierarchyRawBound_le hn hB

/-- Uniform public cap. Neither an optimum nor its value is a selector input. -/
def suppliedHierarchyTree (P : Pkg V) (B : ℝ) :
    DTree (Finset V) ℝ (Option (WeightedGraph V)) (hierarchyBudget (Fintype.card V) B) :=
  (suppliedHierarchyProg P B).toDTree (hierarchyBudget (Fintype.card V) B)

/-- Correctness discharges the cap for every honest promised input. -/
theorem suppliedHierarchyTree_correct (P : Pkg V) (B : ℝ) (G : WeightedGraph V)
    (hn : 2 ≤ Fintype.card V) (hpos : 0 < mincutValue G) (hB : 1 ≤ B)
    (hlc : P.H.LeafChildless) (hm : P.m ≤ 2 * Fintype.card V + 1)
    (hprom : ∃ S, IsMinCut G S ∧ P.H.rep (P.H.canon G) S ≤ B * mincutValue G) :
    ∃ F, (suppliedHierarchyTree P B).eval G.cut = some F ∧ IsWeakSkeleton G F := by
  have hs := suppliedHierarchyProg_spec P B G hn hpos hB hlc hm hprom
  refine ⟨(suppliedHierarchyProg P B).eval G.cut, ?_, hs.1⟩
  apply toDTree_eval
  have hcost : ((suppliedHierarchyProg P B).cost G.cut : ℝ) ≤
      (hierarchyBudget (Fintype.card V) B : ℝ) := hs.2.trans (Nat.le_ceil _)
  exact_mod_cast hcost

/-- Every oracle obeys the public depth-independent linear-in-B cap. -/
theorem suppliedHierarchyTree_cost (P : Pkg V) (B : ℝ)
    (hn : 2 ≤ Fintype.card V) (hB : 1 ≤ B) (read : Finset V → ℝ) :
    ((suppliedHierarchyTree P B).cost read : ℝ) ≤
      (hierarchyConstant + 1) * Fintype.card V * B * (logL (Fintype.card V) : ℝ) ^ 5 := by
  have hcost := DTree.cost_le (suppliedHierarchyTree P B) read
  exact (Nat.cast_le.mpr hcost).trans (hierarchyBudget_le hn hB)

/-- The standalone supplied-hierarchy endpoint, with program-before-graph
quantifiers. It improves the paper's log-seven bound to log-five by reusing
the repository's proved quadratic-distortion construction. -/
theorem supplied_hierarchy_log5 :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : Type) [Fintype W] [DecidableEq W]
      (P : Pkg W) (B : ℝ), 2 ≤ Fintype.card W → 1 ≤ B →
      P.H.LeafChildless → P.m ≤ 2 * Fintype.card W + 1 →
      ∃ q : ℕ, (q : ℝ) ≤ C * Fintype.card W * B * (logL (Fintype.card W) : ℝ) ^ 5 ∧
        ∃ D : DTree (Finset W) ℝ (Option (WeightedGraph W)) q,
          (∀ read, D.cost read ≤ q) ∧
          ∀ G : WeightedGraph W, 0 < mincutValue G →
            (∃ S, IsMinCut G S ∧ P.H.rep (P.H.canon G) S ≤ B * mincutValue G) →
            ∃ F, D.eval G.cut = some F ∧ IsWeakSkeleton G F := by
  refine ⟨hierarchyConstant + 1, by linarith [hierarchyConstant_pos],
    fun W _ _ P B hn hB hlc hm => ?_⟩
  refine ⟨hierarchyBudget (Fintype.card W) B, hierarchyBudget_le hn hB,
    suppliedHierarchyTree P B, fun read => DTree.cost_le _ read, ?_⟩
  intro G hpos hprom
  exact suppliedHierarchyTree_correct P B G hn hpos hB hlc hm hprom

#print axioms hierarchyGamma_calibration
#print axioms hierarchyRawBound_le
#print axioms hierarchyBudget_le
#print axioms suppliedHierarchyProg_spec
#print axioms suppliedHierarchyTree_correct
#print axioms suppliedHierarchyTree_cost
#print axioms supplied_hierarchy_log5

end
end CutQueryComplexity.UndirectedClosure
