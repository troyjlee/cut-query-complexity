import CutQueryComplexity.DetMinCut.UnconditionalLogLog
import CutQueryComplexity.Hierarchy.RackeShah.Existence

/-! # The supplied-hierarchy budget with the Räcke–Shah quality (log-log plan, M4)

`HierarchyBudget.lean` with the quadratic distortion `1690 L²` replaced by the Räcke–Shah
distortion `268 L L(L)` (`rackeShah_hierarchyBound`). The refinement guard weight becomes
`γ = 1 / (100 (268 L K)² 42²)`, and the cap of the supplied-hierarchy weak-skeleton program is
`O(n B L(n)³ K(n)²)` with `K = L ∘ L` (`supplied_hierarchy_log3loglog2`), linear in `B`.
-/

set_option autoImplicit false

namespace CutQueryComplexity.UndirectedClosure

noncomputable section
open Hierarchy Search Search.Comp DetMinCut TwoRespecting Hierarchy.RackeShah

/-- The distortion `a(n) = 268 L(n) L(L(n))` of the Räcke–Shah hierarchy. -/
def aLK (n : ℕ) : ℝ := rsConstant * (logL n : ℝ) * (logL (logL n) : ℝ)

theorem one_le_aLK' (n : ℕ) : 1 ≤ aLK n := one_le_aLK n

def hierarchyGammaLL (n : ℕ) : ℝ :=
  1 / (100 * (aLK n) ^ 2 * 42 ^ 2)

theorem hierarchyGammaLL_pos (n : ℕ) : 0 < hierarchyGammaLL n := by
  have := one_le_aLK' n
  unfold hierarchyGammaLL
  positivity

theorem hierarchyGammaLL_le_one (n : ℕ) : hierarchyGammaLL n ≤ 1 := by
  have ha := one_le_aLK' n
  have hden : (0 : ℝ) < 100 * (aLK n) ^ 2 * 42 ^ 2 := by positivity
  unfold hierarchyGammaLL
  apply (div_le_one hden).mpr
  nlinarith [sq_nonneg (aLK n - 1)]

theorem hierarchyGammaLL_calibration (n : ℕ) :
    100 * (aLK n) ^ 2 * 42 ^ 2 * hierarchyGammaLL n ≤ 1 := by
  have ha := one_le_aLK' n
  have hden : (100 * (aLK n) ^ 2 * 42 ^ 2) ≠ 0 := by positivity
  unfold hierarchyGammaLL
  rw [mul_one_div_cancel hden]

theorem hierarchyGammaLL_inverse (n : ℕ) :
    1 / hierarchyGammaLL n =
      (100 * rsConstant ^ 2 * 42 ^ 2) * ((logL n : ℝ) ^ 2 * (logL (logL n) : ℝ) ^ 2) := by
  rw [hierarchyGammaLL, one_div_one_div, aLK]
  ring

def hierarchyConstantLL : ℝ := 9 + 12 * (16 + 800 * 42 ^ 2) * (100 * rsConstant ^ 2 * 42 ^ 2)

theorem hierarchyConstantLL_pos : 0 < hierarchyConstantLL := by norm_num [hierarchyConstantLL, rsConstant]

/-- The explicit refined bound, before compilation to a uniformly capped tree. -/
def hierarchyRawBoundLL (n : ℕ) (B : ℝ) : ℝ :=
  (2 * n + 1 : ℕ) * ((⌈hierarchyGammaLL n * B⌉₊ : ℝ) + 1) +
    (2 * n + 1 : ℕ) * ((Nat.log 2 n : ℝ) + 3) * (16 + 800 * 42 ^ 2) * B /
      hierarchyGammaLL n

/-- The refinement cost is linear in B and independent of the initial depth. -/
theorem hierarchyRawBoundLL_le {n : ℕ} (hn : 2 ≤ n) {B : ℝ} (hB : 1 ≤ B) :
    hierarchyRawBoundLL n B ≤
      hierarchyConstantLL * n * B * ((logL n : ℝ) ^ 3 * (logL (logL n) : ℝ) ^ 2) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hL1 : (1 : ℝ) ≤ (logL n : ℝ) := by exact_mod_cast one_le_logL' n
  have hK1 : (1 : ℝ) ≤ (logL (logL n) : ℝ) := by exact_mod_cast one_le_logL' _
  set LK : ℝ := (logL n : ℝ) ^ 3 * (logL (logL n) : ℝ) ^ 2 with hLK
  have hLK1 : 1 ≤ LK := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL1) (one_le_pow₀ hK1)
  have hB0 : 0 ≤ B := by linarith
  have hceil := Nat.ceil_lt_add_one (mul_nonneg (hierarchyGammaLL_pos n).le hB0)
  have hgammaB : hierarchyGammaLL n * B ≤ B :=
    (mul_le_mul_of_nonneg_right (hierarchyGammaLL_le_one n) hB0).trans_eq (one_mul B)
  have hfuel : (⌈hierarchyGammaLL n * B⌉₊ : ℝ) + 1 ≤ 3 * B := by linarith
  have hM : ((2 * n + 1 : ℕ) : ℝ) ≤ 3 * n := by push_cast; linarith
  have hlog : (Nat.log 2 n : ℝ) + 3 ≤ 4 * (logL n : ℝ) := by
    have h := log_le_logL (le_refl n)
    have hr : (Nat.log 2 n : ℝ) ≤ logL n := by exact_mod_cast h
    linarith
  have hfirst : ((2 * n + 1 : ℕ) : ℝ) * ((⌈hierarchyGammaLL n * B⌉₊ : ℝ) + 1) ≤
      9 * n * B * LK := by
    calc
      _ ≤ (3 * n) * (3 * B) := mul_le_mul hM hfuel (by positivity) (by positivity)
      _ = 9 * n * B := by ring
      _ ≤ 9 * n * B * LK := le_mul_of_one_le_right (by positivity) hLK1
  have hsecond : ((2 * n + 1 : ℕ) : ℝ) * ((Nat.log 2 n : ℝ) + 3) *
      (16 + 800 * 42 ^ 2) * B / hierarchyGammaLL n ≤
      (12 * (16 + 800 * 42 ^ 2) * (100 * rsConstant ^ 2 * 42 ^ 2)) * n * B * LK := by
    have hrs : (0 : ℝ) ≤ rsConstant := by norm_num [rsConstant]
    calc
      _ = ((2 * n + 1 : ℕ) : ℝ) * ((Nat.log 2 n : ℝ) + 3) *
          (16 + 800 * 42 ^ 2) * B *
          ((100 * rsConstant ^ 2 * 42 ^ 2) * ((logL n : ℝ) ^ 2 * (logL (logL n) : ℝ) ^ 2)) := by
        rw [div_eq_mul_one_div, hierarchyGammaLL_inverse]
      _ ≤ (3 * n) * (4 * (logL n : ℝ)) * (16 + 800 * 42 ^ 2) * B *
          ((100 * rsConstant ^ 2 * 42 ^ 2) * ((logL n : ℝ) ^ 2 * (logL (logL n) : ℝ) ^ 2)) := by
        gcongr
      _ = _ := by rw [hLK]; ring
  unfold hierarchyRawBoundLL hierarchyConstantLL
  linarith

def hierarchyBudgetLL (n : ℕ) (B : ℝ) : ℕ :=
  ⌈hierarchyConstantLL * n * B * ((logL n : ℝ) ^ 3 * (logL (logL n) : ℝ) ^ 2)⌉₊

theorem hierarchyBudgetLL_le {n : ℕ} (hn : 2 ≤ n) {B : ℝ} (hB : 1 ≤ B) :
    (hierarchyBudgetLL n B : ℝ) ≤
      (hierarchyConstantLL + 1) * n * B * ((logL n : ℝ) ^ 3 * (logL (logL n) : ℝ) ^ 2) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hL1 : (1 : ℝ) ≤ (logL n : ℝ) := by exact_mod_cast one_le_logL' n
  have hK1 : (1 : ℝ) ≤ (logL (logL n) : ℝ) := by exact_mod_cast one_le_logL' _
  have hbase : (1 : ℝ) ≤ (n : ℝ) * B * ((logL n : ℝ) ^ 3 * (logL (logL n) : ℝ) ^ 2) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hn1 hB)
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL1) (one_le_pow₀ hK1))
  have hc := hierarchyConstantLL_pos
  have hceil := Nat.ceil_lt_add_one
    (show 0 ≤ hierarchyConstantLL * n * B * ((logL n : ℝ) ^ 3 * (logL (logL n) : ℝ) ^ 2) by
      positivity)
  unfold hierarchyBudgetLL
  nlinarith

variable {V : Type} [Fintype V] [DecidableEq V]

/-- An actual public refinement program, with all mathematical infrastructure
instantiated by the repository's proved hierarchy and guard theorems. -/
def suppliedHierarchyProgLL (P : Pkg V) (B : ℝ) : Comp (Finset V) ℝ (WeightedGraph V) :=
  Hierarchy.refine rackeShah_hierarchyBound 42 (hierarchyGammaLL (Fintype.card V))
    (hierarchyGammaLL_pos _).le (fun _ hB => by positivity)
    ⌈hierarchyGammaLL (Fintype.card V) * B⌉₊ B P

theorem suppliedHierarchyProgLL_spec (P : Pkg V) (B : ℝ) (G : WeightedGraph V)
    (hn : 2 ≤ Fintype.card V) (hpos : 0 < mincutValue G) (hB : 1 ≤ B)
    (hlc : P.H.LeafChildless) (hm : P.m ≤ 2 * Fintype.card V + 1)
    (hprom : ∃ S, IsMinCut G S ∧ P.H.rep (P.H.canon G) S ≤ B * mincutValue G) :
    IsWeakSkeleton G ((suppliedHierarchyProgLL P B).eval G.cut) ∧
      ((suppliedHierarchyProgLL P B).cost G.cut : ℝ) ≤
        hierarchyConstantLL * Fintype.card V * B *
          ((logL (Fintype.card V) : ℝ) ^ 3 * (logL (logL (Fintype.card V)) : ℝ) ^ 2) := by
  have hs := refine_weakSkeleton_of_good rackeShah_hierarchyBound G hn hpos
    (by norm_num : (1 : ℝ) ≤ 42) (hierarchyGammaLL_pos (Fintype.card V))
    (hierarchyGammaLL_calibration (Fintype.card V)) (one_le_aLK' (Fintype.card V))
    (fun P : Pkg V => P.H.LeafChildless)
    (fun _ hP => Hier.ConstantCutGuard.guardFor constantCutGuard_42 hP)
    (fun J => (hbPkg_spec rackeShah_hierarchyBound J).2.1) (le_refl _)
    (fun _ hB => by positivity) hB P hlc hm hprom
  refine ⟨hs.1, hs.2.trans ?_⟩
  exact hierarchyRawBoundLL_le hn hB

/-- Uniform public cap. Neither an optimum nor its value is a selector input. -/
def suppliedHierarchyTreeLL (P : Pkg V) (B : ℝ) :
    DTree (Finset V) ℝ (Option (WeightedGraph V)) (hierarchyBudgetLL (Fintype.card V) B) :=
  (suppliedHierarchyProgLL P B).toDTree (hierarchyBudgetLL (Fintype.card V) B)

/-- Correctness discharges the cap for every honest promised input. -/
theorem suppliedHierarchyTreeLL_correct (P : Pkg V) (B : ℝ) (G : WeightedGraph V)
    (hn : 2 ≤ Fintype.card V) (hpos : 0 < mincutValue G) (hB : 1 ≤ B)
    (hlc : P.H.LeafChildless) (hm : P.m ≤ 2 * Fintype.card V + 1)
    (hprom : ∃ S, IsMinCut G S ∧ P.H.rep (P.H.canon G) S ≤ B * mincutValue G) :
    ∃ F, (suppliedHierarchyTreeLL P B).eval G.cut = some F ∧ IsWeakSkeleton G F := by
  have hs := suppliedHierarchyProgLL_spec P B G hn hpos hB hlc hm hprom
  refine ⟨(suppliedHierarchyProgLL P B).eval G.cut, ?_, hs.1⟩
  apply toDTree_eval
  have hcost : ((suppliedHierarchyProgLL P B).cost G.cut : ℝ) ≤
      (hierarchyBudgetLL (Fintype.card V) B : ℝ) := hs.2.trans (Nat.le_ceil _)
  exact_mod_cast hcost

/-- Every oracle obeys the public depth-independent linear-in-B cap. -/
theorem suppliedHierarchyTreeLL_cost (P : Pkg V) (B : ℝ)
    (hn : 2 ≤ Fintype.card V) (hB : 1 ≤ B) (read : Finset V → ℝ) :
    ((suppliedHierarchyTreeLL P B).cost read : ℝ) ≤
      (hierarchyConstantLL + 1) * Fintype.card V * B *
        ((logL (Fintype.card V) : ℝ) ^ 3 * (logL (logL (Fintype.card V)) : ℝ) ^ 2) := by
  have hcost := DTree.cost_le (suppliedHierarchyTreeLL P B) read
  exact (Nat.cast_le.mpr hcost).trans (hierarchyBudgetLL_le hn hB)

/-- The standalone supplied-hierarchy endpoint with the Räcke–Shah quality:
`O(n B L(n)³ L(L(n))²)` queries. -/
theorem supplied_hierarchy_log3loglog2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : Type) [Fintype W] [DecidableEq W]
      (P : Pkg W) (B : ℝ), 2 ≤ Fintype.card W → 1 ≤ B →
      P.H.LeafChildless → P.m ≤ 2 * Fintype.card W + 1 →
      ∃ q : ℕ, (q : ℝ) ≤ C * Fintype.card W * B *
          ((logL (Fintype.card W) : ℝ) ^ 3 * (logL (logL (Fintype.card W)) : ℝ) ^ 2) ∧
        ∃ D : DTree (Finset W) ℝ (Option (WeightedGraph W)) q,
          (∀ read, D.cost read ≤ q) ∧
          ∀ G : WeightedGraph W, 0 < mincutValue G →
            (∃ S, IsMinCut G S ∧ P.H.rep (P.H.canon G) S ≤ B * mincutValue G) →
            ∃ F, D.eval G.cut = some F ∧ IsWeakSkeleton G F := by
  refine ⟨hierarchyConstantLL + 1, by linarith [hierarchyConstantLL_pos],
    fun W _ _ P B hn hB hlc hm => ?_⟩
  refine ⟨hierarchyBudgetLL (Fintype.card W) B, hierarchyBudgetLL_le hn hB,
    suppliedHierarchyTreeLL P B, fun read => DTree.cost_le _ read, ?_⟩
  intro G hpos hprom
  exact suppliedHierarchyTreeLL_correct P B G hn hpos hB hlc hm hprom


end
end CutQueryComplexity.UndirectedClosure
