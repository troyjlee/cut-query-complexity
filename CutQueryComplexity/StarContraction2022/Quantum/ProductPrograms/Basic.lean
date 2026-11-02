import CutQueryComplexity.StarContraction2022.Quantum.CutProduct
import CutQueryComplexity.StarContraction2022.Quantum.RandomizedCompiler
import CutQueryComplexity.StarContraction2022.Quantum.FiniteCutEncoding
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Semiring

/-! # Public randomized product-query programs and their physical implementation

The tree, finite work space, circuit, initialization and readout are chosen
before the hidden graph. Every virtual call is replaced by the implemented
compute/copy/uncompute product oracle, costing twelve times the product bit
width. Honest output laws are exact. Arbitrary physical answer tables retain
the same valid circuit and physical count, without a graph-simulation claim.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms

noncomputable section
open QuantumQueryComplexity
open scoped Classical Matrix

abbrev ProductTree (n : ℕ) (O : Type) (q : ℕ) :=
  RTree (Finset (Fin n)) (ProductAnswer n 1) O q

abbrev Candidate (n : ℕ) := FiniteCutResult n 1

/-- Public binary width shared by row isolation and the final schedules. -/
def logWidth (n : ℕ) : ℕ := 1 + Nat.clog 2 (n + 2)

/-- The branch threshold is public, not a measured degree. -/
def rootThreshold (n : ℕ) : ℕ := ⌈Real.sqrt (n : ℝ)⌉₊

theorem logWidth_pos (n : ℕ) : 0 < logWidth n := by
  unfold logWidth
  omega

theorem le_two_pow_logWidth (n : ℕ) : n + 2 ≤ 2 ^ logWidth n := by
  have h := Nat.le_pow_clog (by decide : 1 < 2) (n + 2)
  simp only [logWidth, Nat.pow_add, Nat.pow_one]
  omega

theorem productBits_le_logWidth (n : ℕ) : productBits n 1 ≤ logWidth n := by
  have h := Nat.clog_mono_right 2 (show n + 1 ≤ n + 2 by omega)
  simp only [productBits, Nat.one_mul, logWidth]
  omega

@[simp] theorem rootThreshold_zero : rootThreshold 0 = 0 := by
  simp [rootThreshold]

theorem sqrt_le_rootThreshold (n : ℕ) : Real.sqrt (n : ℝ) ≤ rootThreshold n :=
  Nat.le_ceil _

theorem rootThreshold_pos {n : ℕ} (hn : 0 < n) : 0 < rootThreshold n := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hr := sqrt_le_rootThreshold n
  by_contra h
  have hz : rootThreshold n = 0 := by omega
  rw [hz, Nat.cast_zero] at hr
  linarith

theorem rootThreshold_le_n (n : ℕ) : rootThreshold n ≤ n := by
  by_cases hn : n = 0
  · simp [hn]
  · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    apply Nat.ceil_le.mpr
    exact Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩

theorem rootThreshold_le_two_sqrt {n : ℕ} (hn : 1 ≤ n) :
    (rootThreshold n : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
  have hs : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    simpa only [Real.sqrt_one] using
      Real.sqrt_le_sqrt (show (1 : ℝ) ≤ n by exact_mod_cast hn)
  have hc : (rootThreshold n : ℝ) < Real.sqrt (n : ℝ) + 1 :=
    Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
  linarith

/-- Absence is harmless; every retained result must be an exact original cut. -/
def CandidateSound {n : ℕ} (G : CapacityGraph (Fin n) 1) : Candidate n → Prop
  | none => True
  | some (S, a) => (⟨S, decodeCutAnswer a⟩ : CutResult (Fin n)).Sound G.toWeighted

@[simp] theorem candidateSound_none {n : ℕ} (G : CapacityGraph (Fin n) 1) :
    CandidateSound G none := trivial

theorem candidateSound_mincut_le {n : ℕ} {G : CapacityGraph (Fin n) 1}
    {S : Finset (Fin n)} {a : CutAnswer n 1} (h : CandidateSound G (some (S, a))) :
    mincutValue G.toWeighted ≤ decodeCutAnswer a :=
  CutResult.Sound.mincut_le h

/-- Supported-output soundness does not assume the result is minimum. -/
def ProductTreeSound {n q : ℕ} (T : ProductTree n (Candidate n) q)
    (G : CapacityGraph (Fin n) 1) : Prop :=
  ∀ o ∈ (T.eval (productRead G)).support, CandidateSound G o

/-- Includes the inverse calls needed to leave the product scratch clean. -/
def physicalQueries (n q : ℕ) : ℕ := 12 * productBits n 1 * q

theorem physicalQueries_eq (n q : ℕ) :
    physicalQueries n q = q * (12 * productBits n 1) := Nat.mul_comm _ _

@[simp] theorem physicalQueries_zero (n : ℕ) : physicalQueries n 0 = 0 := by
  simp [physicalQueries]

local instance productAlphabetInhabited (n : ℕ) : Inhabited (ProductAnswer n 1) :=
  ⟨productZero n 1⟩

/-- Use the standard structural decisions without unfolding deep workspaces. -/
local instance basisDecidableEq {I A D : Type} [DecidableEq I]
    [DecidableEq A] [DecidableEq D] : DecidableEq (QBasis I A D) :=
  inferInstanceAs (DecidableEq (Option I × Option A × D))

local instance workspaceDecidableEq {I A D : Type} [DecidableEq I]
    [DecidableEq A] [DecidableEq D] : DecidableEq (QBasis I A D × A) :=
  inferInstanceAs (DecidableEq ((Option I × Option A × D) × A))

variable {n q : ℕ} {O : Type} [Fintype O] [DecidableEq O]

abbrev productTreeWork (T : ProductTree n O q) : Type :=
  QBasis (Finset (Fin n)) (ProductAnswer n 1) (randomizedWork T) × ProductAnswer n 1

/-- Public composition of the actual randomized and exact product compilers. -/
def productTreeAlg (T : ProductTree n O q) : CutQAlg n 1 O (productTreeWork T) :=
  compileProductAlg n 1 (randomizedAlg T) q

/-- The compiled algorithm's actual finite schedule, including idle padding. -/
def productTreeRoutine (T : ProductTree n O q) :
    QRoutine (Finset (Fin n)) (CutAnswer n 1) (productTreeWork T) where
  len := physicalQueries n q
  step := (productTreeAlg T).step
  step_unitary := (productTreeAlg T).step_unitary

@[simp] theorem productTreeRoutine_len (T : ProductTree n O q) :
    (productTreeRoutine T).len = 12 * productBits n 1 * q := rfl

/-- This operational equality holds even for inconsistent physical tables. -/
theorem productTreeRoutine_state (T : ProductTree n O q)
    (read : Finset (Fin n) → CutAnswer n 1) :
    (productTreeRoutine T).run read *ᵥ (productTreeAlg T).init =
      (productTreeAlg T).state read (physicalQueries n q) :=
  ((productTreeAlg T).state_eq_runUpto (productTreeRoutine T) rfl read
    (physicalQueries n q)).symm

theorem productTreeRoutine_isQState (T : ProductTree n O q)
    (read : Finset (Fin n) → CutAnswer n 1) :
    IsQState ((productTreeRoutine T).run read *ᵥ (productTreeAlg T).init) := by
  rw [productTreeRoutine_state]
  exact (productTreeAlg T).state_isQState read (physicalQueries n q)

/-- Only honest graph replies are used for the clean-subspace simulation. -/
theorem productTreeAlg_state (T : ProductTree n O q) (G : CapacityGraph (Fin n) 1) :
    (productTreeAlg T).state (capacityRead G) (physicalQueries n q) =
      productCallEmbed (productZero n 1) ((randomizedAlg T).state (productRead G) q) := by
  rw [productTreeAlg, physicalQueries_eq]
  exact compileProductAlg_state (randomizedAlg T) q G

theorem productTreeAlg_prob (T : ProductTree n O q) (G : CapacityGraph (Fin n) 1)
    (o : O) :
    (productTreeAlg T).prob (capacityRead G) (physicalQueries n q) o =
      (((RTree.run (productRead G) T).map Prod.fst) o).toReal := by
  rw [productTreeAlg, physicalQueries_eq, compileProductAlg_prob, randomizedAlg_prob]

/-- Exact event law, with no error or success assumption about the source tree. -/
theorem productTreeAlg_successProb (T : ProductTree n O q)
    (G : CapacityGraph (Fin n) 1) (Good : O → Prop) [DecidablePred Good] :
    goodProb (productTreeAlg T).readout Good
        ((productTreeAlg T).state (capacityRead G) (physicalQueries n q)) =
      T.successProb (productRead G) Good := by
  rw [goodProb_eq_sum]
  change (∑ o, if Good o then
    (productTreeAlg T).prob (capacityRead G) (physicalQueries n q) o else 0) = _
  simp_rw [productTreeAlg_prob]
  rw [← RandomizedCompiler.pmf_event_toReal]
  rw [PMF.toOuterMeasure_map_apply]
  rfl

theorem productTree_cost (T : ProductTree n O q)
    (read : Finset (Fin n) → ProductAnswer n 1) {out : O × ℕ}
    (h : out ∈ (RTree.run read T).support) : out.2 ≤ q := RTree.cost_le T read h

#print axioms le_two_pow_logWidth
#print axioms productBits_le_logWidth
#print axioms rootThreshold_pos
#print axioms rootThreshold_le_n
#print axioms rootThreshold_le_two_sqrt
#print axioms candidateSound_mincut_le
#print axioms productTreeRoutine_len
#print axioms productTreeRoutine_state
#print axioms productTreeRoutine_isQState
#print axioms productTreeAlg_state
#print axioms productTreeAlg_prob
#print axioms productTreeAlg_successProb
#print axioms productTree_cost

end
end CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms
