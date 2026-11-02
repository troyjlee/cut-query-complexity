import CutQueryComplexity.Spanner.Trial
import CutQueryComplexity.Probability.Expectation
import Mathlib.Probability.Distributions.Uniform

/-! # Fair cluster coins: expected reports (D3; source `lem:spanner`)

Coins are fair and independent, one per potential cluster center (`coinPMF`). For one phase
with frozen state `st`:

* `expect_reportsOf_le`: a vertex reports, in expectation, at most two old clusters. Its
  reports lie among the adjacent clusters with no sampled adjacent cluster of smaller minimum key
  (`reportsOf_subset`). A cluster of key rank `j` needs `j` specific fair coins to come up
  `false`, probability `2^{-j}`, and the ranks are distinct.
* `clusters_step_subset`: only sampled old clusters survive, so the expected number of clusters
  halves (`expect_card_sampled`).
* `totalReports_final_le`: in the final phase, with no sampled cluster, each vertex reports at
  most every cluster.
-/

namespace CutQueryComplexity
namespace Spanner

open Finset Probability
open scoped ENNReal

noncomputable section

attribute [local instance 10] Classical.propDecidable

variable {V : Type} [Fintype V] [DecidableEq V] {κ : Type} [LinearOrder κ]

/-- Independent fair coins, one per potential center. -/
def coinPMF (V : Type) [Fintype V] [DecidableEq V] : PMF (V → Bool) := PMF.uniformOfFintype (V → Bool)

/-- The probability that the coins on `T` take prescribed values. -/
theorem mass_coins_eq (T : Finset V) (b : V → Bool) :
    mass (coinPMF V) (fun c => ∀ D ∈ T, c D = b D) = (2⁻¹ : ℝ≥0∞) ^ T.card := by
  set F := Fintype.piFinset fun D => if D ∈ T then ({b D} : Finset Bool) else univ
  have hF : ∀ c : V → Bool, c ∈ F ↔ ∀ D ∈ T, c D = b D := by
    intro c
    simp only [F, Fintype.mem_piFinset]
    constructor
    · intro h D hD; have := h D; simpa [hD] using this
    · intro h D
      by_cases hD : D ∈ T
      · simp [hD, h D hD]
      · simp [hD]
  have hprod : F.card = 2 ^ Tᶜ.card := by
    rw [Fintype.card_piFinset, ← prod_mul_prod_compl T]
    have h1 : ∏ D ∈ T, (if D ∈ T then ({b D} : Finset Bool) else univ).card = 1 :=
      prod_eq_one fun D hD => by simp [hD]
    have h2 : ∏ D ∈ Tᶜ, (if D ∈ T then ({b D} : Finset Bool) else univ).card = 2 ^ Tᶜ.card := by
      rw [← prod_const]; exact prod_congr rfl fun D hD => by simp [mem_compl.mp hD]
    rw [h1, h2, one_mul]
  have hset : {c : V → Bool | ∀ D ∈ T, c D = b D} = ↑F := by ext c; simp [hF]
  rw [mass, coinPMF, hset, PMF.toOuterMeasure_uniformOfFintype_apply]
  rw [show Fintype.card (↑(↑F : Set (V → Bool))) = F.card from by simp, hprod, Fintype.card_fun,
    Fintype.card_bool]
  have hcard : Fintype.card V = T.card + Tᶜ.card := (card_add_card_compl T).symm
  rw [hcard, pow_add]
  push_cast
  rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inr (by simp)) (Or.inr (by simp)), mul_assoc,
    ENNReal.inv_mul_cancel (by simp) (by simp), mul_one, ENNReal.inv_pow]

theorem mass_coin_true (c0 : V) : mass (coinPMF V) (fun c => c c0 = true) = 2⁻¹ := by
  have := mass_coins_eq {c0} (fun _ => true)
  simpa using this

omit [Fintype V] [DecidableEq V] in
/-- Expected size of a filtered set, as a sum of probabilities. -/
theorem expect_card_filter {α : Type} (p : PMF α) (A : Finset V) (P : α → V → Prop)
    [∀ x, DecidablePred (P x)] :
    expect p (fun x => ((A.filter (P x)).card : ℝ≥0∞)) = ∑ D ∈ A, mass p (fun x => P x D) := by
  have : ∀ x, ((A.filter (P x)).card : ℝ≥0∞) = ∑ D ∈ A, if P x D then 1 else 0 := fun x => by
    rw [card_filter]; push_cast; rfl
  simp only [this, expect_sum]
  refine sum_congr rfl fun D _ => ?_
  have h := expect_indicator p (fun x => P x D) 1
  rw [one_mul] at h
  convert h using 3
  congr

omit [Fintype V] in
/-- Distinct ranks give a geometric bound. -/
theorem sum_half_pow_rank_le (A : Finset V) (g : V → κ) (hg : Set.InjOn g A) :
    ∑ D ∈ A, (2⁻¹ : ℝ≥0∞) ^ (A.filter fun D' => g D' < g D).card ≤ 2 := by
  set r : V → ℕ := fun D => (A.filter fun D' => g D' < g D).card
  have hr : Set.InjOn r A := by
    intro D hD D' hD' hrr
    by_contra hne
    rcases lt_or_gt_of_ne (fun h => hne (hg hD hD' h)) with h | h
    · have : r D < r D' := card_lt_card ⟨fun x hx => by
          simp only [mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.trans h⟩,
        fun hsub => by
          have := hsub (mem_filter.mpr ⟨hD, h⟩); simp at this⟩
      omega
    · have : r D' < r D := card_lt_card ⟨fun x hx => by
          simp only [mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.trans h⟩,
        fun hsub => by
          have := hsub (mem_filter.mpr ⟨hD', h⟩); simp at this⟩
      omega
  have hrange : ∀ D ∈ A, r D ∈ range A.card := fun D hD => by
    rw [mem_range]
    exact card_lt_card ⟨filter_subset _ _, fun hsub => by
      have := hsub hD; simp at this⟩
  calc ∑ D ∈ A, (2⁻¹ : ℝ≥0∞) ^ r D = ∑ j ∈ A.image r, (2⁻¹ : ℝ≥0∞) ^ j :=
        (sum_image hr).symm
    _ ≤ ∑ j ∈ range A.card, (2⁻¹ : ℝ≥0∞) ^ j :=
        sum_le_sum_of_subset (fun j hj => by
          obtain ⟨D, hD, rfl⟩ := mem_image.mp hj; exact hrange D hD)
    _ ≤ ∑' j, (2⁻¹ : ℝ≥0∞) ^ j := ENNReal.sum_le_tsum _
    _ = 2 := by rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]

variable (key : Sym2 V → κ)

/-- The clusters reported by `a`. -/
def reportsOf (coin : V → Bool) (st : State V) (a : V) : Finset V :=
  univ.filter (Reported key coin st a)

/-- All reports of a phase. -/
def totalReports (coin : V → Bool) (st : State V) : ℕ := ∑ a, (reportsOf key coin st a).card

/-- The current cluster centers. -/
def clusters (st : State V) : Finset V := univ.filter fun c => ∃ a, st.lab a = some c

/-- The old clusters adjacent to `a` through residual pairs. -/
def adjCl (st : State V) (a : V) : Finset V := univ.filter fun D => (toClus st a D).Nonempty

/-- The key of the minimum pair from `a` into `D` (a default when there is none). -/
def clKey (st : State V) (a : V) (k0 : κ) (D : V) : κ :=
  ((minNbr key a (toClus st a D)).map fun y => key s(a, y)).getD k0

variable {key}

theorem clKey_eq {st : State V} {a D y : V} (k0 : κ) (h : minNbr key a (toClus st a D) = some y) :
    clKey key st a k0 D = key s(a, y) := by
  simp [clKey, h]

/-- Reports lie among adjacent clusters with no smaller sampled adjacent cluster. -/
theorem reportsOf_subset (coin : V → Bool) (st : State V) (a : V) (k0 : κ) :
    reportsOf key coin st a ⊆ (adjCl st a).filter fun D => ∀ D' ∈ adjCl st a,
      clKey key st a k0 D' < clKey key st a k0 D → coin D' = false := by
  intro D hD
  obtain ⟨hns, y, hy, hmin⟩ := (mem_filter.mp hD).2
  have hyC := (minNbr_some key hy).1
  refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, ⟨y, hyC⟩⟩, fun D' hD' hlt => ?_⟩
  by_contra hc
  have hc' : coin D' = true := by simpa using hc
  obtain ⟨y', hy'⟩ := exists_minNbr key (mem_filter.mp hD').2 (a := a)
  obtain ⟨hy'C, -⟩ := minNbr_some key hy'
  obtain ⟨hy'E, hy'D⟩ := mem_toClus.mp hy'C
  have hy'S : y' ∈ toSamp coin st a := mem_toSamp.mpr ⟨hy'E, D', hy'D, hc'⟩
  obtain ⟨z, hz⟩ := exists_minNbr key ⟨y', hy'S⟩ (a := a)
  have hzle := (minNbr_some key hz).2 y' hy'S
  have h1 := hmin z hz
  rw [clKey_eq k0 hy', clKey_eq k0 hy] at hlt
  exact absurd (h1.trans hzle) (not_le.mpr hlt)

/-- Minimum keys of distinct adjacent clusters are distinct. -/
theorem clKey_injOn (hinj : Function.Injective key) (st : State V) (a : V) (k0 : κ) :
    Set.InjOn (clKey key st a k0) (adjCl st a) := by
  intro D hD D' hD' heq
  obtain ⟨y, hy⟩ := exists_minNbr key (mem_filter.mp hD).2 (a := a)
  obtain ⟨y', hy'⟩ := exists_minNbr key (mem_filter.mp hD').2 (a := a)
  rw [clKey_eq k0 hy, clKey_eq k0 hy'] at heq
  have hp := hinj heq
  have hyy : y = y' := by
    rcases Sym2.eq_iff.mp hp with ⟨-, h⟩ | ⟨h1, h2⟩
    · exact h
    · rw [← h1, h2]
  obtain ⟨-, hyD⟩ := mem_toClus.mp (minNbr_some key hy).1
  obtain ⟨-, hy'D⟩ := mem_toClus.mp (minNbr_some key hy').1
  rw [hyy, hy'D] at hyD
  exact (Option.some_injective _ hyD).symm

/-- **A vertex reports at most two clusters in expectation.** -/
theorem expect_reportsOf_le (hinj : Function.Injective key) (st : State V) (a : V) :
    expect (coinPMF V) (fun c => ((reportsOf key c st a).card : ℝ≥0∞)) ≤ 2 := by
  by_cases hV : Nonempty κ
  swap
  · -- no keys: then no pair has a key, so `V` has no pairs at all
    exact absurd ⟨key s(a, a)⟩ hV
  obtain ⟨k0⟩ := hV
  set A := adjCl st a
  set P : (V → Bool) → V → Prop := fun c D => ∀ D' ∈ A,
    clKey key st a k0 D' < clKey key st a k0 D → c D' = false
  calc expect (coinPMF V) (fun c => ((reportsOf key c st a).card : ℝ≥0∞))
      ≤ expect (coinPMF V) (fun c => ((A.filter (P c)).card : ℝ≥0∞)) :=
        expect_mono_on_support _ fun c _ => by
          exact_mod_cast card_le_card (reportsOf_subset c st a k0)
    _ = ∑ D ∈ A, mass (coinPMF V) (fun c => P c D) := expect_card_filter _ A P
    _ = ∑ D ∈ A, (2⁻¹ : ℝ≥0∞) ^
          (A.filter fun D' => clKey key st a k0 D' < clKey key st a k0 D).card := by
        refine sum_congr rfl fun D _ => ?_
        rw [← mass_coins_eq _ (fun _ => false)]
        congr 1; funext c
        simp only [P, mem_filter, and_imp]
    _ ≤ 2 := sum_half_pow_rank_le A _ (clKey_injOn hinj st a k0)

/-- **A phase has at most `2n` reports in expectation.** -/
theorem expect_totalReports_le (hinj : Function.Injective key) (st : State V) :
    expect (coinPMF V) (fun c => (totalReports key c st : ℝ≥0∞)) ≤ 2 * Fintype.card V := by
  simp only [totalReports, Nat.cast_sum]
  rw [expect_sum]
  calc ∑ a ∈ univ, expect (coinPMF V) (fun c => ((reportsOf key c st a).card : ℝ≥0∞))
      ≤ ∑ _a ∈ (univ : Finset V), (2 : ℝ≥0∞) := sum_le_sum fun a _ => expect_reportsOf_le hinj st a
    _ = 2 * Fintype.card V := by simp [mul_comm]

/-- Only sampled old clusters survive a phase. -/
theorem clusters_step_subset (coin : V → Bool) (st : State V) :
    clusters (step key coin st) ⊆ (clusters st).filter fun c => coin c = true := by
  intro c hc
  obtain ⟨a, ha⟩ := (mem_filter.mp hc).2
  simp only [step, newLab] at ha
  split_ifs at ha with hs
  · obtain ⟨c', hc', hcoin⟩ := hs
    rw [hc'] at ha; cases ha
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, a, hc'⟩, hcoin⟩
  · cases hz : minNbr key a (toSamp coin st a) with
    | none => rw [hz] at ha; cases ha
    | some z =>
        rw [hz, Option.bind_some] at ha
        obtain ⟨-, c', hzc, hcoin⟩ := mem_toSamp.mp (minNbr_some key hz).1
        rw [ha] at hzc; cases hzc
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, z, ha⟩, hcoin⟩

/-- The expected number of sampled clusters is half the number of clusters. -/
theorem expect_card_sampled (C : Finset V) :
    expect (coinPMF V) (fun c => ((C.filter fun d => c d = true).card : ℝ≥0∞)) =
      C.card * 2⁻¹ := by
  rw [expect_card_filter (coinPMF V) C (fun c d => c d = true)]
  simp [mass_coin_true]

/-- Reports go to existing clusters, so the final phase has at most `n |C|` reports. -/
theorem totalReports_le (coin : V → Bool) (st : State V) :
    totalReports key coin st ≤ Fintype.card V * (clusters st).card := by
  unfold totalReports
  calc ∑ a, (reportsOf key coin st a).card ≤ ∑ _a : V, (clusters st).card :=
        sum_le_sum fun a _ => card_le_card fun D hD => by
          obtain ⟨-, y, hy, -⟩ := (mem_filter.mp hD).2
          obtain ⟨-, hyD⟩ := mem_toClus.mp (minNbr_some key hy).1
          exact mem_filter.mpr ⟨mem_univ _, y, hyD⟩
    _ = _ := by simp

/-! ## Coin sequences -/

omit [Fintype V] [DecidableEq V] in
/-- Resampling one coordinate of a uniform product leaves it uniform. -/
theorem expect_uniform_resample {ι X : Type} [Fintype ι] [DecidableEq ι] [Fintype X]
    [DecidableEq X] [Nonempty X] (j : ι) (f : (ι → X) → ℝ≥0∞) :
    expect (PMF.uniformOfFintype (ι → X)) f =
      expect (PMF.uniformOfFintype (ι → X)) (fun cs =>
        expect (PMF.uniformOfFintype X) (fun c => f (Function.update cs j c))) := by
  unfold Probability.expect
  simp only [tsum_fintype, PMF.uniformOfFintype_apply, ← mul_sum]
  -- the bijection `(cs, c) ↦ (update cs j c, cs j)`
  let e : (ι → X) × X ≃ (ι → X) × X :=
    { toFun := fun q => (Function.update q.1 j q.2, q.1 j)
      invFun := fun q => (Function.update q.1 j q.2, q.1 j)
      left_inv := fun q => by simp
      right_inv := fun q => by simp }
  have hsum : ∑ cs : ι → X, ∑ c : X, f (Function.update cs j c) =
      (Fintype.card X : ℝ≥0∞) * ∑ cs : ι → X, f cs := by
    rw [← Fintype.sum_prod_type']
    rw [show (∑ q : (ι → X) × X, f (Function.update q.1 j q.2)) =
        ∑ q : (ι → X) × X, f (e q).1 from rfl]
    rw [Fintype.sum_equiv e (fun q => f (e q).1) (fun q => f q.1) (fun q => rfl),
      Fintype.sum_prod_type]
    simp [mul_sum, mul_comm]
  have hX : (Fintype.card X : ℝ≥0∞) ≠ 0 := by simp
  have hX' : (Fintype.card X : ℝ≥0∞) ≠ ⊤ := by simp
  congr 1
  rw [hsum, ← mul_assoc, ENNReal.inv_mul_cancel hX hX', one_mul]

/-- Phase coins from a finite array, with no sampled cluster after it ends. -/
def extCoins {K : ℕ} (cs : Fin K → V → Bool) (j : ℕ) : V → Bool :=
  if h : j < K then cs ⟨j, h⟩ else fun _ => false

/-- The state after `j` phases depends only on the coins of those phases. -/
theorem runPhases_congr (key : Sym2 V → κ) {coins coins' : ℕ → V → Bool} (E0 : Finset (Sym2 V)) :
    ∀ j, (∀ i < j, coins i = coins' i) → runPhases key coins E0 j = runPhases key coins' E0 j
  | 0, _ => rfl
  | j + 1, h => by
      simp only [runPhases]
      rw [h j (Nat.lt_succ_self j), runPhases_congr key E0 j fun i hi => h i (Nat.lt_succ_of_lt hi)]

omit [Fintype V] [DecidableEq V] in
theorem extCoins_update {K : ℕ} (cs : Fin K → V → Bool) (j : Fin K) (c : V → Bool) :
    extCoins (Function.update cs j c) j = c ∧
      ∀ i < (j : ℕ), extCoins (Function.update cs j c) i = extCoins cs i := by
  refine ⟨by simp [extCoins], fun i hi => ?_⟩
  have hiK : i < K := hi.trans j.isLt
  simp only [extCoins, hiK, ↓reduceDIte]
  rw [Function.update_of_ne]
  intro h; rw [← h] at hi; simp at hi

/-- The uniform distribution on coin arrays. -/
def coinSeqPMF (V : Type) [Fintype V] [DecidableEq V] (K : ℕ) : PMF (Fin K → V → Bool) :=
  PMF.uniformOfFintype (Fin K → V → Bool)

theorem coinSeq_resample {K : ℕ} (j : Fin K) (f : (Fin K → V → Bool) → ℝ≥0∞) :
    expect (coinSeqPMF V K) f = expect (coinSeqPMF V K) (fun cs =>
      expect (coinPMF V) (fun c => f (Function.update cs j c))) :=
  expect_uniform_resample j f

variable (key)

/-- **Each sampled phase has at most `2n` reports in expectation.** -/
theorem expect_phase_reports (hinj : Function.Injective key) (E0 : Finset (Sym2 V)) {K : ℕ}
    (j : Fin K) :
    expect (coinSeqPMF V K) (fun cs =>
      (totalReports key (extCoins cs j) (runPhases key (extCoins cs) E0 j) : ℝ≥0∞)) ≤
      2 * Fintype.card V := by
  rw [coinSeq_resample j]
  refine expect_le_of_le_on_support _ fun cs _ => ?_
  have h : ∀ c, (totalReports key (extCoins (Function.update cs j c) j)
      (runPhases key (extCoins (Function.update cs j c)) E0 j) : ℝ≥0∞) =
      totalReports key c (runPhases key (extCoins cs) E0 j) := fun c => by
    obtain ⟨h1, h2⟩ := extCoins_update cs j c
    rw [h1, runPhases_congr key E0 j h2]
  simp only [h]
  exact expect_totalReports_le hinj _

theorem clusters_init (E0 : Finset (Sym2 V)) : clusters (init E0) = univ := by
  ext c; simp [clusters, init]

/-- **The expected cluster count halves each sampled phase.** -/
theorem expect_clusters_le (E0 : Finset (Sym2 V)) {K : ℕ} :
    ∀ j ≤ K, expect (coinSeqPMF V K) (fun cs =>
      ((clusters (runPhases key (extCoins cs) E0 j)).card : ℝ≥0∞)) ≤
      Fintype.card V * (2⁻¹ : ℝ≥0∞) ^ j
  | 0, _ => by simp [runPhases, clusters_init]
  | j + 1, hj => by
      have ih := expect_clusters_le E0 (K := K) j (by omega)
      set jj : Fin K := ⟨j, by omega⟩
      calc expect (coinSeqPMF V K) (fun cs =>
            ((clusters (runPhases key (extCoins cs) E0 (j + 1))).card : ℝ≥0∞))
          ≤ expect (coinSeqPMF V K) (fun cs =>
            (((clusters (runPhases key (extCoins cs) E0 j)).filter
              fun d => extCoins cs j d = true).card : ℝ≥0∞)) :=
            expect_mono_on_support _ fun cs _ => by
              exact_mod_cast card_le_card (clusters_step_subset _ _)
        _ = expect (coinSeqPMF V K) (fun cs => expect (coinPMF V) (fun c =>
            (((clusters (runPhases key (extCoins cs) E0 j)).filter
              fun d => c d = true).card : ℝ≥0∞))) := by
            rw [coinSeq_resample jj]
            congr 1; funext cs; congr 1; funext c
            obtain ⟨h1, h2⟩ := extCoins_update cs jj c
            rw [show (j : ℕ) = (jj : ℕ) from rfl, h1, runPhases_congr key E0 jj h2]
        _ = expect (coinSeqPMF V K) (fun cs =>
            ((clusters (runPhases key (extCoins cs) E0 j)).card : ℝ≥0∞) * 2⁻¹) := by
            congr 1; funext cs; exact expect_card_sampled _
        _ = expect (coinSeqPMF V K) (fun cs =>
            ((clusters (runPhases key (extCoins cs) E0 j)).card : ℝ≥0∞)) * 2⁻¹ :=
            expect_mul_const _ _ _
        _ ≤ Fintype.card V * (2⁻¹ : ℝ≥0∞) ^ j * 2⁻¹ := mul_le_mul_left ih _
        _ = _ := by rw [pow_succ, mul_assoc]

/-- All reports of a trial with `K` sampled phases and a final phase. -/
def trialReports (E0 : Finset (Sym2 V)) {K : ℕ} (cs : Fin K → V → Bool) : ℕ :=
  ∑ j : Fin K, totalReports key (extCoins cs j) (runPhases key (extCoins cs) E0 j) +
    totalReports key (fun _ => false) (runPhases key (extCoins cs) E0 K)

/-- **A trial has at most `2nk` reports in expectation** when `n ≤ 2^(k−1)`. -/
theorem expect_trialReports_le (hinj : Function.Injective key) (E0 : Finset (Sym2 V)) {K : ℕ}
    (hK : Fintype.card V ≤ 2 ^ K) :
    expect (coinSeqPMF V K) (fun cs => (trialReports key E0 cs : ℝ≥0∞)) ≤
      2 * Fintype.card V * (K + 1) := by
  simp only [trialReports, Nat.cast_add, Nat.cast_sum]
  rw [expect_add, expect_sum]
  have h1 : ∑ j : Fin K, expect (coinSeqPMF V K) (fun cs =>
      (totalReports key (extCoins cs j) (runPhases key (extCoins cs) E0 j) : ℝ≥0∞)) ≤
      K * (2 * Fintype.card V) := by
    calc _ ≤ ∑ _j : Fin K, (2 * Fintype.card V : ℝ≥0∞) :=
          sum_le_sum fun j _ => expect_phase_reports key hinj E0 j
      _ = _ := by simp
  have h2 : expect (coinSeqPMF V K) (fun cs => (totalReports key (fun _ => false)
      (runPhases key (extCoins cs) E0 K) : ℝ≥0∞)) ≤ Fintype.card V := by
    calc _ ≤ expect (coinSeqPMF V K) (fun cs => (Fintype.card V : ℝ≥0∞) *
          ((clusters (runPhases key (extCoins cs) E0 K)).card : ℝ≥0∞)) :=
          expect_mono_on_support _ fun cs _ => by exact_mod_cast totalReports_le _ _
      _ = Fintype.card V * expect (coinSeqPMF V K) (fun cs =>
          ((clusters (runPhases key (extCoins cs) E0 K)).card : ℝ≥0∞)) := expect_const_mul _ _ _
      _ ≤ Fintype.card V * (Fintype.card V * (2⁻¹ : ℝ≥0∞) ^ K) :=
          mul_le_mul_right (expect_clusters_le key E0 K le_rfl) _
      _ ≤ Fintype.card V * 1 := by
          refine mul_le_mul_right ?_ _
          rw [← ENNReal.inv_pow]
          calc (Fintype.card V : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ K)⁻¹ ≤ 2 ^ K * ((2 : ℝ≥0∞) ^ K)⁻¹ :=
                mul_le_mul_left (by exact_mod_cast hK) _
            _ = 1 := ENNReal.mul_inv_cancel (by simp) (by simp)
      _ = _ := mul_one _
  have h3 : K * (2 * (Fintype.card V : ℝ≥0∞)) + Fintype.card V ≤
      2 * Fintype.card V * (K + 1) := by
    calc K * (2 * (Fintype.card V : ℝ≥0∞)) + Fintype.card V
        ≤ K * (2 * (Fintype.card V : ℝ≥0∞)) + 2 * Fintype.card V := by
          refine add_le_add le_rfl ?_
          calc (Fintype.card V : ℝ≥0∞) = 1 * Fintype.card V := (one_mul _).symm
            _ ≤ 2 * Fintype.card V := mul_le_mul_left (by norm_num) _
      _ = 2 * Fintype.card V * (K + 1) := by ring
  exact (add_le_add h1 h2).trans h3

/-- **The report cap fails with probability at most one half** (Markov). -/
theorem mass_trialReports_gt (hinj : Function.Injective key) (E0 : Finset (Sym2 V)) {K : ℕ}
    (hK : Fintype.card V ≤ 2 ^ K) :
    mass (coinSeqPMF V K) (fun cs => 4 * Fintype.card V * (K + 1) < trialReports key E0 cs) ≤
      2⁻¹ := by
  set b : ℝ≥0∞ := 2 * Fintype.card V * (K + 1)
  set a : ℝ≥0∞ := 4 * Fintype.card V * (K + 1) + 1
  have hm := mul_mass_le_expect (coinSeqPMF V K)
    (fun cs => 4 * Fintype.card V * (K + 1) < trialReports key E0 cs)
    (fun cs => (trialReports key E0 cs : ℝ≥0∞)) a (fun cs _ hcs => by
      simp only [a]; exact_mod_cast hcs)
  have hb := (hm.trans (expect_trialReports_le key hinj E0 hK))
  have ha0 : a ≠ 0 := by simp [a]
  have hatop : a ≠ ⊤ := by
    simp only [a]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (by simp))
      (by simp), by simp⟩
  have h2b : 2 * b ≤ a := by
    simp only [a, b]
    calc 2 * (2 * (Fintype.card V : ℝ≥0∞) * (K + 1)) = 4 * Fintype.card V * (K + 1) := by ring
      _ ≤ _ := le_self_add
  set m := mass (coinSeqPMF V K) (fun cs => 4 * Fintype.card V * (K + 1) < trialReports key E0 cs)
  have : a * (2 * m) ≤ a * 1 := by
    calc a * (2 * m) = 2 * (a * m) := by ring
      _ ≤ 2 * b := mul_le_mul_right hb _
      _ ≤ a := h2b
      _ = a * 1 := (mul_one a).symm
  have h2m : 2 * m ≤ 1 := (ENNReal.mul_le_mul_iff_right ha0 hatop).mp this
  rw [ENNReal.le_inv_iff_mul_le, mul_comm]
  exact h2m

end

end Spanner
end CutQueryComplexity
