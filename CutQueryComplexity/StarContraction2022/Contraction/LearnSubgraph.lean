import CutQueryComplexity.StarContraction2022.Contraction.SparseCenters.Goodness
import CutQueryComplexity.Primitive.Learn
import CutQueryComplexity.Probability.FiniteEvents

/-!
# Public fair colors and outgoing-row omission

Rows that are omitted are replaced by empty lists. Every ambient vertex remains
an available target of every retained row. Colors are genuine independent fair
draws, and their opposite-color statistics are an actual public cut program.
The hidden graph and fixed cut enter only the correctness/probability side.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph

open Finset WeightedGraph SparseCenters
open CutQueryComplexity.Probability
open scoped Classical ENNReal
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

def colors : PMF (V → Bool) :=
  Probability.uniformRows (fun _ : V => (univ : Finset Bool)) (fun _ => univ_nonempty)

theorem colors_support (c : V → Bool) : c ∈ (colors (V := V)).support := by
  simp only [colors, Probability.mem_support_uniformRows, mem_univ, implies_true]

theorem colors_apply (c : V → Bool) : colors c = ((2 : ℝ≥0∞)⁻¹) ^ Fintype.card V := by
  simp [colors, Probability.uniformRows, Probability.product_apply,
    PMF.uniformOfFinset_apply]

theorem colors_eq_centerBits : colors (V := V) = centerBits (1 / 2) (by norm_num) := by
  have hbit (b : Bool) : centerBit (1 / 2) (by norm_num) b = (2 : ℝ≥0∞)⁻¹ := by
    cases b <;> norm_num [centerBit_apply]
  ext c : 1
  rw [colors_apply]
  simp [centerBits, Probability.product_apply, hbit]

/-- Complement precisely this row when its source has color true. If the
row is loopless the source color is unchanged, so this is an involution. -/
def flipRow (N : Finset V) (v : V) (c : V → Bool) (w : V) : Bool :=
  if w ∈ N ∧ c v = true then !(c w) else c w

theorem flipRow_source (N : Finset V) (v : V) (hv : v ∉ N) (c : V → Bool) :
    flipRow N v c v = c v := by simp [flipRow, hv]

theorem flipRow_involutive (N : Finset V) (v : V) (hv : v ∉ N) :
    Function.Involutive (flipRow N v) := by
  intro c
  funext w
  by_cases hw : w ∈ N <;> by_cases hc : c v = true <;>
    simp [flipRow, hv, hw, hc]

/-- This finite involution proves the fair opposite-color row law without
postulating independence from a global successful-learning event. -/
theorem colors_flipRow (N : Finset V) (v : V) (hv : v ∉ N) :
    (colors (V := V)).map (flipRow N v) = colors := by
  have hi := flipRow_involutive N v hv
  ext c : 1
  rw [PMF.map_apply, tsum_eq_single (flipRow N v c)]
  · rw [hi c, if_pos rfl, colors_apply, colors_apply]
  · intro b hb
    apply if_neg
    intro he
    apply hb
    apply hi.injective
    simpa only [hi c] using he.symm

theorem flipRow_opposite (N : Finset V) (v : V) (c : V → Bool) :
    N.filter (fun w => c w ≠ c v) =
      N.filter (fun w => flipRow N v c w = true) := by
  ext w
  by_cases hw : w ∈ N <;> cases hv : c v <;> cases hc : c w <;>
    simp [flipRow, hw, hv, hc]

/-- For each fixed loopless row, its actual opposite-color subset has the
fair Bernoulli law. Overlapping rows need not be independent. -/
theorem colors_opposite_law (N : Finset V) (v : V) (hv : v ∉ N) :
    (colors (V := V)).map (fun c => N.filter (fun w => c w ≠ c v)) =
      Probability.bernoulliSubset N (1 / 2) (by norm_num) := by
  let select : (V → Bool) → Finset V := fun c => N.filter (fun w => c w = true)
  have he : (fun c : V → Bool => N.filter (fun w => c w ≠ c v)) =
      select ∘ flipRow N v := by
    funext c
    exact flipRow_opposite N v c
  rw [he, ← PMF.map_comp, colors_flipRow N v hv, colors_eq_centerBits]
  exact centerBits_subset_law N (1 / 2) (by norm_num)

theorem colors_opposite_mean_le (N C : Finset V) (v : V) (hv : v ∉ N) (hC : C ⊆ N) :
    expect (colors (V := V))
      (fun c => ENNReal.ofReal (Probability.crossingRatio C (N.filter (fun w => c w ≠ c v)))) ≤
      ENNReal.ofReal ((C.card : ℝ) / N.card) := by
  rw [← expect_map (colors (V := V)) (fun c => N.filter (fun w => c w ≠ c v))
    (fun T => ENNReal.ofReal (Probability.crossingRatio C T)), colors_opposite_law N v hv]
  exact Probability.bernoulliSubset_ratio_mean_le N C (1 / 2) (by norm_num) hC

theorem colors_opposite_tenth_tail (N C : Finset V) (v : V) (hv : v ∉ N) (hC : C ⊆ N) :
    mass (colors (V := V))
      (fun c => (C.card : ℝ) / N.card + 1 / 10 <
        Probability.crossingRatio C (N.filter (fun w => c w ≠ c v))) ≤
      (200 * ENNReal.ofReal ((C.card : ℝ) / N.card)) / ((N.card : ℝ≥0∞) * (1 / 2)) := by
  rw [← mass_map (colors (V := V)) (fun c => N.filter (fun w => c w ≠ c v))
    (fun T => (C.card : ℝ) / N.card + 1 / 10 < Probability.crossingRatio C T),
    colors_opposite_law N v hv]
  exact Probability.bernoulliSubset_ratio_tenth_tail N C (1 / 2) (by norm_num) (by norm_num) hC

/-- A dyadic exponential-Markov calculation gives a rational bound. This
avoids any independence claim between the different rows of one coloring. -/
theorem fairSubset_low_tail (N : Finset V) (h : ℕ) (hdegree : 4 * h ≤ N.card) :
    mass (Probability.bernoulliSubset N (1 / 2) (by norm_num))
      (fun S => S.card < h) ≤ (3 / 4 : ℝ≥0∞) ^ h := by
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hthree : ENNReal.ofReal (3 / 4 : ℝ) = (3 / 4 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
    norm_num
  have hthree_le : (3 / 4 : ℝ≥0∞) ≤ 1 := by
    rw [← hthree]
    simpa only [ENNReal.ofReal_one] using
      ENNReal.ofReal_le_ofReal (by norm_num : (3 / 4 : ℝ) ≤ 1)
  have hfactor : (1 / 2 : ℝ≥0∞) * (1 / 2) + (1 - 1 / 2) = 3 / 4 := by
    calc
      _ = ENNReal.ofReal ((1 / 2 : ℝ) * (1 / 2) + (1 - 1 / 2)) := by
        simp only [ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ (1 / 2) * (1 / 2))
          (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
          ENNReal.ofReal_sub 1 (by norm_num : (0 : ℝ) ≤ 1 / 2),
          hhalf, ENNReal.ofReal_one]
      _ = _ := by
        rw [show (1 / 2 : ℝ) * (1 / 2) + (1 - 1 / 2) = 3 / 4 by norm_num, hthree]
  have hcoefficient : (2 : ℝ≥0∞) * (3 / 4 : ℝ≥0∞) ^ 4 ≤ 3 / 4 := by
    have hr := ENNReal.ofReal_le_ofReal
      (by norm_num : (2 : ℝ) * (3 / 4 : ℝ) ^ 4 ≤ 3 / 4)
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 3 / 4) 4,
      hthree, ENNReal.ofReal_ofNat] using hr
  have hm := mul_mass_le_expect
    (Probability.bernoulliSubset N (1 / 2) (by norm_num))
    (fun S => S.card < h) (fun S => (1 / 2 : ℝ≥0∞) ^ S.card)
    ((1 / 2 : ℝ≥0∞) ^ h) (by
      intro S _ hS
      exact pow_le_pow_of_le_one (by positivity) (by norm_num) hS.le)
  rw [bernoulli_power_moment] at hm
  rw [hfactor] at hm
  have hc : (2 : ℝ≥0∞) ^ h * (1 / 2 : ℝ≥0∞) ^ h = 1 := by
    rw [← mul_pow, one_div, ENNReal.mul_inv_cancel
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by simp : (2 : ℝ≥0∞) ≠ ∞), one_pow]
  calc
    _ = ((2 : ℝ≥0∞) ^ h * (1 / 2 : ℝ≥0∞) ^ h) *
        mass (Probability.bernoulliSubset N (1 / 2) (by norm_num))
          (fun S => S.card < h) := by rw [hc, one_mul]
    _ ≤ (2 : ℝ≥0∞) ^ h * (3 / 4 : ℝ≥0∞) ^ N.card := by
      rw [mul_assoc]
      exact mul_le_mul le_rfl hm (by positivity) (by positivity)
    _ ≤ (2 : ℝ≥0∞) ^ h * (3 / 4 : ℝ≥0∞) ^ (4 * h) :=
      mul_le_mul le_rfl
        (pow_le_pow_of_le_one (by positivity) hthree_le hdegree)
        (by positivity) (by positivity)
    _ = ((2 : ℝ≥0∞) * (3 / 4 : ℝ≥0∞) ^ 4) ^ h := by
      rw [pow_mul, mul_pow]
    _ ≤ (3 / 4 : ℝ≥0∞) ^ h := by
      exact pow_le_pow_left' hcoefficient h

theorem colors_opposite_low_tail (N : Finset V) (v : V) (hv : v ∉ N)
    (h : ℕ) (hdegree : 4 * h ≤ N.card) :
    mass (colors (V := V))
      (fun c => (N.filter (fun w => c w ≠ c v)).card < h) ≤
      (3 / 4 : ℝ≥0∞) ^ h := by
  rw [← mass_map (colors (V := V)) (fun c => N.filter (fun w => c w ≠ c v))
    (fun T => T.card < h), colors_opposite_law N v hv]
  exact fairSubset_low_tail N h hdegree

/-- A completely rational numerical bound, valid at the source threshold. -/
theorem mul_geometric_le_hundredth (h : ℕ) (hh : 35 ≤ h) :
    (h : ℝ) * (3 / 4 : ℝ) ^ h ≤ 1 / 100 := by
  induction h, hh using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      have hkR : (35 : ℝ) ≤ k := by exact_mod_cast hk
      calc
        ((k + 1 : ℕ) : ℝ) * (3 / 4 : ℝ) ^ (k + 1) =
            (((k : ℝ) + 1) * (3 / 4)) * (3 / 4 : ℝ) ^ k := by
          rw [Nat.cast_add, Nat.cast_one, pow_succ]
          ring
        _ ≤ (k : ℝ) * (3 / 4 : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ ≤ 1 / 100 := ih

def oppositeSet (c : V → Bool) (v : V) : Finset V := univ.filter fun w => c w ≠ c v

@[simp] theorem mem_oppositeSet (c : V → Bool) (v w : V) :
    w ∈ oppositeSet c v ↔ c w ≠ c v := by simp [oppositeSet]

@[simp] theorem self_not_mem_oppositeSet (c : V → Bool) (v : V) :
    v ∉ oppositeSet c v := by simp

/-- This operation removes outgoing rows only. The target type remains V. -/
def omitRows (keep : Finset V) (N : V → Finset V) (v : V) : Finset V :=
  if v ∈ keep then N v else ∅

@[simp] theorem omitRows_kept (keep : Finset V) (N : V → Finset V) {v : V}
    (hv : v ∈ keep) : omitRows keep N v = N v := by simp [omitRows, hv]

@[simp] theorem omitRows_removed (keep : Finset V) (N : V → Finset V) {v : V}
    (hv : v ∉ keep) : omitRows keep N v = ∅ := by simp [omitRows, hv]

/-- In particular, a removed vertex may still be sampled by any retained row. -/
theorem target_survives_omission (keep : Finset V) (N : V → Finset V) {v w : V}
    (hv : v ∈ keep) (hw : w ∈ N v) : w ∈ omitRows keep N v := by
  simpa only [omitRows_kept keep N hv] using hw

def oppositeRows (N : V → Finset V) (c : V → Bool) (v : V) : Finset V :=
  N v ∩ oppositeSet c v

def crossingSet (S : Finset V) (v : V) : Finset V := if v ∈ S then Sᶜ else S

def rowFraction (N : V → Finset V) (S : Finset V) (v : V) : ℝ :=
  Probability.crossingRatio (crossingSet S v) (N v)

theorem rowFraction_nonneg (N : V → Finset V) (S : Finset V) (v : V) :
    0 ≤ rowFraction N S v := Probability.crossingRatio_nonneg _ _

theorem rowFraction_omit (keep : Finset V) (N : V → Finset V) (S : Finset V) (v : V) :
    rowFraction (omitRows keep N) S v = if v ∈ keep then rowFraction N S v else 0 := by
  by_cases hv : v ∈ keep <;> simp [rowFraction, omitRows, hv]

/-- Goodness is a proof-only property of an explicit row table and fixed cut. -/
def GoodRows (alpha beta : ℝ) (N : V → Finset V) (S : Finset V) : Prop :=
  (∀ v, rowFraction N S v ≤ alpha) ∧ (∑ v, rowFraction N S v) ≤ beta

theorem GoodRows.omit {alpha beta : ℝ} {N : V → Finset V} {S : Finset V}
    (h : GoodRows alpha beta N S) (ha : 0 ≤ alpha) (keep : Finset V) :
    GoodRows alpha beta (omitRows keep N) S := by
  constructor
  · intro v
    rw [rowFraction_omit]
    split_ifs
    · exact h.1 v
    · exact ha
  · apply le_trans _ h.2
    apply Finset.sum_le_sum
    intro v _
    rw [rowFraction_omit]
    split_ifs
    · exact le_rfl
    · exact rowFraction_nonneg N S v

/-- Three original cut families measure every opposite-color degree. There
is no hidden row table or fixed cut among the public program arguments. -/
def oppositeStatistics (c : V → Bool) :
    DTree (Finset V) ℝ (V → ℝ) (3 * Fintype.card V) :=
  ((DTree.queryAll (fun v : V => ({v} : Finset V)) (fun _ => (0 : ℝ))).bind fun a =>
    (DTree.queryAll (oppositeSet c) (fun _ => (0 : ℝ))).bind fun b =>
      (DTree.queryAll (fun v => ({v} : Finset V) ∪ oppositeSet c v) (fun _ => (0 : ℝ))).map
        (fun d v => (a v + b v - d v) / 2)).cast (by omega)

theorem oppositeStatistics_eval (G : WeightedGraph V) (c : V → Bool) :
    (oppositeStatistics c).eval G.cut = fun v => ∑ w ∈ oppositeSet c v, G.w v w := by
  simp only [oppositeStatistics, DTree.eval, DTree.run_cast, DTree.run_bind,
    DTree.run_map, DTree.queryAll_run]
  funext v
  have he := G.cross_eq_three_cuts
    (disjoint_singleton_left.mpr (self_not_mem_oppositeSet c v))
  simpa only [WeightedGraph.cross, sum_singleton] using he.symm

theorem oppositeStatistics_cost (c : V → Bool) (answer : Finset V → ℝ) :
    (oppositeStatistics c).cost answer ≤ 3 * Fintype.card V := DTree.cost_le _ _

/-- The public extra-omission guard uses measured degrees and measured
opposite-color answers. Arbitrary answers never change the query budget. -/
def retainedRows (h : ℕ) (degree : V → ℕ) (opposite : V → ℝ) : Finset V :=
  univ.filter fun v => 4 * h ≤ degree v ∧ (h : ℝ) ≤ opposite v

/-- The explicit intermediate row table after the public degree guards.
The unretained sources are removed only as rows, never as possible columns. -/
def coloredRows (h : ℕ) (N : V → Finset V) (c : V → Bool) : V → Finset V :=
  omitRows (retainedRows h (fun v => (N v).card)
    (fun v => ((oppositeRows N c v).card : ℝ))) (oppositeRows N c)

theorem crossingRatio_inter_of_subset (C N T : Finset V) (hT : T ⊆ N) :
    Probability.crossingRatio (C ∩ N) T = Probability.crossingRatio C T := by
  unfold Probability.crossingRatio
  apply congrArg (fun k : ℕ => (k : ℝ) / T.card)
  apply congrArg Finset.card
  ext v
  simp only [mem_inter]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hT h.2⟩, h.2⟩⟩

theorem oppositeRows_filter (N : V → Finset V) (c : V → Bool) (v : V) :
    oppositeRows N c v = (N v).filter (fun w => c w ≠ c v) := by
  ext w
  simp [oppositeRows, oppositeSet]

theorem rowFraction_opposite (N : V → Finset V) (S : Finset V)
    (c : V → Bool) (v : V) :
    rowFraction (oppositeRows N c) S v =
      Probability.crossingRatio (crossingSet S v ∩ N v)
        ((N v).filter (fun w => c w ≠ c v)) := by
  rw [rowFraction, oppositeRows_filter,
    crossingRatio_inter_of_subset _ _ _ (filter_subset _ _)]

theorem rowFraction_colored_le (h : ℕ) (N : V → Finset V) (S : Finset V)
    (c : V → Bool) (v : V) :
    rowFraction (coloredRows h N c) S v ≤ rowFraction (oppositeRows N c) S v := by
  rw [coloredRows, rowFraction_omit]
  split_ifs
  · exact le_rfl
  · exact rowFraction_nonneg _ _ _

theorem colored_mean_le (h : ℕ) (N : V → Finset V) (S : Finset V)
    (hloop : ∀ v, v ∉ N v) (v : V) :
    expect (colors (V := V))
      (fun c => ENNReal.ofReal (rowFraction (coloredRows h N c) S v)) ≤
      ENNReal.ofReal (rowFraction N S v) := by
  calc
    _ ≤ expect (colors (V := V))
        (fun c => ENNReal.ofReal (rowFraction (oppositeRows N c) S v)) :=
      expect_mono_on_support _ (fun c _ =>
        ENNReal.ofReal_le_ofReal (rowFraction_colored_le h N S c v))
    _ = expect (colors (V := V)) (fun c => ENNReal.ofReal
        (Probability.crossingRatio (crossingSet S v ∩ N v)
          ((N v).filter (fun w => c w ≠ c v)))) := by
      apply expect_congr_on_support
      intro c _
      rw [rowFraction_opposite]
    _ ≤ ENNReal.ofReal (((crossingSet S v ∩ N v).card : ℝ) / (N v).card) :=
      colors_opposite_mean_le (N v) (crossingSet S v ∩ N v) v (hloop v)
        inter_subset_right
    _ = ENNReal.ofReal (rowFraction N S v) := by
      apply congrArg ENNReal.ofReal
      unfold rowFraction Probability.crossingRatio
      apply congrArg (fun k : ℕ => (k : ℝ) / (N v).card)
      apply congrArg Finset.card
      ext w
      simp only [mem_inter]

/-- Each retained row inherits the actual unconditional fair-color tail;
no successful-omission or query-cap event is conditioned on. -/
theorem colored_row_tail (h : ℕ) (N : V → Finset V) (S : Finset V)
    (hloop : ∀ v, v ∉ N v) {alpha : ℝ} (ha : 0 ≤ alpha)
    (hmax : ∀ v, rowFraction N S v ≤ alpha) (v : V) :
    mass (colors (V := V))
      (fun c => alpha + 1 / 10 < rowFraction (coloredRows h N c) S v) ≤
      200 * ENNReal.ofReal (rowFraction N S v) / (h : ℝ≥0∞) := by
  have hratio : (((crossingSet S v ∩ N v).card : ℝ) / (N v).card) =
      rowFraction N S v := by
    unfold rowFraction Probability.crossingRatio
    apply congrArg (fun k : ℕ => (k : ℝ) / (N v).card)
    apply congrArg Finset.card
    ext w
    simp only [mem_inter]
  by_cases hd : 4 * h ≤ (N v).card
  · have htwo : (2 : ℝ≥0∞) * (1 / 2) = 1 := by
      rw [one_div, ENNReal.mul_inv_cancel
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by simp : (2 : ℝ≥0∞) ≠ ∞)]
    have hden : (h : ℝ≥0∞) ≤ ((N v).card : ℝ≥0∞) * (1 / 2) := by
      calc
        (h : ℝ≥0∞) = ((2 : ℝ≥0∞) * (1 / 2)) * h := by rw [htwo, one_mul]
        _ = ((2 : ℝ≥0∞) * h) * (1 / 2) := by ring
        _ ≤ ((N v).card : ℝ≥0∞) * (1 / 2) := by
          apply mul_le_mul _ le_rfl (by positivity) (by positivity)
          exact_mod_cast (show 2 * h ≤ (N v).card by omega)
    calc
      _ ≤ mass (colors (V := V)) (fun c => rowFraction N S v + 1 / 10 <
          Probability.crossingRatio (crossingSet S v ∩ N v)
            ((N v).filter (fun w => c w ≠ c v))) := by
        apply mass_mono
        intro c hc
        have hm := rowFraction_colored_le h N S c v
        rw [rowFraction_opposite] at hm
        linarith [hmax v]
      _ ≤ (200 * ENNReal.ofReal (rowFraction N S v)) /
          (((N v).card : ℝ≥0∞) * (1 / 2)) := by
        simpa only [hratio] using
          colors_opposite_tenth_tail (N v) (crossingSet S v ∩ N v) v (hloop v)
            inter_subset_right
      _ ≤ _ := ENNReal.div_le_div le_rfl hden
  · have hz (c : V → Bool) : rowFraction (coloredRows h N c) S v = 0 := by
      have hnot : v ∉ retainedRows h (fun v => (N v).card)
          (fun v => ((oppositeRows N c v).card : ℝ)) := by
        simp [retainedRows, hd]
      simp only [coloredRows, rowFraction_omit, hnot, ite_false]
    have hfalse : (fun c => alpha + 1 / 10 < rowFraction (coloredRows h N c) S v) =
        fun _ => False := by
      funext c
      rw [hz]
      exact propext ⟨fun hc => by linarith, False.elim⟩
    rw [hfalse, mass_false]
    positivity

theorem colored_sum_mean_le (h : ℕ) (N : V → Finset V) (S : Finset V)
    (hloop : ∀ v, v ∉ N v) {beta : ℝ} (hsum : (∑ v, rowFraction N S v) ≤ beta) :
    expect (colors (V := V))
      (fun c => ENNReal.ofReal (∑ v, rowFraction (coloredRows h N c) S v)) ≤
      ENNReal.ofReal beta := by
  have he (c : V → Bool) : ENNReal.ofReal (∑ v, rowFraction (coloredRows h N c) S v) =
      ∑ v, ENNReal.ofReal (rowFraction (coloredRows h N c) S v) :=
    ENNReal.ofReal_sum_of_nonneg (fun v _ => rowFraction_nonneg _ _ v)
  calc
    _ = expect (colors (V := V))
        (fun c => ∑ v, ENNReal.ofReal (rowFraction (coloredRows h N c) S v)) :=
      expect_congr_on_support _ (fun c _ => he c)
    _ = ∑ v, expect (colors (V := V))
        (fun c => ENNReal.ofReal (rowFraction (coloredRows h N c) S v)) := expect_sum _ _ _
    _ ≤ ∑ v, ENNReal.ofReal (rowFraction N S v) :=
      Finset.sum_le_sum (fun v _ => colored_mean_le h N S hloop v)
    _ = ENNReal.ofReal (∑ v, rowFraction N S v) :=
      (ENNReal.ofReal_sum_of_nonneg (fun v _ => rowFraction_nonneg N S v)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hsum

theorem colored_sum_tail (h : ℕ) (N : V → Finset V) (S : Finset V)
    (hloop : ∀ v, v ∉ N v) {beta : ℝ} (hb : 0 < beta)
    (hsum : (∑ v, rowFraction N S v) ≤ beta) :
    mass (colors (V := V)) (fun c => 10 * beta <
      ∑ v, rowFraction (coloredRows h N c) S v) ≤ (1 / 10 : ℝ≥0∞) := by
  have hmark := mul_mass_le_expect (colors (V := V))
    (fun c => 10 * beta < ∑ v, rowFraction (coloredRows h N c) S v)
    (fun c => ENNReal.ofReal (∑ v, rowFraction (coloredRows h N c) S v))
    (ENNReal.ofReal (10 * beta)) (fun c _ hc => ENNReal.ofReal_le_ofReal hc.le)
  calc
    _ ≤ expect (colors (V := V))
        (fun c => ENNReal.ofReal (∑ v, rowFraction (coloredRows h N c) S v)) /
          ENNReal.ofReal (10 * beta) := by
      apply (ENNReal.le_div_iff_mul_le (Or.inl (by positivity))
        (Or.inl ENNReal.ofReal_ne_top)).mpr
      simpa only [mul_comm] using hmark
    _ ≤ ENNReal.ofReal beta / ENNReal.ofReal (10 * beta) :=
      ENNReal.div_le_div (colored_sum_mean_le h N S hloop hsum) le_rfl
    _ = _ := by
      rw [← ENNReal.ofReal_div_of_pos (by positivity : 0 < 10 * beta)]
      have he : beta / (10 * beta) = 1 / 10 := by field_simp [hb.ne']
      rw [he, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 10)]
      norm_num

/-- The intermediate fair-color graph is good with the claimed marginal
bound. All rows use one shared color tape; only expectations and a union bound
are combined. Neither an omission success nor a recovery clock is a premise. -/
theorem coloredRows_good_failure (h : ℕ) (N : V → Finset V) (S : Finset V)
    (hloop : ∀ v, v ∉ N v) {alpha beta : ℝ} (ha : 0 ≤ alpha) (hb : 0 < beta)
    (hgood : GoodRows alpha beta N S) :
    mass (colors (V := V))
      (fun c => ¬ GoodRows (alpha + 1 / 10) (10 * beta) (coloredRows h N c) S) ≤
      1 / 10 + 200 * ENNReal.ofReal beta / (h : ℝ≥0∞) := by
  have hmax : mass (colors (V := V))
      (fun c => ∃ v, alpha + 1 / 10 < rowFraction (coloredRows h N c) S v) ≤
        200 * ENNReal.ofReal beta / (h : ℝ≥0∞) := by
    have he : (fun c => ∃ v, alpha + 1 / 10 < rowFraction (coloredRows h N c) S v) =
        (fun c => ∃ v ∈ (univ : Finset V),
          alpha + 1 / 10 < rowFraction (coloredRows h N c) S v) := by
      funext c
      simp only [mem_univ, true_and]
    rw [he]
    calc
      _ ≤ ∑ v : V, mass (colors (V := V))
          (fun c => alpha + 1 / 10 < rowFraction (coloredRows h N c) S v) :=
        mass_exists_finset_le _ _ _
      _ ≤ ∑ v : V, 200 * ENNReal.ofReal (rowFraction N S v) / (h : ℝ≥0∞) :=
        Finset.sum_le_sum (fun v _ => colored_row_tail h N S hloop ha hgood.1 v)
      _ = 200 * (∑ v, ENNReal.ofReal (rowFraction N S v)) / (h : ℝ≥0∞) := by
        simp only [div_eq_mul_inv]
        rw [← Finset.sum_mul,← Finset.mul_sum]
      _ ≤ 200 * ENNReal.ofReal beta / (h : ℝ≥0∞) := by
        apply ENNReal.div_le_div _ le_rfl
        apply mul_le_mul le_rfl _ (by positivity) (by positivity)
        rw [← ENNReal.ofReal_sum_of_nonneg (fun v _ => rowFraction_nonneg N S v)]
        exact ENNReal.ofReal_le_ofReal hgood.2
  calc
    _ ≤ mass (colors (V := V)) (fun c =>
        10 * beta < (∑ v, rowFraction (coloredRows h N c) S v) ∨
          ∃ v, alpha + 1 / 10 < rowFraction (coloredRows h N c) S v) := by
      apply mass_mono
      intro c hc
      by_contra hbad
      apply hc
      constructor
      · intro v
        by_contra hv
        exact hbad (Or.inr ⟨v, lt_of_not_ge hv⟩)
      · by_contra hs
        exact hbad (Or.inl (lt_of_not_ge hs))
    _ ≤ mass (colors (V := V))
        (fun c => 10 * beta < ∑ v, rowFraction (coloredRows h N c) S v) +
      mass (colors (V := V))
        (fun c => ∃ v, alpha + 1 / 10 < rowFraction (coloredRows h N c) S v) :=
      mass_or_le _ _ _
    _ ≤ _ := add_le_add (colored_sum_tail h N S hloop hb hgood.2) hmax

/-- Extra omissions depend on the public fair color tape and the explicit
row table; low-degree rows are accounted for separately. -/
def extraOmissions (N : V → Finset V) (h : ℕ) (c : V → Bool) : Finset V :=
  univ.filter fun v => 4 * h ≤ (N v).card ∧
    ((N v).filter (fun w => c w ≠ c v)).card < h

theorem expect_extraOmissions_le (N : V → Finset V) (h : ℕ)
    (hloop : ∀ v, v ∉ N v) :
    expect (colors (V := V)) (fun c => ((extraOmissions N h c).card : ℝ≥0∞)) ≤
      (Fintype.card V : ℝ≥0∞) * ENNReal.ofReal ((3 / 4 : ℝ) ^ h) := by
  have he (c : V → Bool) : ((extraOmissions N h c).card : ℝ≥0∞) =
      ∑ v : V, if v ∈ extraOmissions N h c then (1 : ℝ≥0∞) else 0 := by simp
  have hp (v : V) : mass (colors (V := V))
      (fun c => v ∈ extraOmissions N h c) ≤ (3 / 4 : ℝ≥0∞) ^ h := by
    by_cases hd : 4 * h ≤ (N v).card
    · apply (mass_mono (colors (V := V))
        (Q := fun c => ((N v).filter (fun w => c w ≠ c v)).card < h) ?_).trans
      · exact colors_opposite_low_tail (N v) v (hloop v) h hd
      · intro c hc
        exact (mem_filter.mp hc).2.2
    · have hnone : (fun c => v ∈ extraOmissions N h c) = fun _ => False := by
        funext c
        exact propext (by simp [extraOmissions, hd])
      rw [hnone, mass_false]
      positivity
  calc
    _ = expect (colors (V := V)) (fun c =>
        ∑ v : V, if v ∈ extraOmissions N h c then (1 : ℝ≥0∞) else 0) :=
      expect_congr_on_support _ (fun c _ => he c)
    _ = ∑ v : V, mass (colors (V := V)) (fun c => v ∈ extraOmissions N h c) := by
      calc
        _ = ∑ v : V, expect (colors (V := V))
            (fun c => if v ∈ extraOmissions N h c then (1 : ℝ≥0∞) else 0) := expect_sum _ _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro v _
          calc
            _ = expect (colors (V := V))
                (fun c => @ite ℝ≥0∞ (v ∈ extraOmissions N h c) (Classical.propDecidable _) 1 0) := by
              apply expect_congr_on_support
              intro c _
              by_cases hv : v ∈ extraOmissions N h c <;> simp only [hv, ite_true, ite_false]
            _ = _ := by
              simpa only [one_mul] using CutQueryComplexity.Probability.expect_indicator
                (colors (V := V)) (fun c => v ∈ extraOmissions N h c) 1
    _ ≤ ∑ _v : V, (3 / 4 : ℝ≥0∞) ^ h := Finset.sum_le_sum (fun v _ => hp v)
    _ = _ := by
      simp only [sum_const, card_univ, nsmul_eq_mul,
        ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 3 / 4) h,
        ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4), ENNReal.ofReal_ofNat]

/-- Markov is applied to the sum of the shared-color omission indicators.
No independence between those indicators, or from recovery success, is used. -/
theorem extraOmissions_failure_le (N : V → Finset V) (h : ℕ)
    (hh : 35 ≤ h) (hloop : ∀ v, v ∉ N v) :
    mass (colors (V := V)) (fun c => (Fintype.card V : ℝ) / h <
      (extraOmissions N h c).card) ≤ (1 / 100 : ℝ≥0∞) := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  by_cases hn : 0 < Fintype.card V
  · have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
    let a := ENNReal.ofReal ((Fintype.card V : ℝ) / h)
    have ha0 : a ≠ 0 := by dsimp [a]; positivity
    have hat : a ≠ ∞ := ENNReal.ofReal_ne_top
    have hm := mul_mass_le_expect (colors (V := V))
      (fun c => (Fintype.card V : ℝ) / h < (extraOmissions N h c).card)
      (fun c => ((extraOmissions N h c).card : ℝ≥0∞)) a (by
        intro c _ hc
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal hc.le)
    calc
      _ ≤ expect (colors (V := V))
          (fun c => ((extraOmissions N h c).card : ℝ≥0∞)) / a := by
        apply (ENNReal.le_div_iff_mul_le (Or.inl ha0) (Or.inl hat)).mpr
        simpa only [mul_comm] using hm
      _ ≤ ((Fintype.card V : ℝ≥0∞) * ENNReal.ofReal ((3 / 4 : ℝ) ^ h)) / a :=
        ENNReal.div_le_div (expect_extraOmissions_le N h hloop) le_rfl
      _ = ENNReal.ofReal ((h : ℝ) * (3 / 4 : ℝ) ^ h) := by
        rw [show (Fintype.card V : ℝ≥0∞) = ENNReal.ofReal (Fintype.card V : ℝ) by simp,
          ← ENNReal.ofReal_mul hnR.le]
        change ENNReal.ofReal ((Fintype.card V : ℝ) * (3 / 4 : ℝ) ^ h) /
          ENNReal.ofReal ((Fintype.card V : ℝ) / h) = _
        rw [← ENNReal.ofReal_div_of_pos (div_pos hnR hhR)]
        congr 1
        field_simp [hnR.ne', hhR.ne']
      _ ≤ ENNReal.ofReal (1 / 100 : ℝ) :=
        ENNReal.ofReal_le_ofReal (mul_geometric_le_hundredth h hh)
      _ = _ := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 100)]
        norm_num
  · have hn0 : Fintype.card V = 0 := by omega
    have hnone : (fun c : V → Bool => (Fintype.card V : ℝ) / h <
        (extraOmissions N h c).card) = fun _ => False := by
      funext c
      have hc : (extraOmissions N h c).card = 0 := by
        have := card_le_univ (extraOmissions N h c)
        omega
      simp only [hn0, hc, Nat.cast_zero, zero_div, lt_self_iff_false]
    rw [hnone, mass_false]
    positivity

def lowSources (N : V → Finset V) (h : ℕ) : Finset V :=
  univ.filter fun v => (N v).card < 4 * h

def zeroSources (N : V → Finset V) : Finset V := univ.filter fun v => N v = ∅

theorem coloredRows_nonzero_degree (h : ℕ) (N : V → Finset V) (c : V → Bool)
    (v : V) (hv : coloredRows h N c v ≠ ∅) : h ≤ (coloredRows h N c v).card := by
  let keep := retainedRows h (fun v => (N v).card)
    (fun v => ((oppositeRows N c v).card : ℝ))
  have hkeep : v ∈ keep := by
    by_contra hk
    apply hv
    change omitRows keep (oppositeRows N c) v = ∅
    exact omitRows_removed keep _ hk
  have hdegree : (h : ℝ) ≤ (oppositeRows N c v).card := (mem_filter.mp hkeep).2.2
  change h ≤ (omitRows keep (oppositeRows N c) v).card
  rw [omitRows_kept keep _ hkeep]
  exact_mod_cast hdegree

/-- Every omitted source is either an original low row or an actual extra
color omission. These are row sets only; their vertices remain target labels. -/
theorem coloredRows_zero_subset (h : ℕ) (hh : 0 < h)
    (N : V → Finset V) (c : V → Bool) :
    zeroSources (coloredRows h N c) ⊆ lowSources N h ∪ extraOmissions N h c := by
  intro v hv
  have hz : coloredRows h N c v = ∅ := (mem_filter.mp hv).2
  by_cases hd : 4 * h ≤ (N v).card
  · have ho : (oppositeRows N c v).card < h := by
      by_contra hnot
      have hcard : h ≤ (oppositeRows N c v).card := Nat.le_of_not_gt hnot
      have hkeep : v ∈ retainedRows h (fun v => (N v).card)
          (fun v => ((oppositeRows N c v).card : ℝ)) := by
        apply mem_filter.mpr
        refine ⟨mem_univ _, hd, ?_⟩
        change (h : ℝ) ≤ ((oppositeRows N c v).card : ℝ)
        exact_mod_cast hcard
      have hEq : coloredRows h N c v = oppositeRows N c v :=
        omitRows_kept _ _ hkeep
      rw [hEq] at hz
      have hc0 : (oppositeRows N c v).card = 0 := by rw [hz]; simp
      omega
    apply mem_union_right
    apply mem_filter.mpr
    exact ⟨mem_univ _, hd, by simpa only [oppositeRows_filter] using ho⟩
  · apply mem_union_left
    exact mem_filter.mpr ⟨mem_univ _, Nat.lt_of_not_ge hd⟩

theorem coloredRows_zero_card_le (h : ℕ) (hh : 0 < h)
    (N : V → Finset V) (c : V → Bool) :
    (zeroSources (coloredRows h N c)).card ≤ (lowSources N h).card + (extraOmissions N h c).card :=
  (card_le_card (coloredRows_zero_subset h hh N c)).trans (card_union_le _ _)

theorem coloredRows_zero_real_le (h : ℕ) (hh : 0 < h)
    (N : V → Finset V) (c : V → Bool) (tau : ℕ)
    (hlow : (lowSources N h).card ≤ tau)
    (hextra : ((extraOmissions N h c).card : ℝ) ≤ (Fintype.card V : ℝ) / h) :
    ((zeroSources (coloredRows h N c)).card : ℝ) ≤ tau + (Fintype.card V : ℝ) / h := by
  have hz : ((zeroSources (coloredRows h N c)).card : ℝ) ≤
      (lowSources N h).card + (extraOmissions N h c).card := by
    exact_mod_cast coloredRows_zero_card_le h hh N c
  have hl : ((lowSources N h).card : ℝ) ≤ tau := by exact_mod_cast hlow
  linarith

/-- The entire color stage has the literal debit 11/100+200*beta/h:
its good-row estimate and its extra-omission clock are combined by a union
bound, not by conditioning one event on the other. -/
theorem colored_stage_failure (h : ℕ) (hh : 35 ≤ h)
    (N : V → Finset V) (S : Finset V) (tau : ℕ)
    (hlow : (lowSources N h).card ≤ tau) (hloop : ∀ v, v ∉ N v)
    {alpha beta : ℝ} (ha : 0 ≤ alpha) (hb : 0 < beta) (hgood : GoodRows alpha beta N S) :
    mass (colors (V := V)) (fun c => ¬ (
      GoodRows (alpha + 1 / 10) (10 * beta) (coloredRows h N c) S ∧
      ((zeroSources (coloredRows h N c)).card : ℝ) ≤ tau + (Fintype.card V : ℝ) / h)) ≤
      11 / 100 + 200 * ENNReal.ofReal beta / (h : ℝ≥0∞) := by
  calc
    _ ≤ mass (colors (V := V)) (fun c =>
        ¬ GoodRows (alpha + 1 / 10) (10 * beta) (coloredRows h N c) S ∨
        (Fintype.card V : ℝ) / h < (extraOmissions N h c).card) := by
      apply mass_mono
      intro c hbad
      by_contra hn
      have hg : GoodRows (alpha + 1 / 10) (10 * beta) (coloredRows h N c) S := by
        by_contra hg
        exact hn (Or.inl hg)
      have he : ((extraOmissions N h c).card : ℝ) ≤ (Fintype.card V : ℝ) / h := by
        by_contra he
        exact hn (Or.inr (lt_of_not_ge he))
      exact hbad ⟨hg, coloredRows_zero_real_le h (by omega) N c tau hlow he⟩
    _ ≤ mass (colors (V := V))
        (fun c => ¬ GoodRows (alpha + 1 / 10) (10 * beta) (coloredRows h N c) S) +
      mass (colors (V := V)) (fun c => (Fintype.card V : ℝ) / h < (extraOmissions N h c).card) :=
      mass_or_le _ _ _
    _ ≤ (1 / 10 + 200 * ENNReal.ofReal beta / (h : ℝ≥0∞)) + 1 / 100 :=
      add_le_add (coloredRows_good_failure h N S hloop ha hb hgood)
        (extraOmissions_failure_le N h hh hloop)
    _ = _ := by
      have he : (1 / 10 : ℝ≥0∞) + 1 / 100 = 11 / 100 := by
        calc
          _ = ENNReal.ofReal ((1 / 10 : ℝ) + 1 / 100) := by
            rw [ENNReal.ofReal_add (by norm_num) (by norm_num),
              ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 10),
              ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 100)]
            norm_num
          _ = _ := by
            rw [show (1 / 10 : ℝ) + 1 / 100 = 11 / 100 by norm_num,
              ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 100)]
            norm_num
      rw [add_right_comm, he]

/-- The analysis-only crossing row is exactly the original row restricted
to the opposite shore of the fixed cut. -/
theorem inputCrossRows_eq (G : SimpleInput V) (S : Finset V) (v : V) :
    SparseCenters.inputCrossRows G S v = crossingSet S v ∩ SparseCenters.inputRows G v := by
  ext w
  by_cases hv : v ∈ S <;>
    simp [SparseCenters.inputCrossRows, SparseCenters.inputRows, AllPairs.rowSupport,
      crossingSet, hv, and_left_comm, and_assoc]

theorem center_rowFraction_eq (G : SimpleInput V) (S R : Finset V) (v : V) :
    rowFraction (fun u => SparseCenters.inputRows G u ∩ R) S v =
      Probability.crossingRatio (SparseCenters.inputCrossRows G S v)
        (SparseCenters.inputRows G v ∩ R) := by
  rw [rowFraction, inputCrossRows_eq]
  exact (crossingRatio_inter_of_subset _ _ _ inter_subset_left).symm

/-- Both later center branches inherit one shared good-center event. Row
omissions preserve its bounds without paying for that event a second time. -/
theorem center_goodRows (G : SimpleInput V) (S R : Finset V) (d : ℕ)
    (hgood : SparseCenters.GoodCenters (SparseCenters.inputRows G)
      (SparseCenters.inputCrossRows G S) d R) :
    GoodRows (3 / 5) 8 (fun u => SparseCenters.inputRows G u ∩ R) S := by
  constructor
  · intro v
    rw [center_rowFraction_eq]
    exact hgood.2.2.1 v
  · simp_rw [center_rowFraction_eq]
    exact hgood.2.2.2

/-- The actual low-degree omission set lies in the already measured bad
set. This is the inside branch's deficiency premise, not a new random event. -/
theorem center_lowSources_subset_bad (G : SimpleInput V) (R : Finset V) (d : ℕ)
    (hd : Schedule.degreeCutoff ≤ d) :
    lowSources (fun u => SparseCenters.inputRows G u ∩ R) (Schedule.height d) ⊆
      SparseCenters.badRows (SparseCenters.inputRows G) d R := by
  intro v hv
  have hlow : (SparseCenters.inputRows G v ∩ R).card < 4 * Schedule.height d :=
    (mem_filter.mp hv).2
  have hlowR : ((SparseCenters.inputRows G v ∩ R).card : ℝ) < 4 * Schedule.height d := by
    exact_mod_cast hlow
  have hthreshold := Schedule.inside_omission_threshold d hd
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_⟩
  have hh0 : (0 : ℝ) ≤ Schedule.height d := Nat.cast_nonneg _
  nlinarith

theorem center_lowSources_inside_card_le (G : SimpleInput V) (R : Finset V) (d : ℕ)
    (hd : Schedule.degreeCutoff ≤ d) :
    (lowSources (fun u => SparseCenters.inputRows G u ∩ R) (Schedule.height d) ∩ R).card ≤
      (SparseCenters.badRows (SparseCenters.inputRows G) d R ∩ R).card := by
  apply card_le_card
  intro v hv
  exact mem_inter.mpr ⟨center_lowSources_subset_bad G R d hd (mem_inter.mp hv).1,
    (mem_inter.mp hv).2⟩

/-- Restrict the actual vertex type, so later component counts and budgets
use the number of centers rather than the original ambient vertex count. -/
def onRows (U : Finset V) (N : V → Finset V) (u : U) : Finset U :=
  (N u.val).subtype (· ∈ U)

theorem onRows_card (U : Finset V) (N : V → Finset V) (u : U) :
    (onRows U N u).card = (N u.val ∩ U).card := by
  rw [onRows, card_subtype, filter_mem_eq_inter]

theorem onRows_loopless (U : Finset V) (N : V → Finset V)
    (hloop : ∀ v, v ∉ N v) (u : U) : u ∉ onRows U N u := by
  intro hu
  exact hloop u.val (mem_subtype.mp hu)

theorem onRows_rowFraction (U : Finset V) (N : V → Finset V) (S : Finset V) (u : U) :
    rowFraction (onRows U N) (S.subtype (· ∈ U)) u =
      rowFraction (fun v => N v ∩ U) S u.val := by
  unfold rowFraction Probability.crossingRatio
  apply congrArg₂ (fun a b : ℕ => (a : ℝ) / (b : ℝ))
  · apply Finset.card_bij (fun w _ => w.val)
    · intro w hw
      simp only [mem_inter] at hw ⊢
      have hs : w.val ∈ crossingSet S u.val := by
        by_cases hu : u.val ∈ S <;> simpa [crossingSet, hu] using hw.1
      have hn : w.val ∈ N u.val := by
        simpa only [onRows, mem_subtype] using hw.2
      exact ⟨hs, hn, w.property⟩
    · intro w _ z _ he
      exact Subtype.ext he
    · intro w hw
      have hm : w ∈ crossingSet S u.val ∧ w ∈ N u.val ∧ w ∈ U := by
        simpa only [mem_inter] using hw
      refine ⟨⟨w, hm.2.2⟩, ?_, rfl⟩
      simp only [mem_inter]
      constructor
      · by_cases hu : u.val ∈ S <;> simpa [crossingSet, hu] using hm.1
      · simpa only [onRows, mem_subtype] using hm.2.1
  · exact onRows_card U N u

theorem onRows_good {alpha beta : ℝ} (U : Finset V) (N : V → Finset V) (S : Finset V)
    (hgood : GoodRows alpha beta (fun v => N v ∩ U) S) :
    GoodRows alpha beta (onRows U N) (S.subtype (· ∈ U)) := by
  constructor
  · intro u
    rw [onRows_rowFraction]
    exact hgood.1 u.val
  · simp_rw [onRows_rowFraction]
    rw [sum_coe_sort U (fun v => rowFraction (fun w => N w ∩ U) S v)]
    apply le_trans _ hgood.2
    exact sum_le_sum_of_subset_of_nonneg (subset_univ U)
      (fun v _ _ => rowFraction_nonneg _ _ v)

/-- The induced center table inherits the original shared center event on
the actual center subtype. No vertex outside R contributes to its order. -/
theorem center_subtype_goodRows (G : SimpleInput V) (S R : Finset V) (d : ℕ)
    (hgood : SparseCenters.GoodCenters (SparseCenters.inputRows G)
      (SparseCenters.inputCrossRows G S) d R) :
    GoodRows (3 / 5) 8 (onRows R (SparseCenters.inputRows G)) (S.subtype (· ∈ R)) :=
  onRows_good R (SparseCenters.inputRows G) S (center_goodRows G S R d hgood)

/-- The center-subtype deficiency count is charged only to B intersect R. -/
theorem center_subtype_lowSources_card_le (G : SimpleInput V) (R : Finset V) (d : ℕ)
    (hd : Schedule.degreeCutoff ≤ d) :
    (lowSources (onRows R (SparseCenters.inputRows G)) (Schedule.height d)).card ≤
      (SparseCenters.badRows (SparseCenters.inputRows G) d R ∩ R).card := by
  let low := lowSources (onRows R (SparseCenters.inputRows G)) (Schedule.height d)
  let embed : R ↪ V := Function.Embedding.subtype (· ∈ R)
  calc
    _ = (low.map embed).card := by rw [card_map]
    _ ≤ _ := by
      apply card_le_card
      intro v hv
      obtain ⟨u, hu, rfl⟩ := mem_map.mp hv
      refine mem_inter.mpr ⟨?_, u.property⟩
      apply center_lowSources_subset_bad G R d hd
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      have hlow : (onRows R (SparseCenters.inputRows G) u).card < 4 * Schedule.height d :=
        (mem_filter.mp hu).2
      change (SparseCenters.inputRows G u.val ∩ R).card < 4 * Schedule.height d
      simpa only [onRows_card] using hlow

#print axioms colors
#print axioms colors_flipRow
#print axioms colors_opposite_law
#print axioms colors_opposite_mean_le
#print axioms colors_opposite_tenth_tail
#print axioms fairSubset_low_tail
#print axioms colors_opposite_low_tail
#print axioms mul_geometric_le_hundredth
#print axioms target_survives_omission
#print axioms GoodRows.omit
#print axioms oppositeStatistics_eval
#print axioms oppositeStatistics_cost
#print axioms colored_mean_le
#print axioms colored_row_tail
#print axioms colored_sum_tail
#print axioms coloredRows_good_failure
#print axioms expect_extraOmissions_le
#print axioms extraOmissions_failure_le
#print axioms coloredRows_nonzero_degree
#print axioms coloredRows_zero_real_le
#print axioms colored_stage_failure
#print axioms center_goodRows
#print axioms center_lowSources_subset_bad
#print axioms center_lowSources_inside_card_le
#print axioms onRows_rowFraction
#print axioms onRows_good
#print axioms center_subtype_goodRows
#print axioms center_subtype_lowSources_card_le

end
end CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph
