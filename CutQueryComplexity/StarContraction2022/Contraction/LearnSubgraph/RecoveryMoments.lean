import CutQueryComplexity.StarContraction2022.Recovery.Capped
import CutQueryComplexity.Model.RandomizedComposition

/-!
# Unconditional moments for actual capped recovery

Row expectations are combined by linearity before Markov's inequality. The
common recovery cap is charged separately, without conditioning the row law
on global success or assuming independence between overlapping learned rows.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph

open Finset WeightedGraph
open CutQueryComplexity.Probability
open scoped Classical ENNReal
noncomputable section

variable {U V : Type} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]

/-- General linearity/union calculation, with no independence assumption on
rows. This is instantiated below with actual capped recovery laws. -/
theorem row_moment_failure_bound {A I : Type} [Fintype I]
    (p : PMF A) (ratio : A → I → ℝ) (base : I → ℝ) (h : ℕ)
    {alpha beta : ℝ} (hb : 0 < beta)
    (hbase : ∀ i, 0 ≤ base i) (hratio : ∀ a i, 0 ≤ ratio a i)
    (hsum : (∑ i, base i) ≤ beta)
    (hmean : ∀ i, expect p (fun a => ENNReal.ofReal (ratio a i)) ≤ ENNReal.ofReal (base i))
    (htail : ∀ i, mass p (fun a => alpha + 1 / 10 < ratio a i) ≤
      200 * ENNReal.ofReal (base i) / (h : ℝ≥0∞)) :
    mass p (fun a => ¬ ((∀ i, ratio a i ≤ alpha + 1 / 10) ∧
      (∑ i, ratio a i) ≤ 10 * beta)) ≤
      1 / 10 + 200 * ENNReal.ofReal beta / (h : ℝ≥0∞) := by
  have hsummean : expect p (fun a => ENNReal.ofReal (∑ i, ratio a i)) ≤ ENNReal.ofReal beta := by
    calc
      _ = expect p (fun a => ∑ i, ENNReal.ofReal (ratio a i)) :=
        expect_congr_on_support _ (fun a _ =>
          ENNReal.ofReal_sum_of_nonneg (fun i _ => hratio a i))
      _ = ∑ i, expect p (fun a => ENNReal.ofReal (ratio a i)) := expect_sum _ _ _
      _ ≤ ∑ i, ENNReal.ofReal (base i) := sum_le_sum (fun i _ => hmean i)
      _ = ENNReal.ofReal (∑ i, base i) :=
        (ENNReal.ofReal_sum_of_nonneg (fun i _ => hbase i)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hsum
  have hsumtail : mass p (fun a => 10 * beta < ∑ i, ratio a i) ≤ (1 / 10 : ℝ≥0∞) := by
    have hm := mul_mass_le_expect p (fun a => 10 * beta < ∑ i, ratio a i)
      (fun a => ENNReal.ofReal (∑ i, ratio a i)) (ENNReal.ofReal (10 * beta))
      (fun a _ ha => ENNReal.ofReal_le_ofReal ha.le)
    calc
      _ ≤ expect p (fun a => ENNReal.ofReal (∑ i, ratio a i)) / ENNReal.ofReal (10 * beta) := by
        apply (ENNReal.le_div_iff_mul_le (Or.inl (by positivity))
          (Or.inl ENNReal.ofReal_ne_top)).mpr
        simpa only [mul_comm] using hm
      _ ≤ ENNReal.ofReal beta / ENNReal.ofReal (10 * beta) :=
        ENNReal.div_le_div hsummean le_rfl
      _ = _ := by
        rw [← ENNReal.ofReal_div_of_pos (by positivity : 0 < 10 * beta)]
        have he : beta / (10 * beta) = 1 / 10 := by field_simp [hb.ne']
        rw [he, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 10)]
        norm_num
  have hmaxtail : mass p (fun a => ∃ i, alpha + 1 / 10 < ratio a i) ≤
      200 * ENNReal.ofReal beta / (h : ℝ≥0∞) := by
    have he : (fun a => ∃ i, alpha + 1 / 10 < ratio a i) =
        (fun a => ∃ i ∈ (univ : Finset I), alpha + 1 / 10 < ratio a i) := by
      funext a
      simp only [mem_univ, true_and]
    rw [he]
    calc
      _ ≤ ∑ i, mass p (fun a => alpha + 1 / 10 < ratio a i) := mass_exists_finset_le _ _ _
      _ ≤ ∑ i, 200 * ENNReal.ofReal (base i) / (h : ℝ≥0∞) := sum_le_sum (fun i _ => htail i)
      _ = 200 * (∑ i, ENNReal.ofReal (base i)) / (h : ℝ≥0∞) := by
        simp only [div_eq_mul_inv]
        rw [← Finset.sum_mul, ← Finset.mul_sum]
      _ ≤ _ := by
        apply ENNReal.div_le_div _ le_rfl
        apply mul_le_mul le_rfl _ (by positivity) (by positivity)
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hbase i)]
        exact ENNReal.ofReal_le_ofReal hsum
  calc
    _ ≤ mass p (fun a => (10 * beta < ∑ i, ratio a i) ∨ ∃ i, alpha + 1 / 10 < ratio a i) := by
      apply mass_mono
      intro a ha
      by_contra hn
      apply ha
      constructor
      · intro i
        by_contra hi
        exact hn (Or.inr ⟨i,lt_of_not_ge hi⟩)
      · by_contra hs
        exact hn (Or.inl (lt_of_not_ge hs))
    _ ≤ mass p (fun a => 10 * beta < ∑ i, ratio a i) +
        mass p (fun a => ∃ i, alpha + 1 / 10 < ratio a i) := mass_or_le _ _ _
    _ ≤ _ := add_le_add hsumtail hmaxtail




section MappedLists

variable {X : Type} [DecidableEq X]

theorem map_filter_members (e : X ↪ U) (N : Finset X) (C : Finset U) :
    (N.filter fun x => e x ∈ C).map e = C ∩ N.map e := by
  ext v
  constructor
  · intro hv
    obtain ⟨x,hx,rfl⟩ := mem_map.mp hv
    rcases mem_filter.mp hx with ⟨hx,hC⟩
    exact mem_inter.mpr ⟨hC,mem_map.mpr ⟨x,hx,rfl⟩⟩
  · intro hv
    rcases mem_inter.mp hv with ⟨hC,hv⟩
    obtain ⟨x,hx,rfl⟩ := mem_map.mp hv
    exact mem_map.mpr ⟨x,mem_filter.mpr ⟨hx,hC⟩,rfl⟩

theorem crossingRatio_mapped (e : X ↪ U) (N F : Finset X) (C : Finset U) (hNF : N ⊆ F) :
    Probability.crossingRatio C (N.map e) =
      Probability.crossingRatio (F.filter fun x => e x ∈ C) N := by
  unfold Probability.crossingRatio
  rw [card_map]
  apply congrArg (fun n : ℕ => (n : ℝ) / N.card)
  symm
  apply Finset.card_bij (fun x _ => e x)
  · intro x hx
    simp only [mem_inter, mem_filter] at hx
    simp only [mem_inter, mem_map]
    exact ⟨hx.1.2, x, hx.2, rfl⟩
  · intro x _ y _ he
    exact e.injective he
  · intro v hv
    simp only [mem_inter, mem_map] at hv
    obtain ⟨hC, x, hN, rfl⟩ := hv
    refine ⟨x, ?_, rfl⟩
    simp only [mem_inter, mem_filter]
    exact ⟨⟨hNF hN, hC⟩, hN⟩

end MappedLists

section ActualCappedRows

variable {R C : Type} [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C]

/-- An absent result contributes zero to the unconditional ratio statistic.
This convention is not a declaration of success; cap abort is paid separately. -/
def recoveredRatio (u : R) (Z : Finset C) (out : Option (Recovery.BucketState R C)) : ℝ :=
  out.elim 0 fun st => (st.learned u).elim 0 (Probability.crossingRatio Z)

theorem recoveredRatio_nonneg (u : R) (Z : Finset C)
    (out : Option (Recovery.BucketState R C)) : 0 ≤ recoveredRatio u Z out := by
  cases out with
  | none => exact le_rfl
  | some st =>
      cases hs : st.learned u with
      | none => simp [recoveredRatio, hs]
      | some N => simpa [recoveredRatio, hs] using Probability.crossingRatio_nonneg Z N

theorem recoveredRatio_mean (row : R ↪ V) (col : C ↪ V)
    (hdisjoint : ∀ u v, row u ≠ col v) (G : SimpleInput V) (h : ℕ)
    (hh : 10 ≤ h) (hdegree : ∀ u, h ≤ Recovery.fullDegrees (Recovery.graphMatrix row col G) u)
    (u : R) (Z : Finset C) (hZ : Z ⊆ Recovery.rowNeighbors (Recovery.graphMatrix row col G u)) :
    expect ((Recovery.recoverTree row col h).eval G.toWeighted.cut)
      (fun out => ENNReal.ofReal (recoveredRatio u Z out)) ≤
      ENNReal.ofReal ((Z.card : ℝ) / (Recovery.rowNeighbors (Recovery.graphMatrix row col G u)).card) := by
  have he : (fun out : Option (Recovery.BucketState R C) => ENNReal.ofReal (recoveredRatio u Z out)) =
      fun out => out.elim 0 fun st => (st.learned u).elim 0
        (fun N => ENNReal.ofReal (Probability.crossingRatio Z N)) := by
    funext out
    cases out with
    | none => simp [recoveredRatio]
    | some st => cases hs : st.learned u <;> simp [recoveredRatio, hs]
  rw [he]
  exact Recovery.recoverTree_row_ratio_mean row col hdisjoint G h hh hdegree u Z hZ

/-- The cap's actual unconditional tail, with the source's convenient slack
constant 200. No global-success conditioning appears in the event or law. -/
theorem recoveredRatio_tail (row : R ↪ V) (col : C ↪ V)
    (hdisjoint : ∀ u v, row u ≠ col v) (G : SimpleInput V) (h : ℕ)
    (hh : 10 ≤ h) (hdegree : ∀ u, h ≤ Recovery.fullDegrees (Recovery.graphMatrix row col G) u)
    (u : R) (Z : Finset C) (hZ : Z ⊆ Recovery.rowNeighbors (Recovery.graphMatrix row col G u)) :
    mass ((Recovery.recoverTree row col h).eval G.toWeighted.cut)
      (fun out => (Z.card : ℝ) / (Recovery.rowNeighbors (Recovery.graphMatrix row col G u)).card +
        1 / 10 < recoveredRatio u Z out) ≤
      200 * ENNReal.ofReal ((Z.card : ℝ) / (Recovery.rowNeighbors (Recovery.graphMatrix row col G u)).card) /
        (h : ℝ≥0∞) := by
  let r : ℝ := (Z.card : ℝ) / (Recovery.rowNeighbors (Recovery.graphMatrix row col G u)).card
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hhR : 0 < (h : ℝ) := by exact_mod_cast (show 0 < h by omega)
  have hm : mass ((Recovery.recoverTree row col h).eval G.toWeighted.cut)
      (fun out => r + 1 / 10 < recoveredRatio u Z out) ≤
      mass ((Recovery.recoverTree row col h).eval G.toWeighted.cut)
        (fun out => out.elim False fun st => (st.learned u).elim False
          (fun N => r + 1 / 10 < Probability.crossingRatio Z N)) := by
    apply mass_mono
    intro out hout
    cases out with
    | none => simp [recoveredRatio] at hout; linarith
    | some st =>
        cases hs : st.learned u with
        | none => simp [recoveredRatio, hs] at hout; linarith
        | some N => simpa only [recoveredRatio, Option.elim_some, hs] using hout
  calc
    _ ≤ _ := hm
    _ ≤ ENNReal.ofReal (r / h / (1 / 10 : ℝ) ^ 2) :=
      Recovery.recoverTree_row_ratio_tail row col hdisjoint G h hh hdegree u Z hZ
        (1 / 10) (by norm_num)
    _ ≤ ENNReal.ofReal (200 * r / h) := by
      apply ENNReal.ofReal_le_ofReal
      have hdiv : 0 ≤ r / h := div_nonneg hr hhR.le
      calc
        _ = 100 * (r / h) := by ring
        _ ≤ 200 * (r / h) := by nlinarith
        _ = _ := by ring
    _ = _ := by
      rw [ENNReal.ofReal_div_of_pos hhR, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 200)]
      norm_num [r]

/-- One actual bipartite call, including its cap debit. The arbitrary sets Z
are proof-only crossing columns; no good-event or row-independence oracle is
passed to the program. This is the outside-to-center recovery interface. -/
theorem recoverTree_good_rows_failure (row : R ↪ V) (col : C ↪ V)
    (hdisjoint : ∀ u v, row u ≠ col v) (G : SimpleInput V) (h : ℕ)
    (hh : 10 ≤ h) (hdegree : ∀ u, h ≤ Recovery.fullDegrees (Recovery.graphMatrix row col G) u)
    (Z : R → Finset C) (hZ : ∀ u, Z u ⊆ Recovery.rowNeighbors (Recovery.graphMatrix row col G u))
    (alpha beta : ℝ) (hb : 0 < beta)
    (hmax : ∀ u, ((Z u).card : ℝ) /
      (Recovery.rowNeighbors (Recovery.graphMatrix row col G u)).card ≤ alpha)
    (hsum : (∑ u, ((Z u).card : ℝ) /
      (Recovery.rowNeighbors (Recovery.graphMatrix row col G u)).card) ≤ beta) :
    mass ((Recovery.recoverTree row col h).eval G.toWeighted.cut) (fun out =>
      ¬ ∃ st : Recovery.BucketState R C, out = some st ∧
        (∀ u, ∃ N, st.learned u = some N ∧ h ≤ N.card ∧
          ∀ v ∈ N, (G.w (row u) (col v) : ℕ) = 1) ∧
        (∀ u, recoveredRatio u (Z u) (some st) ≤ alpha + 1 / 10) ∧
        (∑ u, recoveredRatio u (Z u) (some st)) ≤ 10 * beta) ≤
      11 / 100 + 200 * ENNReal.ofReal beta / (h : ℝ≥0∞) := by
  let p := (Recovery.recoverTree row col h).eval G.toWeighted.cut
  let base (u : R) : ℝ := ((Z u).card : ℝ) /
    (Recovery.rowNeighbors (Recovery.graphMatrix row col G u)).card
  let ratio (out : Option (Recovery.BucketState R C)) (u : R) := recoveredRatio u (Z u) out
  let GoodRatio (out : Option (Recovery.BucketState R C)) : Prop :=
    (∀ u, ratio out u ≤ alpha + 1 / 10) ∧ (∑ u, ratio out u) ≤ 10 * beta
  have hm : mass p (fun out => ¬ GoodRatio out) ≤
      1 / 10 + 200 * ENNReal.ofReal beta / (h : ℝ≥0∞) := by
    apply row_moment_failure_bound p ratio base h hb
    · intro u
      dsimp [base]
      positivity
    · intro out u
      exact recoveredRatio_nonneg u (Z u) out
    · exact hsum
    · intro u
      exact recoveredRatio_mean row col hdisjoint G h hh hdegree u (Z u) (hZ u)
    · intro u
      calc
        _ ≤ mass p (fun out => base u + 1 / 10 < ratio out u) := by
          apply mass_mono
          intro out hout
          have hu : base u ≤ alpha := hmax u
          exact (show base u + (1 / 10 : ℝ) ≤ alpha + 1 / 10 by linarith).trans_lt hout
        _ ≤ _ := recoveredRatio_tail row col hdisjoint G h hh hdegree u (Z u) (hZ u)
  calc
    _ ≤ mass p (fun out => out = none ∨ ¬ GoodRatio out) := by
      apply mass_mono_on_support
      intro out hout hfail
      cases out with
      | none => exact Or.inl rfl
      | some st =>
        apply Or.inr
        intro hg
        apply hfail
        exact ⟨st,rfl,Recovery.recoverTree_true_neighbors row col hdisjoint G h hh hdegree
          st hout,hg.1,hg.2⟩
    _ ≤ mass p (fun out => out = none) + mass p (fun out => ¬ GoodRatio out) := mass_or_le _ _ _
    _ ≤ (100 : ℝ≥0∞)⁻¹ + (1 / 10 + 200 * ENNReal.ofReal beta / (h : ℝ≥0∞)) :=
      add_le_add (Recovery.recoverTree_abort_le row col hdisjoint G h hh hdegree) hm
    _ = _ := by
      have he : (100 : ℝ≥0∞)⁻¹ + 1 / 10 = 11 / 100 := by
        calc
          _ = ENNReal.ofReal ((1 / 100 : ℝ) + 1 / 10) := by
            rw [ENNReal.ofReal_add (by norm_num) (by norm_num),
              ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 100),
              ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 10)]
            norm_num [one_div]
          _ = _ := by
            rw [show (1 / 100 : ℝ) + 1 / 10 = 11 / 100 by norm_num,
              ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 100)]
            norm_num
      rw [← add_assoc, he]

/-- The literal outside level 5000 and center ratio parameters (3/5,8)
give a true learned graph with parameters (7/10,80) with probability at
least one half. No distribution is conditioned on global cap success. -/
theorem recoverTree_outside_success_half (row : R ↪ V) (col : C ↪ V)
    (hdisjoint : ∀ u v, row u ≠ col v) (G : SimpleInput V)
    (hdegree : ∀ u, 5000 ≤ Recovery.fullDegrees (Recovery.graphMatrix row col G) u)
    (Z : R → Finset C) (hZ : ∀ u, Z u ⊆ Recovery.rowNeighbors (Recovery.graphMatrix row col G u))
    (hmax : ∀ u, ((Z u).card : ℝ) /
      (Recovery.rowNeighbors (Recovery.graphMatrix row col G u)).card ≤ 3 / 5)
    (hsum : (∑ u, ((Z u).card : ℝ) /
      (Recovery.rowNeighbors (Recovery.graphMatrix row col G u)).card) ≤ 8) :
    (1 / 2 : ℝ≥0∞) ≤
      mass ((Recovery.recoverTree row col 5000).eval G.toWeighted.cut) (fun out =>
        ∃ st : Recovery.BucketState R C, out = some st ∧
          (∀ u, ∃ N, st.learned u = some N ∧ 5000 ≤ N.card ∧
            ∀ v ∈ N, (G.w (row u) (col v) : ℕ) = 1) ∧
          (∀ u, recoveredRatio u (Z u) (some st) ≤ 7 / 10) ∧
          (∑ u, recoveredRatio u (Z u) (some st)) ≤ 80) := by
  let Good := fun out : Option (Recovery.BucketState R C) =>
    ∃ st : Recovery.BucketState R C, out = some st ∧
      (∀ u, ∃ N, st.learned u = some N ∧ 5000 ≤ N.card ∧
        ∀ v ∈ N, (G.w (row u) (col v) : ℕ) = 1) ∧
      (∀ u, recoveredRatio u (Z u) (some st) ≤ 7 / 10) ∧
      (∑ u, recoveredRatio u (Z u) (some st)) ≤ 80
  have hf : mass ((Recovery.recoverTree row col 5000).eval G.toWeighted.cut) (fun out => ¬ Good out) ≤
      ENNReal.ofReal (43 / 100 : ℝ) := by
    dsimp only [Good]
    have hh := recoverTree_good_rows_failure row col hdisjoint G 5000 (by norm_num) hdegree
      Z hZ (3 / 5) 8 (by norm_num) hmax hsum
    have h11 : ENNReal.ofReal (11 / 100 : ℝ) = (11 / 100 : ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 100)]
      norm_num
    have he : (11 / 100 : ℝ≥0∞) + 200 * ENNReal.ofReal (8 : ℝ) / 5000 =
        ENNReal.ofReal (43 / 100 : ℝ) := by
      calc
        _ = ENNReal.ofReal ((11 / 100 : ℝ) + 200 * 8 / 5000) := by
          rw [ENNReal.ofReal_add (by norm_num) (by norm_num), h11,
            ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 5000),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 200)]
          norm_num
        _ = _ := by congr 1; norm_num
    simpa only [show (3 / 5 : ℝ) + 1 / 10 = 7 / 10 by norm_num,
      show (10 : ℝ) * 8 = 80 by norm_num, Nat.cast_ofNat, he] using hh
  have hs := success_of_failure_le ((Recovery.recoverTree row col 5000).eval G.toWeighted.cut)
    Good (by norm_num : (0 : ℝ) ≤ 43 / 100) hf
  have hreal : (1 / 2 : ℝ) ≤
      (mass ((Recovery.recoverTree row col 5000).eval G.toWeighted.cut) Good).toReal := by
    linarith
  have he := ENNReal.ofReal_le_ofReal hreal
  simpa only [ENNReal.ofReal_toReal (mass_ne_top _ _), ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
    ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using he

end ActualCappedRows

theorem recoveredRatio_some {R C : Type} (u : R) (Z : Finset C)
    (st : Recovery.BucketState R C) :
    recoveredRatio u Z (some st) = Probability.crossingRatio Z ((st.learned u).getD ∅) := by
  cases hs : st.learned u <;> simp [recoveredRatio, hs, Probability.crossingRatio]


#print axioms row_moment_failure_bound
#print axioms recoveredRatio_mean
#print axioms recoveredRatio_tail
#print axioms recoverTree_good_rows_failure
#print axioms recoverTree_outside_success_half
#print axioms crossingRatio_mapped

end
end CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph
