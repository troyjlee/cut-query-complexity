import CutQueryComplexity.DeterministicAPMCExpansion.Flow.BFS
import Mathlib.Tactic.FinCases

/-!
# Publicly selected residual cut certificates

The middle pair is selected by the cardinalities of computed layers, not by
minimizing unknown cut capacities. Its measured shore is an actual one-query
output. The source-cut identity retains the factor-two approximation gap.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.Flow

open Finset DirectedCertificate Certificate
open DirectedUnitST.Repair
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

theorem internalVertices_card :
    (internalVertices (source : NetworkVertex V) sink).card = Fintype.card V := by
  have he : internalVertices (source : NetworkVertex V) sink =
      (univ : Finset V).map (Function.Embedding.inl : V ↪ NetworkVertex V) := by
    ext x
    rw [internalVertices, mem_filter]
    simp only [mem_univ, true_and]
    cases x with
    | inl v => simp [source, sink]
    | inr i => fin_cases i <;> simp [source, sink]
  rw [he, card_map, card_univ]

theorem residual_internal_pair_bound {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G)
    {a z : V → ℕ} {f : NetworkVertex V → NetworkVertex V → ℝ}
    (hf : (directed (twoStar G a z)).Feasible f) :
    ∀ u v, u ≠ source → u ≠ sink → v ≠ source → v ≠ sink →
      (residualNetwork G a z f hf).c u v + (residualNetwork G a z f hf).c v u ≤ 2 := by
  intro u v hus hut hvs hvt
  cases u with
  | inr i => fin_cases i <;> simp [source, sink] at hus hut
  | inl x =>
      cases v with
      | inr i => fin_cases i <;> simp [source, sink] at hvs hvt
      | inl y => exact internal_residual_pair_bound hG hf x y

def middlePair (level : NetworkVertex V → ℕ) (j : ℕ) : Finset (NetworkVertex V) :=
  layer level (2 * j + 1) ∪ layer level (2 * j + 2)

/-- Finite choice over an explicit public table of layer cardinalities. -/
def middleIndex (level : NetworkVertex V → ℕ) (d : ℕ) : ℕ :=
  if h : (range ((d - 1) / 2)).Nonempty then
    Classical.choose (exists_mem_eq_inf' h (fun j => (middlePair level j).card))
  else 0

theorem middleIndex_spec (level : NetworkVertex V → ℕ) {d : ℕ} (hd : 4 ≤ d) :
    middleIndex level d ∈ range ((d - 1) / 2) ∧
      ∀ j ∈ range ((d - 1) / 2),
        (middlePair level (middleIndex level d)).card ≤ (middlePair level j).card := by
  have hn : (range ((d - 1) / 2)).Nonempty := ⟨0, mem_range.mpr (by omega)⟩
  have hs := Classical.choose_spec
    (exists_mem_eq_inf' hn (fun j => (middlePair level j).card))
  rw [middleIndex, dif_pos hn]
  refine ⟨hs.1, ?_⟩
  intro j hj
  rw [← hs.2]
  exact inf'_le _ hj

def middlePrefix (level : NetworkVertex V → ℕ) (d : ℕ) : Finset (NetworkVertex V) :=
  levelPrefix level (2 * middleIndex level d + 1)

/-- The actual selected prefix has small capacity. The only property of
capacities used by its selection is a theorem, not an input to the selector. -/
theorem middlePrefix_bound (H : WeightedDiGraph (NetworkVertex V))
    (level : NetworkVertex V → ℕ) (d : ℕ)
    (hlevel : ∀ u v, 0 < H.c u v → level v ≤ level u + 1)
    (hs : level source = 0) (ht : level sink = d) (hd : 4 ≤ d)
    (hcap : ∀ u v, u ≠ source → u ≠ sink → v ≠ source → v ≠ sink →
      H.c u v + H.c v u ≤ 2) :
    source ∈ middlePrefix level d ∧ sink ∉ middlePrefix level d ∧
      H.out (middlePrefix level d) ≤ 8 * (Fintype.card V : ℝ) ^ 2 / (d : ℝ) ^ 2 := by
  let m := (d - 1) / 2
  let i := middleIndex level d
  obtain ⟨hi, hminimal⟩ := middleIndex_spec level hd
  have hm : 0 < m := by dsimp [m]; omega
  have hmid : ∀ j ∈ range m, 2 * j + 1 + 2 ≤ d := by
    intro j hj
    simp only [mem_range] at hj
    dsimp [m] at hj
    omega
  have hsub : ∀ j ∈ range m,
      middlePair level j ⊆ internalVertices (source : NetworkVertex V) sink := by
    intro j hj v hv
    simp only [middlePair, layer, mem_union, mem_filter, mem_univ, true_and] at hv
    have hjd := hmid j hj
    simp only [internalVertices, mem_filter, mem_univ, true_and]
    constructor
    · intro he; subst v; omega
    · intro he; subst v; omega
  have hAB : ∀ j, Disjoint (layer level (2 * j + 1)) (layer level (2 * j + 2)) := by
    intro j
    apply disjoint_left.mpr
    intro v hv hw
    simp only [layer, mem_filter, mem_univ, true_and] at hv hw
    omega
  have hdisj : (range m : Set ℕ).PairwiseDisjoint (middlePair level) := by
    intro j _ k _ hjk
    apply disjoint_left.mpr
    intro v hv hw
    simp only [middlePair, layer, mem_union, mem_filter, mem_univ, true_and] at hv hw
    omega
  obtain ⟨j, hj, hsize⟩ := exists_small_disjoint_member_in
    (internalVertices (source : NetworkVertex V) sink) (range m)
    ⟨0, mem_range.mpr hm⟩ (middlePair level) hsub hdisj
  simp only [card_range, internalVertices_card] at hsize
  have hchosen : m * (middlePair level i).card ≤ Fintype.card V :=
    (Nat.mul_le_mul_left m (hminimal j hj)).trans hsize
  have hi' : i ∈ range m := hi
  have hid := hmid i hi'
  have hsource : source ∈ middlePrefix level d := by
    simp [middlePrefix, levelPrefix, hs]
  have hsink : sink ∉ middlePrefix level d := by
    simp only [middlePrefix, levelPrefix, mem_filter, mem_univ, true_and, ht, not_le]
    change 2 * i + 1 < d
    omega
  refine ⟨hsource, hsink, ?_⟩
  have hc := middle_cut_bound H level hlevel source sink d (2 * i + 1)
    hs ht (by omega) hid hcap
  change H.out (middlePrefix level d) ≤
    2 * ((layer level (2 * i + 1)).card : ℝ) * (layer level (2 * i + 2)).card at hc
  have hcard : (middlePair level i).card =
      (layer level (2 * i + 1)).card + (layer level (2 * i + 2)).card :=
    card_union_of_disjoint (hAB i)
  rw [hcard] at hchosen
  have hchosenR : (m : ℝ) * ((layer level (2 * i + 1)).card +
      (layer level (2 * i + 2)).card) ≤ Fintype.card V := by exact_mod_cast hchosen
  have hsumSquare := mul_self_le_mul_self (by positivity) hchosenR
  have hproduct : 4 * ((layer level (2 * i + 1)).card : ℝ) *
      (layer level (2 * i + 2)).card ≤
      (((layer level (2 * i + 1)).card : ℝ) + (layer level (2 * i + 2)).card) ^ 2 := by
    nlinarith [sq_nonneg (((layer level (2 * i + 1)).card : ℝ) -
      (layer level (2 * i + 2)).card)]
  have hp := mul_le_mul_of_nonneg_left hproduct (sq_nonneg (m : ℝ))
  have hcm := mul_le_mul_of_nonneg_left hc (show 0 ≤ 2 * (m : ℝ) ^ 2 by positivity)
  have hsmall : 2 * (m : ℝ) ^ 2 * H.out (middlePrefix level d) ≤
      (Fintype.card V : ℝ) ^ 2 := by nlinarith
  have hdm : (d : ℝ) ≤ 4 * (m : ℝ) := by
    exact_mod_cast (show d ≤ 4 * m by dsimp [m]; omega)
  have hdR : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hsq : (d : ℝ) ^ 2 ≤ 16 * (m : ℝ) ^ 2 := by
    have h := mul_self_le_mul_self hdR.le hdm
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hsq (H.out_nonneg (middlePrefix level d))
  apply (le_div_iff₀ (sq_pos_of_pos hdR)).mpr
  nlinarith

/-- Exact conservation identity for any source shore; no optimality premise. -/
theorem source_cut_eq_value_add_residual (G : WeightedGraph V) (a z : V → ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ)
    (hf : (directed (twoStar G a z)).STFlow source sink f)
    (P : Finset (NetworkVertex V)) (hs : source ∈ P) (ht : sink ∉ P) :
    (twoStar G a z).cut P = netOut f source + (residualNetwork G a z f hf.1).out P := by
  have hsum : ∑ x ∈ P, netOut f x = netOut f source := by
    rw [← sum_erase_add _ _ hs]
    have hz : ∑ x ∈ P.erase source, netOut f x = 0 := sum_eq_zero fun x hx =>
      hf.2 x (ne_of_mem_erase hx) fun he => ht (he ▸ mem_of_mem_erase hx)
    rw [hz, zero_add]
  rw [sum_netOut_eq hf.1.1] at hsum
  change (twoStar G a z).cut P = netOut f source +
    ∑ u ∈ P, ∑ v ∈ Pᶜ, ((twoStar G a z).w u v - f u v)
  simp only [sum_sub_distrib]
  rw [hsum]
  change (twoStar G a z).cut P =
    netOut f source + ((twoStar G a z).cut P - netOut f source)
  ring

structure MeasuredCut (V : Type) where
  shore : Finset (NetworkVertex V)
  capacity : ℝ

def measureCut (a z : V → ℕ) (P : Finset (NetworkVertex V)) :
    DTree (Finset V) ℝ (MeasuredCut V) 1 :=
  (twoStarQuery a z P).map (fun capacity => ⟨P, capacity⟩)

theorem measureCut_eval (G : WeightedGraph V) (a z : V → ℕ)
    (P : Finset (NetworkVertex V)) :
    (measureCut a z P).eval G.cut = ⟨P, (twoStar G a z).cut P⟩ := by
  simp only [measureCut, DTree.eval_map, twoStarQuery_eval]

/-- The strict cut threshold follows from the two different margins.
It is not obtained by assuming a minimum cut or an exact maximum flow. -/
theorem measured_cut_below_threshold (G : WeightedGraph V) (a z : V → ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ)
    (hf : (directed (twoStar G a z)).STFlow source sink f)
    (P : Finset (NetworkVertex V)) (hs : source ∈ P) (ht : sink ∉ P)
    (F η : ℝ) (hvalue : netOut f source < F - 2 * η)
    (hres : (residualNetwork G a z f hf.1).out P ≤ η) :
    ((measureCut a z P).eval G.cut).capacity < F - η := by
  rw [measureCut_eval]
  dsimp only
  rw [source_cut_eq_value_add_residual G a z f hf P hs ht]
  linarith

/-- Specialize the geometric selector to the actual query-produced levels. -/
theorem bfs_middlePrefix_bound (G : WeightedGraph V) (hG : AllPairsAudit.Unweighted G)
    (a z : V → ℕ) (f : NetworkVertex V → NetworkVertex V → ℝ)
    (hf : (directed (twoStar G a z)).Feasible f) (η h : ℕ)
    (hh : 4 ≤ h) (hscale : 8 * Fintype.card V ^ 2 ≤ η * h ^ 2)
    (hd : h ≤ bfsLevel ((bfsProg a z f source).eval G.cut) sink) :
    let data := (bfsProg a z f source).eval G.cut
    let P := middlePrefix (bfsLevel data) (bfsLevel data sink)
    source ∈ P ∧ sink ∉ P ∧ (residualNetwork G a z f hf).out P ≤ η := by
  let data := (bfsProg a z f source).eval G.cut
  let d := bfsLevel data sink
  obtain ⟨hs, hrise, _⟩ := bfsProg_level_rise G a z f hf source
  obtain ⟨hsource, hsink, hbound⟩ := middlePrefix_bound
    (residualNetwork G a z f hf) (bfsLevel data) d hrise hs rfl
    (hh.trans hd) (residual_internal_pair_bound hG hf)
  refine ⟨hsource, hsink, hbound.trans ?_⟩
  have hdNat : 0 < d := lt_of_lt_of_le (by omega : 0 < h) hd
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hdNat
  apply (div_le_iff₀ (sq_pos_of_pos hdpos)).mpr
  have hscaleR : 8 * (Fintype.card V : ℝ) ^ 2 ≤ (η : ℝ) * (h : ℝ) ^ 2 := by
    exact_mod_cast hscale
  have hleR : (h : ℝ) ≤ d := by exact_mod_cast hd
  have hsquare : (h : ℝ) ^ 2 ≤ (d : ℝ) ^ 2 := by
    have hsquare := mul_self_le_mul_self (by positivity) hleR
    nlinarith
  exact hscaleR.trans (mul_le_mul_of_nonneg_left hsquare (by positivity))

inductive SearchResult (V : Type) where
  | cut : MeasuredCut V → SearchResult V
  | phase : BFSData V → SearchResult V

/-- Called after the explicit flow-value test fails. The output is either a
measured cut or the actual short-distance BFS data for a blocking phase. -/
def searchCutOrLevels (a z : V → ℕ) (f : NetworkVertex V → NetworkVertex V → ℝ)
    (h : ℕ) : Prog (Finset V) ℝ (SearchResult V) :=
  (bfsProg a z f source).bind fun data =>
    if sink ∈ data.unseen then
      (treeProg (measureCut a z data.unseenᶜ)).map SearchResult.cut
    else if h ≤ bfsLevel data sink then
      (treeProg (measureCut a z (middlePrefix (bfsLevel data) (bfsLevel data sink)))).map
        SearchResult.cut
    else .pure (SearchResult.phase data)

theorem searchCutOrLevels_cost (read : Finset V → ℝ) (a z : V → ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ) (h : ℕ) :
    (searchCutOrLevels a z f h).cost read ≤ bfsBudget V + 1 := by
  rw [searchCutOrLevels, Prog.cost_bind]
  have hb := bfsProg_cost read a z f source
  have hm (P : Finset (NetworkVertex V)) :
      ((treeProg (measureCut a z P)).map SearchResult.cut).cost read ≤ 1 := by
    rw [Prog.cost_map, treeProg_cost]
    exact DTree.cost_le _ _
  split_ifs
  · have hc := hm ((bfsProg a z f source).eval read).unseenᶜ
    change _ ≤ bfsBudget V + 1
    exact Nat.add_le_add hb hc
  · have hc := hm (middlePrefix (bfsLevel ((bfsProg a z f source).eval read))
      (bfsLevel ((bfsProg a z f source).eval read) sink))
    exact Nat.add_le_add hb hc
  · simp only [Prog.cost_pure, Nat.add_zero]
    exact hb.trans (Nat.le_succ _)

/-- Correctness of the actual cut-or-short-level producer. Its feasible-flow
input is the loop invariant; no maximum-flow or minimum-cut hypothesis occurs. -/
theorem searchCutOrLevels_correct (G : WeightedGraph V) (hG : AllPairsAudit.Unweighted G)
    (a z : V → ℕ) (f : NetworkVertex V → NetworkVertex V → ℝ)
    (hf : (directed (twoStar G a z)).STFlow source sink f) (F η h : ℕ)
    (hh : 4 ≤ h) (hscale : 8 * Fintype.card V ^ 2 ≤ η * h ^ 2)
    (hvalue : netOut f source < (F : ℝ) - 2 * η) :
    match (searchCutOrLevels a z f h).eval G.cut with
    | .cut result =>
        source ∈ result.shore ∧ sink ∉ result.shore ∧
          result.capacity = (twoStar G a z).cut result.shore ∧
          result.capacity < (F : ℝ) - η
    | .phase data =>
        data = (bfsProg a z f source).eval G.cut ∧
          sink ∉ data.unseen ∧ bfsLevel data sink < h := by
  rw [searchCutOrLevels, Prog.eval_bind]
  split_ifs with hmiss hlong
  · simp only [Prog.eval_map, treeProg_eval, measureCut_eval]
    have hi := bfsProg_invariant G a z f hf.1 source
    have hs : source ∈ ((bfsProg a z f source).eval G.cut).unseenᶜ :=
      mem_compl.mpr hi.source_seen
    have ht : sink ∉ ((bfsProg a z f source).eval G.cut).unseenᶜ := by
      simpa only [mem_compl, not_not] using hmiss
    refine ⟨hs, ht, True.intro, ?_⟩
    have hzero := bfsProg_out_zero G a z f hf.1 source
    rw [source_cut_eq_value_add_residual G a z f hf _ hs ht, hzero, add_zero]
    have hη : (0 : ℝ) ≤ η := by positivity
    linarith
  · simp only [Prog.eval_map, treeProg_eval, measureCut_eval]
    obtain ⟨hs, ht, hsmall⟩ := bfs_middlePrefix_bound G hG a z f hf.1 η h hh hscale hlong
    refine ⟨hs, ht, True.intro, ?_⟩
    rw [source_cut_eq_value_add_residual G a z f hf _ hs ht]
    linarith
  · exact ⟨rfl, hmiss, lt_of_not_ge hlong⟩

end
end CutQueryComplexity.DeterministicAPMCExpansion.Flow

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.middlePrefix_bound
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.source_cut_eq_value_add_residual
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.measureCut_eval
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.measured_cut_below_threshold
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.bfs_middlePrefix_bound
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.searchCutOrLevels_cost
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.searchCutOrLevels_correct
