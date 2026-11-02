import CutQueryComplexity.StarContraction2022.Certificates.Parallel.Halving

/-! # Sharp joint bucket charges and retirement amortization

Part of the parallel threshold certificate. The whole parallel C_P bound and
the capped certificate endpoint are in `Certificates/Parallel.lean`.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Certificates

noncomputable section
open scoped Classical ENNReal

variable {V Q : Type} [Fintype V] [DecidableEq V] [Fintype Q] [DecidableEq Q]
variable {π : PublicQuotient V Q} {r : ℕ}

namespace ParallelState

/-- One fixed constant dominates both the actual low-degree decoder and
three-original-query simulation of the degree-10 B primitive. -/
def mixedBucketConstant : ℕ := 281474976710656

def mixedBucketCharge (b n : ℕ) : ℝ :=
  (mixedBucketConstant : ℝ) * ((b : ℝ) + parallelRowWeight b * Real.log (2 * (n : ℝ)))

theorem parallelRowWeight_nonneg (b : ℕ) : 0 ≤ parallelRowWeight b := by
  by_cases hb : b = 0
  · simp only [parallelRowWeight, hb, ite_true, le_refl]
  · have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
    rw [parallelRowWeight, if_neg hb]
    exact div_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith))

theorem mixedBucketCharge_nonneg (b n : ℕ) (hn : 1 ≤ n) : 0 ≤ mixedBucketCharge b n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact mul_nonneg (Nat.cast_nonneg _)
    (add_nonneg (Nat.cast_nonneg _) (mul_nonneg (parallelRowWeight_nonneg b)
      (Real.log_nonneg (by linarith))))

private theorem twoCoefficientCharge_le (b c n : ℕ) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hcn : c ≤ n) (a d : ℝ) (ha : a ≤ mixedBucketConstant)
    (hd0 : 0 ≤ d) (hd : d ≤ mixedBucketConstant) :
    a * b + d * b * Real.log (2 * (c : ℝ)) / Real.log (2 * (b : ℝ)) ≤
      mixedBucketCharge b n := by
  have hb0 : b ≠ 0 := by omega
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hcnR : (c : ℝ) ≤ n := by exact_mod_cast hcn
  have hlog : Real.log (2 * (c : ℝ)) ≤ Real.log (2 * (n : ℝ)) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlogn : 0 ≤ Real.log (2 * (n : ℝ)) := Real.log_nonneg (by linarith)
  have hw := parallelRowWeight_nonneg b
  calc
    _ = a * b + d * (parallelRowWeight b * Real.log (2 * (c : ℝ))) := by
      rw [parallelRowWeight, if_neg hb0]
      ring
    _ ≤ (mixedBucketConstant : ℝ) * b +
        (mixedBucketConstant : ℝ) * (parallelRowWeight b * Real.log (2 * (n : ℝ))) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg _)
      · apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog hw) hd0).trans
        exact mul_le_mul_of_nonneg_right hd (mul_nonneg hw hlogn)
    _ = _ := by unfold mixedBucketCharge; ring

theorem lowBucketNeighbors_cost_eq (s : ParallelState π r) (color : Q → Bool)
    (reps : Finset V) (answers : V → Option (Fin (Fintype.card V + 1)))
    (read : Finset V → ℝ) :
    (s.lowBucketNeighbors color reps answers).cost read =
      (s.lowRowUpdate color (lowColorRows (π := π) color reps answers)).cost read := by
  let rows := lowColorRows (π := π) color reps answers
  let cols := blueVertices (π := π) color
  let raw := s.checkedLowDegreeResidual (Function.Embedding.subtype (· ∈ rows))
    (Function.Embedding.subtype (· ∈ cols))
  change (raw.map (fun out => out.map (learnedNext rows cols))).cost read =
    (raw.map (fun out => out.bind fun M =>
      s.assembleNeighbors color rows (learnedNext rows cols M))).cost read
  rw [det_cost_map, det_cost_map]

private theorem deterministic_expected {I A O : Type} {b : ℕ}
    (tree : DTree I A O b) (read : I → A) :
    (RTree.ofDeterministic tree).expectedQueries read = (tree.cost read : ℝ≥0∞) := by
  change CutQueryComplexity.Probability.expect (RTree.run read (RTree.ofDeterministic tree))
    (fun out => (out.2 : ℝ≥0∞)) = _
  rw [RTree.run_ofDeterministic, CutQueryComplexity.Probability.expect_pure]
  rfl

/-- The actual low/high call, including empty and singleton row buckets,
obeys a common sharp charge. Degree conditions come from its count queries;
the estimate requires no externally supplied recovery or cost premise. -/
theorem bucketCall_expected (s : ParallelState π r) (color : Q → Bool) (reps : Finset V)
    (T : ℕ) (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (hn : 1 ≤ Fintype.card V) (i : Option (Fin (highBucketCount (Fintype.card V)))) :
    (s.bucketCall color reps ((s.colorRows color reps).eval G.toWeighted.cut) T i).expectedQueries
      G.toWeighted.cut ≤ ENNReal.ofReal
        (mixedBucketCharge (colorBucket (π := π) color reps
          ((s.colorRows color reps).eval G.toWeighted.cut) i).card (Fintype.card V)) := by
  let answers := (s.colorRows color reps).eval G.toWeighted.cut
  let cols := blueVertices (π := π) color
  cases i with
  | none =>
      let rows := lowColorRows (π := π) color reps answers
      have hcost : ((s.lowBucketNeighbors color reps answers).cost G.toWeighted.cut : ℝ) ≤
          mixedBucketCharge rows.card (Fintype.card V) := by
        rw [s.lowBucketNeighbors_cost_eq]
        change ((s.lowRowUpdate color rows).cost G.toWeighted.cut : ℝ) ≤ _
        by_cases hrows : rows = ∅
        · rw [hrows, s.lowRowUpdate_empty_cost]
          simpa only [Nat.cast_zero, Finset.card_empty] using
            mixedBucketCharge_nonneg 0 (Fintype.card V) hn
        · have hm : 1 ≤ rows.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hrows)
          obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hrows
          obtain ⟨v, hv, hp⟩ := s.lowColorRows_positive color reps G hs hu
          have hc : 1 ≤ cols.card := Finset.card_pos.mpr ⟨v, hv⟩
          apply (s.lowRowUpdate_cost_bound color rows hm hc G.toWeighted.cut).trans
          exact twoCoefficientCharge_le rows.card cols.card (Fintype.card V) hm hc
            (Finset.card_le_univ cols) 3 1006632960
            (by norm_num [mixedBucketConstant]) (by norm_num) (by norm_num [mixedBucketConstant])
      have hh : (RTree.ofDeterministic (s.lowBucketNeighbors color reps answers)).expectedQueries
          G.toWeighted.cut ≤
          ENNReal.ofReal (mixedBucketCharge rows.card (Fintype.card V)) := by
        rw [deterministic_expected]
        simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hcost
      simpa only [bucketCall, colorBucket, RTree.expectedQueries, RTree.run_weaken] using hh
  | some i =>
      let rows := highColorRows (π := π) color reps answers i.val
      by_cases hrows : rows = ∅
      · have he := s.highBucketNeighbors_empty color reps answers i.val T hrows G.toWeighted.cut
        change CutQueryComplexity.Probability.expect
          (RTree.run G.toWeighted.cut ((s.highBucketNeighbors color reps answers i.val T).weaken
            (highBucketBudget_le _ _ T))) (fun out => (out.2 : ℝ≥0∞)) ≤ _
        rw [RTree.run_weaken, he, CutQueryComplexity.Probability.expect_pure]
        simp only [Nat.cast_zero]
        exact bot_le
      · have hm : 1 ≤ rows.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hrows)
        have hb := s.highBucketNeighbors_expected color reps i.val T G hs hm
        have hdegree := s.highColorRows_degree color reps i.val G hs
        obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hrows
        have hc : 1 ≤ cols.card := by
          let row := s.residualMatrix (Function.Embedding.subtype (· ∈ rows))
            (Function.Embedding.subtype (· ∈ cols)) G ⟨u, hu⟩
          have hlow : 10 * 2 ^ i.val ≤ Recovery.sampleCount row Finset.univ := by
            simpa only [Recovery.sampleCount, Recovery.measure, Recovery.rowVector] using
              (hdegree ⟨u, hu⟩).1
          have hhigh := Recovery.sampleCount_le_card row Finset.univ
          have hpow : 0 < (2 : ℕ) ^ i.val := pow_pos (by norm_num) _
          simp only [Finset.card_univ, Fintype.card_coe] at hhigh
          omega
        have harith : 3 * Recovery.bucketExpectedBound rows cols 10 ≤
            mixedBucketCharge rows.card (Fintype.card V) := by
          have hh := twoCoefficientCharge_le rows.card cols.card (Fintype.card V) hm hc
            (Finset.card_le_univ cols) (3 * Recovery.bucketConstant) (30 * Recovery.bucketConstant)
            (by norm_num [Recovery.bucketConstant, mixedBucketConstant])
            (by positivity) (by norm_num [Recovery.bucketConstant, mixedBucketConstant])
          calc
            _ = (3 * Recovery.bucketConstant : ℝ) * rows.card +
                (30 * Recovery.bucketConstant : ℝ) * rows.card *
                  Real.log (2 * (cols.card : ℝ)) / Real.log (2 * (rows.card : ℝ)) := by
              simp only [Recovery.bucketExpectedBound, Fintype.card_coe, Nat.cast_ofNat]
              ring
            _ ≤ _ := hh
        have hh : (s.highBucketNeighbors color reps answers i.val T).expectedQueries
            G.toWeighted.cut ≤ ENNReal.ofReal (mixedBucketCharge rows.card (Fintype.card V)) := by
          apply hb.trans
          have hof : 3 * ENNReal.ofReal (Recovery.bucketExpectedBound rows cols 10) =
              ENNReal.ofReal (3 * Recovery.bucketExpectedBound rows cols 10) := by
            rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
            norm_num
          rw [hof]
          exact ENNReal.ofReal_le_ofReal harith
        simpa only [bucketCall, colorBucket, RTree.expectedQueries, RTree.run_weaken] using hh

/-- All actual buckets are charged jointly against a public phase scale.
The scale need only bound the representatives, so empty or tiny favorable
sets do not incur a hidden assumption that they outnumber the buckets. -/
theorem jointBucketNeighbors_expected (s : ParallelState π r) (color : Q → Bool)
    (reps : Finset V) (T scale : ℕ) (G : SimpleInput V)
    (hs : s.usedGraph.IsSubgraph G.toWeighted) (hn : 1 ≤ Fintype.card V)
    (hrep : reps.card ≤ scale)
    (hslots : Fintype.card (Option (Fin (highBucketCount (Fintype.card V)))) ≤ scale) :
    (s.jointBucketNeighbors color reps ((s.colorRows color reps).eval G.toWeighted.cut) T).expectedQueries
      G.toWeighted.cut ≤ ENNReal.ofReal
        ((mixedBucketConstant : ℝ) * ((scale : ℝ) +
          4 * scale * Real.log (2 * (Fintype.card V : ℝ)) /
            Real.log (2 * (scale : ℝ) /
              Fintype.card (Option (Fin (highBucketCount (Fintype.card V))))))) := by
  let I := Option (Fin (highBucketCount (Fintype.card V)))
  let answers := (s.colorRows color reps).eval G.toWeighted.cut
  let sizes := fun i : I => (colorBucket (π := π) color reps answers i).card
  let J := Fintype.card I
  have hJ : (0 : ℝ) < J := by
    simp only [J, I, Fintype.card_option, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    positivity
  have hsum : (∑ i, (sizes i : ℝ)) ≤ scale := by
    exact_mod_cast (colorBucket_card_sum_le (π := π) color reps answers).trans hrep
  have hscale : (J : ℝ) ≤ scale := by exact_mod_cast hslots
  have hratio : 1 ≤ (scale : ℝ) / J := (le_div_iff₀ hJ).mpr (by simpa using hscale)
  have hweight : (∑ i, parallelRowWeight (sizes i)) ≤
      4 * scale / Real.log (2 * (scale : ℝ) / J) := by
    have hslots' : (Fintype.card I : ℝ) * ((scale : ℝ) / J) ≤ scale := by
      change (J : ℝ) * ((scale : ℝ) / J) ≤ scale
      exact le_of_eq (by field_simp)
    simpa only [mul_div_assoc] using
      parallelRowWeight_sum sizes scale ((scale : ℝ) / J) hratio hsum hslots'
  have hlogn : 0 ≤ Real.log (2 * (Fintype.card V : ℝ)) := by
    apply Real.log_nonneg
    have hnR : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
    linarith
  have hcharge : (∑ i, mixedBucketCharge (sizes i) (Fintype.card V)) ≤
      (mixedBucketConstant : ℝ) * ((scale : ℝ) +
        4 * scale * Real.log (2 * (Fintype.card V : ℝ)) /
          Real.log (2 * (scale : ℝ) / J)) := by
    simp only [mixedBucketCharge]
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have hh := add_le_add hsum (mul_le_mul_of_nonneg_right hweight hlogn)
    convert hh using 1 <;> ring
  have hcol := s.jointBucketNeighbors_expected_le_sum color reps answers T G.toWeighted.cut
  have hlist : ((Finset.univ.toList : List I).map
      (fun i => (s.bucketCall color reps answers T i).expectedQueries G.toWeighted.cut)).sum =
      ∑ i : I, (s.bucketCall color reps answers T i).expectedQueries G.toWeighted.cut := by
    simpa only [Finset.toList_toFinset] using
      (List.sum_toFinset (fun i : I =>
        (s.bucketCall color reps answers T i).expectedQueries G.toWeighted.cut)
        (Finset.nodup_toList Finset.univ)).symm
  rw [hlist] at hcol
  calc
    _ ≤ ∑ i : I, ENNReal.ofReal (mixedBucketCharge (sizes i) (Fintype.card V)) :=
      hcol.trans (Finset.sum_le_sum (fun i _ => s.bucketCall_expected color reps T G hs hn i))
    _ = ENNReal.ofReal (∑ i : I, mixedBucketCharge (sizes i) (Fintype.card V)) :=
      (ENNReal.ofReal_sum_of_nonneg (fun i _ => mixedBucketCharge_nonneg (sizes i) _ hn)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hcharge

/-- A numerical charge for one actual mixed bucket stage, retaining the
joint denominator and including the number of low/high buckets exactly. -/
def mixedStageBound (n scale : ℕ) : ℝ :=
  (mixedBucketConstant : ℝ) * ((scale : ℝ) +
    4 * scale * Real.log (2 * (n : ℝ)) /
      Real.log (2 * (scale : ℝ) / Fintype.card (Option (Fin (highBucketCount n)))))

theorem mixedUpdate_expected (s : ParallelState π r) (color : Q → Bool) (reps : Finset V)
    (T scale : ℕ) (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (hn : 1 ≤ Fintype.card V) (hrep : reps.card ≤ scale)
    (hslots : Fintype.card (Option (Fin (highBucketCount (Fintype.card V)))) ≤ scale) :
    (s.mixedUpdate color reps ((s.colorRows color reps).eval G.toWeighted.cut) T).expectedQueries
      G.toWeighted.cut ≤ ENNReal.ofReal (mixedStageBound (Fintype.card V) scale) := by
  rw [mixedUpdate, mapped_expected]
  exact s.jointBucketNeighbors_expected color reps T scale G hs hn hrep hslots

/-- Fresh coloring is free; all row-count queries and the actual mixed
recovery are charged. The bound is uniform over the finite recovery fuel. -/
theorem fairBatch_expected (s : ParallelState π r) (hr : 0 < r) (reps : Finset V)
    (T scale : ℕ) (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (hn : 1 ≤ Fintype.card V) (hrep : reps.card ≤ scale)
    (hslots : Fintype.card (Option (Fin (highBucketCount (Fintype.card V)))) ≤ scale) :
    (s.fairBatch hr reps T).expectedQueries G.toWeighted.cut ≤
      3 * (scale : ℝ≥0∞) + ENNReal.ofReal (mixedStageBound (Fintype.card V) scale) := by
  dsimp only [fairBatch, fairBatchBudget]
  rw [mixture_expected, CutQueryComplexity.Probability.expect_map]
  apply CutQueryComplexity.Probability.expect_le_of_le_on_support
  intro tape htape
  rw [bind_expected]
  simp only [RTree.eval_weaken, RTree.eval_ofDeterministic,
    CutQueryComplexity.Probability.expect_pure, weaken_expected, deterministic_expected,
    cast_expected]
  apply add_le_add
  · have hc := (s.colorRows_cost
      (componentColor (s.forests (lastIndex hr)).quotient tape) reps G.toWeighted.cut).trans
        (Nat.mul_le_mul_left 3 hrep)
    exact_mod_cast hc
  · exact s.mixedUpdate_expected
      (componentColor (s.forests (lastIndex hr)).quotient tape) reps T scale G hs hn hrep hslots

/-- Remaining original vertices are a telescoping retirement credit. An
explicit failure has credit zero; this is solely an accounting convention
and does not turn failure into a certificate. -/
def retirementCredit : Option (ParallelState π r) → ℕ
  | none => 0
  | some s => Fintype.card V - s.inactive.card

theorem mixedUpdate_retirementCredit (s : ParallelState π r) (color : Q → Bool)
    (reps : Finset V) (answers : V → Option (Fin (Fintype.card V + 1))) (T : ℕ)
    (read : Finset V → ℝ) {out : Option (ParallelState π r)}
    (hout : out ∈ ((s.mixedUpdate color reps answers T).eval read).support) :
    retirementCredit out ≤ retirementCredit (some s) := by
  cases out with
  | none => exact Nat.zero_le _
  | some t =>
      rw [mixedUpdate, RTree.eval_map] at hout
      obtain ⟨table, htable, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
      cases table with
      | none => cases he
      | some next =>
          have ha : s.assembleNeighbors color (positiveColorRows (π := π) color reps answers)
              next = some t := he
          have hi := (s.assembleNeighbors_monotone color _ next ha).1
          simp only [retirementCredit, hi, le_refl]

theorem fairBatch_retirementCredit (s : ParallelState π r) (hr : 0 < r)
    (reps : Finset V) (T : ℕ) (read : Finset V → ℝ) :
    CutQueryComplexity.Probability.expect ((s.fairBatch hr reps T).eval read)
      (fun out => (retirementCredit out : ℝ≥0∞)) ≤ (retirementCredit (some s) : ℝ≥0∞) := by
  apply CutQueryComplexity.Probability.expect_le_of_le_on_support
  intro out hout
  rw [s.fairBatch_eval hr reps T read] at hout
  obtain ⟨tape, htape, hupdate⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  exact_mod_cast s.mixedUpdate_retirementCredit _ reps _ T read hupdate

/-- The scan is paid by newly retired original vertices plus the public
component scale. Its credit is retained, so repeated phases charge n once. -/
theorem representativeScan_retirement_charge (s : ParallelState π r) (hr : 0 < r)
    (scale : ℕ) (hcount : (s.liveBlocks (lastIndex hr)).card ≤ scale)
    (read : Finset V → ℝ) :
    (s.representativeScan hr).cost read +
      3 * retirementCredit (some ((s.representativeScan hr).eval read).state) ≤
        3 * scale + 3 * retirementCredit (some s) := by
  let out := (s.representativeScan hr).eval read
  have hc : (s.representativeScan hr).cost read ≤
      3 * (out.state.inactive.card - s.inactive.card + (s.liveBlocks (lastIndex hr)).card) :=
    s.representativeScan_cost_charge hr read
  have hi : s.inactive ⊆ out.state.inactive := by
    dsimp only [out]
    rw [representativeScan, DTree.eval_cast]
    exact s.scanBlocks_inactive hr (s.liveBlocks (lastIndex hr)).toList read
  have hcard := Finset.card_le_card hi
  have hn := Finset.card_le_univ out.state.inactive
  change (s.representativeScan hr).cost read + 3 * (Fintype.card V - out.state.inactive.card) ≤
    3 * scale + 3 * (Fintype.card V - s.inactive.card)
  omega

/-- Sharp stage charge plus the count queries and the mandatory active-round
padding. Retirement probes are accounted for separately by retained credit. -/
def phaseRoundBound (n scale : ℕ) : ℝ≥0∞ :=
  1 + 6 * (scale : ℝ≥0∞) + ENNReal.ofReal (mixedStageBound n scale)

theorem halvingRound_retirement_charge (s : ParallelState π r) (hr : 0 < r)
    (hl : s.Laminar) (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (hi : s.InactiveSound hr G.toWeighted) (scale T : ℕ) (hn : 1 ≤ Fintype.card V)
    (hcount : (s.liveBlocks (lastIndex hr)).card ≤ scale)
    (hslots : Fintype.card (Option (Fin (highBucketCount (Fintype.card V)))) ≤ scale) :
    (s.halvingRound hr scale T).expectedQueries G.toWeighted.cut +
      3 * CutQueryComplexity.Probability.expect
        ((s.halvingRound hr scale T).eval G.toWeighted.cut)
        (fun out => (retirementCredit out : ℝ≥0∞)) ≤
      (6 * (scale : ℝ≥0∞) + ENNReal.ofReal (mixedStageBound (Fintype.card V) scale)) *
        (if phaseActive hr scale (some s) then 1 else 0) +
          3 * (retirementCredit (some s) : ℝ≥0∞) := by
  by_cases ha : scale / 2 < (s.liveBlocks (lastIndex hr)).card
  · have hactive : phaseActive hr scale (some s) := ha
    rw [if_pos hactive, mul_one, s.halvingRound_eval hr scale T G.toWeighted.cut, if_pos ha]
    dsimp only [halvingRound, scanFairRoundBudget]
    rw [if_pos ha, bind_expected]
    simp only [RTree.eval_weaken, RTree.eval_ofDeterministic,
      CutQueryComplexity.Probability.expect_pure, weaken_expected, deterministic_expected]
    let out := (s.representativeScan hr).eval G.toWeighted.cut
    have hscan : ((s.representativeScan hr).cost G.toWeighted.cut : ℝ≥0∞) +
        3 * (retirementCredit (some out.state) : ℝ≥0∞) ≤
          3 * (scale : ℝ≥0∞) + 3 * (retirementCredit (some s) : ℝ≥0∞) := by
      exact_mod_cast s.representativeScan_retirement_charge hr scale hcount G.toWeighted.cut
    by_cases hb : scale / 2 <
        (((s.representativeScan hr).eval G.toWeighted.cut).state.liveBlocks (lastIndex hr)).card
    · simp only [if_pos hb]
      obtain ⟨htl, hts, hti, hpot, hsep, hpositive⟩ := s.representativeScan_for_batch hr hl G hs hi
      have hrep : out.vertices.card ≤ scale :=
        (s.representativeScan_vertices_bounds hr G hs).2.trans hcount
      have hbatch := out.state.fairBatch_expected hr out.vertices T scale G hts hn hrep hslots
      have hcredit := out.state.fairBatch_retirementCredit hr out.vertices T G.toWeighted.cut
      calc
        _ ≤ ((s.representativeScan hr).cost G.toWeighted.cut : ℝ≥0∞) +
            (3 * scale + ENNReal.ofReal (mixedStageBound (Fintype.card V) scale)) +
            3 * (retirementCredit (some out.state) : ℝ≥0∞) :=
          add_le_add (add_le_add le_rfl hbatch) (mul_le_mul le_rfl hcredit bot_le bot_le)
        _ = (((s.representativeScan hr).cost G.toWeighted.cut : ℝ≥0∞) +
            3 * (retirementCredit (some out.state) : ℝ≥0∞)) +
            (3 * scale + ENNReal.ofReal (mixedStageBound (Fintype.card V) scale)) := by ac_rfl
        _ ≤ (3 * (scale : ℝ≥0∞) + 3 * (retirementCredit (some s) : ℝ≥0∞)) +
            (3 * scale + ENNReal.ofReal (mixedStageBound (Fintype.card V) scale)) :=
          add_le_add hscan le_rfl
        _ = _ := by ring
    · simp only [if_neg hb]
      simp only [RTree.eval_pure, CutQueryComplexity.Probability.expect_pure]
      have hpure : (RTree.pure (q := fairBatchBudget V T) (PMF.pure (some out.state))).expectedQueries
          G.toWeighted.cut = 0 := by
        change CutQueryComplexity.Probability.expect
          (RTree.run G.toWeighted.cut (RTree.pure (q := fairBatchBudget V T)
            (PMF.pure (some out.state)))) (fun x => (x.2 : ℝ≥0∞)) = 0
        simp only [RTree.run_pure, PMF.pure_map, CutQueryComplexity.Probability.expect_pure,
          Nat.cast_zero]
      rw [hpure, add_zero]
      apply hscan.trans
      have hle : 3 * (scale : ℝ≥0∞) ≤
          6 * (scale : ℝ≥0∞) + ENNReal.ofReal (mixedStageBound (Fintype.card V) scale) := by
        apply (mul_le_mul (by norm_num : (3 : ℝ≥0∞) ≤ 6) le_rfl bot_le bot_le).trans
        exact le_add_of_nonneg_right bot_le
      exact add_le_add hle le_rfl
  · have hactive : ¬phaseActive hr scale (some s) := ha
    rw [if_neg hactive, mul_zero, zero_add,
      s.halvingRound_eval hr scale T G.toWeighted.cut, if_neg ha,
      CutQueryComplexity.Probability.expect_pure]
    have hzero : (s.halvingRound hr scale T).expectedQueries G.toWeighted.cut = 0 := by
      dsimp only [halvingRound, scanFairRoundBudget]
      rw [if_neg ha]
      change CutQueryComplexity.Probability.expect
        (RTree.run G.toWeighted.cut (RTree.pure (q := scanFairRoundBudget V Q T)
          (PMF.pure (some s)))) (fun x => (x.2 : ℝ≥0∞)) = 0
      simp only [RTree.run_pure, PMF.pure_map, CutQueryComplexity.Probability.expect_pure,
        Nat.cast_zero]
    rw [hzero, zero_add]

def ScaleHonestResult (hr : 0 < r) (G : SimpleInput V) (scale : ℕ)
    (out : Option (ParallelState π r)) : Prop :=
  HonestResult hr G out ∧ ∀ s, out = some s → (s.liveBlocks (lastIndex hr)).card ≤ scale

theorem halvingStep_scale_honest (hr : 0 < r) (scale T : ℕ) (G : SimpleInput V)
    (out : Option (ParallelState π r)) (ho : ScaleHonestResult hr G scale out)
    {answer : Option (ParallelState π r)}
    (hanswer : answer ∈ ((halvingStep hr scale T out).eval G.toWeighted.cut).support) :
    ScaleHonestResult hr G scale answer := by
  refine ⟨halvingStep_honest hr scale T G out ho.1 hanswer, ?_⟩
  intro t ht
  subst answer
  cases out with
  | none =>
      have he : some t = none := by
        simpa only [halvingStep, RTree.eval_pure, PMF.mem_support_pure_iff] using hanswer
      cases he
  | some s =>
      by_cases ha : phaseActive hr scale (some s)
      · rw [halvingStep, if_pos ha, chargeRound_eval] at hanswer
        have hh := s.halvingRound_success hr ho.1.1 G ho.1.2.1 ho.1.2.2 scale T hanswer
        exact (hh.2.2.2.2 _).trans (ho.2 s rfl)
      · rw [halvingStep_absorbs hr scale T (some s) ha G.toWeighted.cut] at hanswer
        have he : t = s := Option.some.inj ((PMF.mem_support_pure_iff _ _).mp hanswer)
        simpa only [he] using ho.2 s rfl

/-- The implemented padded step has a uniform stage charge plus an exact
telescoping retirement credit. No external expected-cost premise occurs. -/
theorem halvingStep_retirement_charge (hr : 0 < r) (scale T : ℕ) (G : SimpleInput V)
    (out : Option (ParallelState π r)) (ho : ScaleHonestResult hr G scale out)
    (hn : 1 ≤ Fintype.card V)
    (hslots : Fintype.card (Option (Fin (highBucketCount (Fintype.card V)))) ≤ scale) :
    (halvingStep hr scale T out).expectedQueries G.toWeighted.cut +
      3 * CutQueryComplexity.Probability.expect
        ((halvingStep hr scale T out).eval G.toWeighted.cut)
        (fun x => (retirementCredit x : ℝ≥0∞)) ≤
      phaseRoundBound (Fintype.card V) scale * (if phaseActive hr scale out then 1 else 0) +
        3 * (retirementCredit out : ℝ≥0∞) := by
  cases out with
  | none =>
      have hzero : (halvingStep (π := π) hr scale T none).expectedQueries G.toWeighted.cut = 0 := by
        change CutQueryComplexity.Probability.expect
          (RTree.run G.toWeighted.cut (RTree.pure (q := scanFairRoundBudget V Q T + 1)
            (PMF.pure (none : Option (ParallelState π r))))) (fun x => (x.2 : ℝ≥0∞)) = 0
        simp only [RTree.run_pure, PMF.pure_map, CutQueryComplexity.Probability.expect_pure,
          Nat.cast_zero]
      rw [hzero]
      simp [halvingStep, RTree.eval_pure, CutQueryComplexity.Probability.expect_pure,
        phaseActive, retirementCredit]
  | some s =>
      by_cases ha : phaseActive hr scale (some s)
      · rw [halvingStep, if_pos ha, chargeRound_expectedQueries, chargeRound_eval,
          if_pos ha, mul_one]
        have hh := s.halvingRound_retirement_charge hr ho.1.1 G ho.1.2.1 ho.1.2.2
          scale T hn (ho.2 s rfl) hslots
        rw [if_pos ha, mul_one] at hh
        have hh' := add_le_add hh (le_refl (1 : ℝ≥0∞))
        simpa only [phaseRoundBound, add_assoc, add_comm, add_left_comm] using hh'
      · rw [halvingStep, if_neg ha]
        have hzero : (RTree.pure (q := scanFairRoundBudget V Q T + 1) (PMF.pure (some s))).expectedQueries
            G.toWeighted.cut = 0 := by
          change CutQueryComplexity.Probability.expect
            (RTree.run G.toWeighted.cut (RTree.pure (q := scanFairRoundBudget V Q T + 1)
              (PMF.pure (some s)))) (fun x => (x.2 : ℝ≥0∞)) = 0
          simp only [RTree.run_pure, PMF.pure_map, CutQueryComplexity.Probability.expect_pure,
            Nat.cast_zero]
        rw [hzero, RTree.eval_pure, CutQueryComplexity.Probability.expect_pure]
        simp only [if_neg ha, mul_zero, zero_add, le_refl]

/-- Actual finite query cost is bounded by actual active visits, retaining
the retirement credit at the end. This is the telescoping bridge that avoids
charging all n vertices independently in each halving phase. -/
theorem halvingIterations_retirement_charge (hr : 0 < r) (scale T horizon : ℕ)
    (G : SimpleInput V) (out : Option (ParallelState π r))
    (ho : ScaleHonestResult hr G scale out) (hn : 1 ≤ Fintype.card V)
    (hslots : Fintype.card (Option (Fin (highBucketCount (Fintype.card V)))) ≤ scale) :
    (halvingIterations hr scale T horizon out).expectedQueries G.toWeighted.cut +
      3 * CutQueryComplexity.Probability.expect
        ((halvingIterations hr scale T horizon out).eval G.toWeighted.cut)
        (fun x => (retirementCredit x : ℝ≥0∞)) ≤
      phaseRoundBound (Fintype.card V) scale *
        FiniteProgress.activeVisits
          (fun x => (halvingStep hr scale T x).eval G.toWeighted.cut)
          (phaseActive hr scale) horizon out + 3 * (retirementCredit out : ℝ≥0∞) := by
  induction horizon generalizing out with
  | zero =>
      simp only [halvingIterations, pure_expected, RTree.eval_pure,
        CutQueryComplexity.Probability.expect_pure, FiniteProgress.activeVisits,
        mul_zero, zero_add, le_refl]
  | succ horizon ih =>
      let next := fun x : Option (ParallelState π r) => (halvingStep hr scale T x).eval G.toWeighted.cut
      let credit := fun x : Option (ParallelState π r) => (retirementCredit x : ℝ≥0∞)
      let visits := FiniteProgress.activeVisits next (phaseActive hr scale) horizon
      let B := phaseRoundBound (Fintype.card V) scale
      have hinner : CutQueryComplexity.Probability.expect (next out)
          (fun x => (halvingIterations hr scale T horizon x).expectedQueries G.toWeighted.cut +
            3 * CutQueryComplexity.Probability.expect
              ((halvingIterations hr scale T horizon x).eval G.toWeighted.cut) credit) ≤
          CutQueryComplexity.Probability.expect (next out) (fun x => B * visits x + 3 * credit x) := by
        apply CutQueryComplexity.Probability.expect_mono_on_support
        intro x hx
        exact ih x (halvingStep_scale_honest hr scale T G out ho hx)
      rw [CutQueryComplexity.Probability.expect_add,
        CutQueryComplexity.Probability.expect_const_mul] at hinner
      rw [CutQueryComplexity.Probability.expect_add,
        CutQueryComplexity.Probability.expect_const_mul,
        CutQueryComplexity.Probability.expect_const_mul] at hinner
      have hstep := halvingStep_retirement_charge hr scale T G out ho hn hslots
      calc
        _ = (halvingStep hr scale T out).expectedQueries G.toWeighted.cut +
            (CutQueryComplexity.Probability.expect (next out)
              (fun x => (halvingIterations hr scale T horizon x).expectedQueries G.toWeighted.cut) +
              3 * CutQueryComplexity.Probability.expect (next out)
                (fun x => CutQueryComplexity.Probability.expect
                  ((halvingIterations hr scale T horizon x).eval G.toWeighted.cut) credit)) := by
          simp only [halvingIterations, cast_expected, bind_expected,
            RTree.eval_cast, RTree.eval_bind, CutQueryComplexity.Probability.expect_bind]
          exact add_assoc _ _ _
        _ ≤ (halvingStep hr scale T out).expectedQueries G.toWeighted.cut +
            (B * CutQueryComplexity.Probability.expect (next out) visits +
              3 * CutQueryComplexity.Probability.expect (next out) credit) :=
          add_le_add le_rfl hinner
        _ = ((halvingStep hr scale T out).expectedQueries G.toWeighted.cut +
              3 * CutQueryComplexity.Probability.expect (next out) credit) +
            B * CutQueryComplexity.Probability.expect (next out) visits := by ac_rfl
        _ ≤ (B * (if phaseActive hr scale out then 1 else 0) + 3 * credit out) +
            B * CutQueryComplexity.Probability.expect (next out) visits := add_le_add hstep le_rfl
        _ = _ := by
          simp only [FiniteProgress.activeVisits, mul_add]
          ac_rfl

/-- The implemented finite halving phase has a uniform sharp expected
query charge, independent of cap. The unused original-vertex credit remains
on the left for summation across subsequent phases. -/
theorem halvingPhase_retirement_charge (s : ParallelState π r) (hr : 0 < r)
    (hl : s.Laminar) (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (hi : s.InactiveSound hr G.toWeighted) (scale cap : ℕ) (hscale : 0 < scale)
    (hn : 1 ≤ Fintype.card V) (hcount : (s.liveBlocks (lastIndex hr)).card ≤ scale)
    (hslots : Fintype.card (Option (Fin (highBucketCount (Fintype.card V)))) ≤ scale) :
    (s.halvingPhase hr scale cap).expectedQueries G.toWeighted.cut +
      3 * CutQueryComplexity.Probability.expect
        ((s.halvingPhase hr scale cap).eval G.toWeighted.cut)
        (fun x => (retirementCredit x : ℝ≥0∞)) ≤
      phaseRoundBound (Fintype.card V) scale * (8 * (r : ℝ≥0∞)) +
        3 * (retirementCredit (some s) : ℝ≥0∞) := by
  have ho : ScaleHonestResult hr G scale (some s) := by
    refine ⟨⟨hl, hs, hi⟩, ?_⟩
    intro t ht
    have he : s = t := Option.some.inj ht
    simpa only [← he] using hcount
  have hcharge := halvingIterations_retirement_charge hr scale (cap + 1) (cap + 1)
    G (some s) ho hn hslots
  have hvisits := s.halvingIterations_visits_le hr hl G hs hi scale (cap + 1) (cap + 1)
    hscale hcount
  have hcredit : CutQueryComplexity.Probability.expect
      ((s.halvingPhase hr scale cap).eval G.toWeighted.cut)
      (fun x => (retirementCredit x : ℝ≥0∞)) ≤
      CutQueryComplexity.Probability.expect
        ((halvingIterations hr scale (cap + 1) (cap + 1) (some s)).eval G.toWeighted.cut)
        (fun x => (retirementCredit x : ℝ≥0∞)) := by
    rw [halvingPhase, RTree.eval_map, CutQueryComplexity.Probability.expect_map]
    apply CutQueryComplexity.Probability.expect_mono_on_support
    intro x hx
    by_cases ha : phaseActive hr scale x
    · simp only [if_pos ha, retirementCredit, Nat.cast_zero]
      exact bot_le
    · simp only [if_neg ha, le_refl]
  rw [halvingPhase, mapped_expected]
  apply (add_le_add le_rfl (mul_le_mul le_rfl hcredit bot_le bot_le)).trans
  apply hcharge.trans
  exact add_le_add (mul_le_mul le_rfl hvisits bot_le bot_le) le_rfl

end ParallelState

#print axioms ParallelState.mixedBucketCharge_nonneg
#print axioms ParallelState.bucketCall_expected
#print axioms ParallelState.jointBucketNeighbors_expected
#print axioms ParallelState.mixedUpdate_expected
#print axioms ParallelState.fairBatch_expected
#print axioms ParallelState.fairBatch_retirementCredit
#print axioms ParallelState.representativeScan_retirement_charge
#print axioms ParallelState.halvingRound_retirement_charge
#print axioms ParallelState.halvingStep_scale_honest
#print axioms ParallelState.halvingStep_retirement_charge
#print axioms ParallelState.halvingIterations_retirement_charge
#print axioms ParallelState.halvingPhase_retirement_charge

end
end CutQueryComplexity.StarContraction2022.Certificates
