import CutQueryComplexity.StarContraction2022.Certificates.Parallel.Mixed
import CutQueryComplexity.StarContraction2022.Certificates.Parallel.Scan
import CutQueryComplexity.StarContraction2022.Certificates.Parallel.Fuel

/-! # Actual finite halving phases and fuel coupling

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

/-- Original representatives retained by the actual component scan. -/
def RepresentativeScan.vertices (out : RepresentativeScan π r) : Finset V :=
  (out.selected.map Prod.snd).toFinset

theorem representativeScan_vertices_nodup (s : ParallelState π r) (hr : 0 < r)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted) :
    (((s.representativeScan hr).eval G.toWeighted.cut).selected.map Prod.snd).Nodup := by
  let out := (s.representativeScan hr).eval G.toWeighted.cut
  have hl := s.representativeScan_distinct_labels hr G.toWeighted.cut
  have hg := s.representativeScan_good hr G hs
  apply List.Nodup.map_on ?_ (List.Nodup.of_map Prod.fst hl)
  intro a ha b hb he
  obtain ⟨hA, hvA, _⟩ := hg.2.1 a ha
  obtain ⟨hB, hvB, _⟩ := hg.2.1 b hb
  have hblocksA := (Finset.mem_filter.mp (Finset.mem_toList.mp hA)).1
  have hblocksB := (Finset.mem_filter.mp (Finset.mem_toList.mp hB)).1
  have hea : s.block (lastIndex hr) a.2 = a.1 := s.block_eq_of_mem _ hblocksA hvA
  have heb : s.block (lastIndex hr) b.2 = b.1 := s.block_eq_of_mem _ hblocksB hvB
  exact Prod.ext (hea.symm.trans ((congrArg (s.block (lastIndex hr)) he).trans heb)) he

theorem representativeScan_vertices_card (s : ParallelState π r) (hr : 0 < r)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted) :
    ((s.representativeScan hr).eval G.toWeighted.cut).vertices.card =
      ((s.representativeScan hr).eval G.toWeighted.cut).selected.length := by
  rw [RepresentativeScan.vertices,
    List.toFinset_card_of_nodup (s.representativeScan_vertices_nodup hr G hs), List.length_map]

theorem representativeScan_vertices_bounds (s : ParallelState π r) (hr : 0 < r)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted) :
    let out := (s.representativeScan hr).eval G.toWeighted.cut
    (out.state.liveBlocks (lastIndex hr)).card ≤ out.vertices.card ∧
      out.vertices.card ≤ (s.liveBlocks (lastIndex hr)).card := by
  dsimp only
  rw [s.representativeScan_vertices_card hr G hs]
  refine ⟨s.representativeScan_covers_live hr G hs, ?_⟩
  have hh := (s.scanBlocks_labels_sublist hr (s.liveBlocks (lastIndex hr)).toList
    G.toWeighted.cut).length_le
  simpa only [representativeScan, DTree.eval_cast, List.length_map, Finset.length_toList] using hh

/-- The actual scan establishes the exact hypotheses used by the public
fair batch on its returned state and returned original representatives. -/
theorem representativeScan_for_batch (s : ParallelState π r) (hr : 0 < r) (hl : s.Laminar)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (hi : s.InactiveSound hr G.toWeighted) :
    let out := (s.representativeScan hr).eval G.toWeighted.cut
    out.state.Laminar ∧ out.state.usedGraph.IsSubgraph G.toWeighted ∧
      out.state.InactiveSound hr G.toWeighted ∧ out.state.livePotential ≤ s.livePotential ∧
      (∀ u ∈ out.vertices, ∀ v ∈ out.vertices, u ≠ v →
        ¬(out.state.forests (lastIndex hr)).quotient.Reachable (π.map u) (π.map v)) ∧
      (∀ u ∈ out.vertices, ∃ v,
        ¬(out.state.forests (lastIndex hr)).quotient.Reachable (π.map u) (π.map v) ∧
          0 < (G.toWeighted.subtract out.state.usedGraph).w u v) := by
  let out := (s.representativeScan hr).eval G.toWeighted.cut
  have hf : out.state.forests = s.forests := by
    dsimp only [out]
    rw [representativeScan, DTree.eval_cast]
    exact s.scanBlocks_forests hr (s.liveBlocks (lastIndex hr)).toList G.toWeighted.cut
  have hin : s.inactive ⊆ out.state.inactive := by
    dsimp only [out]
    rw [representativeScan, DTree.eval_cast]
    exact s.scanBlocks_inactive hr (s.liveBlocks (lastIndex hr)).toList G.toWeighted.cut
  have hused : out.state.usedGraph = s.usedGraph := by simp only [usedGraph, hf]
  have hg := s.representativeScan_good hr G hs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change out.state.Laminar
    simpa only [Laminar, hf] using hl
  · change out.state.usedGraph.IsSubgraph G.toWeighted
    simpa only [hused] using hs
  · change out.state.InactiveSound hr G.toWeighted
    dsimp only [out]
    rw [representativeScan, DTree.eval_cast]
    exact s.scanBlocks_inactiveSound hr (s.liveBlocks (lastIndex hr)).toList G hs hi
  · apply Finset.sum_le_sum
    intro i hi
    exact s.liveBlocks_card_mono_of out.state i hin (fun u v h => by simpa only [hf] using h)
  · intro u hu v hv hne
    obtain ⟨a, ha, hau⟩ := List.mem_map.mp (List.mem_toFinset.mp hu)
    obtain ⟨b, hb, hbv⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    have hab : a.1 ≠ b.1 := by
      intro he
      have hab := List.inj_on_of_nodup_map
        (s.representativeScan_distinct_labels hr G.toWeighted.cut) ha hb he
      exact hne (hau.symm.trans ((congrArg Prod.snd hab).trans hbv))
    have hh := s.representativeScan_separated hr G hs ha hb hab
    change ¬(out.state.forests (lastIndex hr)).quotient.Reachable (π.map u) (π.map v)
    simpa only [hf, hau, hbv] using hh
  · intro u hu
    obtain ⟨a, ha, hau⟩ := List.mem_map.mp (List.mem_toFinset.mp hu)
    have hp := (hg.2.1 a ha).2.2
    obtain ⟨w, hw, v, hv, hpv⟩ := ((G.toWeighted.subtract s.usedGraph).cross_pos_iff _ _).mp hp
    have hw' : w = a.2 := Finset.mem_singleton.mp hw
    subst w
    refine ⟨v, ?_, ?_⟩
    · have hnv := Finset.mem_compl.mp hv
      change ¬(out.state.forests (lastIndex hr)).quotient.Reachable (π.map u) (π.map v)
      simpa only [hf, mem_lastBlock, hau] using hnv
    · change 0 < (G.toWeighted.subtract out.state.usedGraph).w u v
      simpa only [hused, hau] using hpv

def scanFairRoundBudget (V Q : Type) [Fintype V] [Fintype Q] (T : ℕ) : ℕ :=
  3 * Fintype.card V * Fintype.card Q + fairBatchBudget V T

/-- The full actual representative scan followed by the independently
randomized fair batch. Its only inputs are the public state, r>0, and fuel. -/
def scanFairRound (s : ParallelState π r) (hr : 0 < r) (T : ℕ) :
    RTree (Finset V) ℝ (Option (ParallelState π r)) (scanFairRoundBudget V Q T) :=
  ((RTree.ofDeterministic (s.representativeScan hr)).weaken
    (Nat.mul_le_mul_left (3 * Fintype.card V) (s.liveBlocks_card_le (lastIndex hr)))).bind
      (fun out => out.state.fairBatch hr out.vertices T)

theorem scanFairRound_eval (s : ParallelState π r) (hr : 0 < r) (T : ℕ)
    (read : Finset V → ℝ) :
    (s.scanFairRound hr T).eval read =
      let out := (s.representativeScan hr).eval read
      (out.state.fairBatch hr out.vertices T).eval read := by
  dsimp only [scanFairRound, scanFairRoundBudget]
  simp only [RTree.eval_bind, RTree.eval_weaken,
    RTree.eval_ofDeterministic, PMF.pure_bind]

/-- Both discovery and recovery hypotheses are discharged by the actual
program. The count is that of the actual representatives retained by the
scan; stopping a halving phase after a large retirement uses a separate
stopped-potential argument, not a false raw-potential decrement claim. -/
theorem scanFairRound_potential (s : ParallelState π r) (hr : 0 < r) (hl : s.Laminar)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (hi : s.InactiveSound hr G.toWeighted) (T : ℕ) :
    CutQueryComplexity.Probability.expect ((s.scanFairRound hr T).eval G.toWeighted.cut)
      (fun out => (resultPotential out : ℝ≥0∞)) +
      (((s.representativeScan hr).eval G.toWeighted.cut).vertices.card : ℝ≥0∞) / 4 ≤
        (s.livePotential : ℝ≥0∞) := by
  let out := (s.representativeScan hr).eval G.toWeighted.cut
  obtain ⟨htl, hts, hti, hpot, hsep, hpositive⟩ := s.representativeScan_for_batch hr hl G hs hi
  rw [s.scanFairRound_eval hr T G.toWeighted.cut]
  apply (out.state.fairBatch_potential hr htl G hts hti out.vertices T hsep hpositive).trans
  exact_mod_cast hpot

def phaseActive (hr : 0 < r) (scale : ℕ) : Option (ParallelState π r) → Prop
  | none => False
  | some s => scale / 2 < (s.liveBlocks (lastIndex hr)).card

/-- Potential is stopped when the actual public component count is halved.
An explicit recovery failure stays failure and also has stopped potential 0. -/
def phasePotential (hr : 0 < r) (scale : ℕ) (out : Option (ParallelState π r)) : ℕ :=
  if phaseActive hr scale out then resultPotential out else 0

theorem phasePotential_le (hr : 0 < r) (scale : ℕ)
    (out : Option (ParallelState π r)) :
    phasePotential hr scale out ≤ resultPotential out := by
  unfold phasePotential
  split <;> omega

/-- An actual halving round stops before recovery when the representative
scan itself has already halved the live components. Thus isolated-component
retirements are not incorrectly treated as raw potential drift. -/
def halvingRound (s : ParallelState π r) (hr : 0 < r) (scale T : ℕ) :
    RTree (Finset V) ℝ (Option (ParallelState π r)) (scanFairRoundBudget V Q T) :=
  if scale / 2 < (s.liveBlocks (lastIndex hr)).card then
    ((RTree.ofDeterministic (s.representativeScan hr)).weaken
      (Nat.mul_le_mul_left (3 * Fintype.card V) (s.liveBlocks_card_le (lastIndex hr)))).bind
        (fun out => if scale / 2 < (out.state.liveBlocks (lastIndex hr)).card then
          out.state.fairBatch hr out.vertices T else RTree.pure (PMF.pure (some out.state)))
  else RTree.pure (PMF.pure (some s))

theorem halvingRound_eval (s : ParallelState π r) (hr : 0 < r) (scale T : ℕ)
    (read : Finset V → ℝ) :
    (s.halvingRound hr scale T).eval read =
      if scale / 2 < (s.liveBlocks (lastIndex hr)).card then
        let out := (s.representativeScan hr).eval read
        if scale / 2 < (out.state.liveBlocks (lastIndex hr)).card then
          (out.state.fairBatch hr out.vertices T).eval read else PMF.pure (some out.state)
      else PMF.pure (some s) := by
  dsimp only [halvingRound, scanFairRoundBudget]
  by_cases ha : scale / 2 < (s.liveBlocks (lastIndex hr)).card
  · simp only [if_pos ha, RTree.eval_bind, RTree.eval_weaken,
      RTree.eval_ofDeterministic, PMF.pure_bind]
    by_cases hb : scale / 2 <
        (((s.representativeScan hr).eval read).state.liveBlocks (lastIndex hr)).card
    · simp only [if_pos hb]
    · simp only [if_neg hb, RTree.eval_pure]
  · simp only [if_neg ha, RTree.eval_pure]

theorem halvingRound_success (s : ParallelState π r) (hr : 0 < r) (hl : s.Laminar)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (hi : s.InactiveSound hr G.toWeighted) (scale T : ℕ) {t : ParallelState π r}
    (ht : some t ∈ ((s.halvingRound hr scale T).eval G.toWeighted.cut).support) :
    t.Laminar ∧ t.usedGraph.IsSubgraph G.toWeighted ∧
      t.InactiveSound hr G.toWeighted ∧ t.livePotential ≤ s.livePotential ∧
      (∀ i, (t.liveBlocks i).card ≤ (s.liveBlocks i).card) := by
  rw [s.halvingRound_eval hr scale T G.toWeighted.cut] at ht
  by_cases ha : scale / 2 < (s.liveBlocks (lastIndex hr)).card
  · rw [if_pos ha] at ht
    let out := (s.representativeScan hr).eval G.toWeighted.cut
    obtain ⟨htl, hts, hti, hpot, hsep, hpositive⟩ := s.representativeScan_for_batch hr hl G hs hi
    have hscan : ∀ i, (out.state.liveBlocks i).card ≤ (s.liveBlocks i).card := by
      intro i
      apply s.liveBlocks_card_mono_of out.state i
      · dsimp only [out]
        rw [representativeScan, DTree.eval_cast]
        exact s.scanBlocks_inactive hr (s.liveBlocks (lastIndex hr)).toList G.toWeighted.cut
      · intro u v huv
        have hf : out.state.forests = s.forests := by
          dsimp only [out]
          rw [representativeScan, DTree.eval_cast]
          exact s.scanBlocks_forests hr (s.liveBlocks (lastIndex hr)).toList G.toWeighted.cut
        simpa only [hf] using huv
    by_cases hb : scale / 2 < (out.state.liveBlocks (lastIndex hr)).card
    · rw [if_pos hb] at ht
      have hg := out.state.fairBatch_success hr htl G hts hti out.vertices T hsep ht
      exact ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1.trans hpot,
        fun i => (hg.2.2.2.2 i).trans (hscan i)⟩
    · rw [if_neg hb] at ht
      have he : t = out.state := Option.some.inj ((PMF.mem_support_pure_iff _ _).mp ht)
      subst t
      exact ⟨htl, hts, hti, hpot, hscan⟩
  · rw [if_neg ha] at ht
    have he : t = s := Option.some.inj ((PMF.mem_support_pure_iff _ _).mp ht)
    subst t
    exact ⟨hl, hs, hi, le_rfl, fun _ => le_rfl⟩

/-- A genuine one-round drift estimate for the implemented public program.
Every discovery, degree, neighbor and merge premise is discharged internally.
The two stopping cases use zero stopped potential; explicit failure is not
reinterpreted as a successful certificate. -/
theorem halvingRound_potential (s : ParallelState π r) (hr : 0 < r) (hl : s.Laminar)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (hi : s.InactiveSound hr G.toWeighted) (scale T : ℕ) :
    CutQueryComplexity.Probability.expect ((s.halvingRound hr scale T).eval G.toWeighted.cut)
      (fun out => (phasePotential hr scale out : ℝ≥0∞)) +
      (scale : ℝ≥0∞) / 8 * (if phaseActive hr scale (some s) then 1 else 0) ≤
        (phasePotential hr scale (some s) : ℝ≥0∞) := by
  by_cases ha : scale / 2 < (s.liveBlocks (lastIndex hr)).card
  · have hactive : phaseActive hr scale (some s) := ha
    rw [s.halvingRound_eval hr scale T G.toWeighted.cut, if_pos ha]
    simp only [if_pos hactive, mul_one, phasePotential, if_pos hactive, resultPotential]
    let out := (s.representativeScan hr).eval G.toWeighted.cut
    obtain ⟨htl, hts, hti, hpot, hsep, hpositive⟩ := s.representativeScan_for_batch hr hl G hs hi
    by_cases hb : scale / 2 < (out.state.liveBlocks (lastIndex hr)).card
    · rw [if_pos hb]
      have hraw := out.state.fairBatch_potential hr htl G hts hti out.vertices T hsep hpositive
      have hrep : (out.state.liveBlocks (lastIndex hr)).card ≤ out.vertices.card :=
        (s.representativeScan_vertices_bounds hr G hs).1
      have hscale : scale ≤ 2 * out.vertices.card := by omega
      have hscale' : (scale : ℝ≥0∞) ≤ 2 * (out.vertices.card : ℝ≥0∞) := by
        exact_mod_cast hscale
      have hdelta : (scale : ℝ≥0∞) / 8 ≤ (out.vertices.card : ℝ≥0∞) / 4 := by
        calc
          _ ≤ (2 * (out.vertices.card : ℝ≥0∞)) / 8 := ENNReal.div_le_div_right hscale' 8
          _ = _ := by
            have he : (8 : ℝ≥0∞) = 2 * 4 := by norm_num
            rw [he]
            exact ENNReal.mul_div_mul_left _ _ (by norm_num) (by simp)
      have hstopped : CutQueryComplexity.Probability.expect
          ((out.state.fairBatch hr out.vertices T).eval G.toWeighted.cut)
          (fun x => (phasePotential hr scale x : ℝ≥0∞)) ≤
          CutQueryComplexity.Probability.expect
            ((out.state.fairBatch hr out.vertices T).eval G.toWeighted.cut)
            (fun x => (resultPotential x : ℝ≥0∞)) := by
        apply CutQueryComplexity.Probability.expect_mono_on_support
        intro x hx
        exact_mod_cast phasePotential_le hr scale x
      have hh := (add_le_add hstopped hdelta).trans hraw
      exact hh.trans (by exact_mod_cast hpot)
    · rw [if_neg hb, CutQueryComplexity.Probability.expect_pure]
      have hstop : ¬phaseActive hr scale (some out.state) := hb
      change (phasePotential hr scale (some out.state) : ℝ≥0∞) +
        (scale : ℝ≥0∞) / 8 ≤ (s.livePotential : ℝ≥0∞)
      simp only [phasePotential, if_neg hstop, Nat.cast_zero, zero_add]
      have hcard : (s.liveBlocks (lastIndex hr)).card ≤ s.livePotential := by
        change (s.liveBlocks (lastIndex hr)).card ≤ ∑ i : Fin r, (s.liveBlocks i).card
        exact Finset.single_le_sum (fun i _ => Nat.zero_le ((s.liveBlocks i).card))
          (Finset.mem_univ (lastIndex hr))
      have hscale : scale ≤ s.livePotential * 8 := by omega
      have hscale' : (scale : ℝ≥0∞) ≤ (s.livePotential : ℝ≥0∞) * 8 := by
        exact_mod_cast hscale
      calc
        _ ≤ ((s.livePotential : ℝ≥0∞) * 8) / 8 := ENNReal.div_le_div_right hscale' 8
        _ = _ := ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)
  · have hactive : ¬phaseActive hr scale (some s) := ha
    rw [s.halvingRound_eval hr scale T G.toWeighted.cut, if_neg ha,
      CutQueryComplexity.Probability.expect_pure]
    simp only [phasePotential, if_neg hactive, Nat.cast_zero, mul_zero, zero_add, le_refl]

/-- Charge a real original cut exactly when another halving round is
executed. Terminal states, including explicit failure, are absorbing. -/
def halvingStep (hr : 0 < r) (scale T : ℕ) : Option (ParallelState π r) →
    RTree (Finset V) ℝ (Option (ParallelState π r)) (scanFairRoundBudget V Q T + 1)
  | none => RTree.pure (PMF.pure none)
  | some s => if phaseActive hr scale (some s) then
      chargeRound (s.halvingRound hr scale T) else RTree.pure (PMF.pure (some s))

theorem halvingStep_absorbs (hr : 0 < r) (scale T : ℕ)
    (out : Option (ParallelState π r)) (ha : ¬phaseActive hr scale out)
    (read : Finset V → ℝ) :
    (halvingStep hr scale T out).eval read = PMF.pure out := by
  cases out with
  | none => exact RTree.eval_pure _ _
  | some s => simp only [halvingStep, if_neg ha, RTree.eval_pure]

theorem halvingStep_positive (hr : 0 < r) (scale T : ℕ)
    (out : Option (ParallelState π r)) (ha : phaseActive hr scale out)
    (read : Finset V → ℝ) {answer : Option (ParallelState π r) × ℕ}
    (hanswer : answer ∈ (RTree.run read (halvingStep hr scale T out)).support) :
    1 ≤ answer.2 := by
  cases out with
  | none => cases ha
  | some s =>
      rw [halvingStep, if_pos ha] at hanswer
      exact chargeRound_positive _ read hanswer

/-- The invariant is a proof-side assertion about the implemented state.
It is not an input to any constructor, color, recovery, or query choice. -/
def HonestResult (hr : 0 < r) (G : SimpleInput V) : Option (ParallelState π r) → Prop
  | none => True
  | some s => s.Laminar ∧ s.usedGraph.IsSubgraph G.toWeighted ∧ s.InactiveSound hr G.toWeighted

theorem halvingStep_honest (hr : 0 < r) (scale T : ℕ) (G : SimpleInput V)
    (out : Option (ParallelState π r)) (ho : HonestResult hr G out)
    {answer : Option (ParallelState π r)}
    (ha : answer ∈ ((halvingStep hr scale T out).eval G.toWeighted.cut).support) :
    HonestResult hr G answer := by
  cases out with
  | none =>
      have he : answer = none := by
        simpa only [halvingStep, RTree.eval_pure, PMF.mem_support_pure_iff] using ha
      rw [he]
      trivial
  | some s =>
      by_cases hactive : phaseActive hr scale (some s)
      · rw [halvingStep, if_pos hactive, chargeRound_eval] at ha
        cases answer with
        | none => trivial
        | some t =>
            have hh := s.halvingRound_success hr ho.1 G ho.2.1 ho.2.2 scale T ha
            exact ⟨hh.1, hh.2.1, hh.2.2.1⟩
      · rw [halvingStep_absorbs hr scale T (some s) hactive G.toWeighted.cut] at ha
        have he := (PMF.mem_support_pure_iff _ _).mp ha
        simpa only [he] using ho

theorem halvingStep_potential (hr : 0 < r) (scale T : ℕ) (G : SimpleInput V)
    (out : Option (ParallelState π r)) (ho : HonestResult hr G out) :
    CutQueryComplexity.Probability.expect
      ((halvingStep hr scale T out).eval G.toWeighted.cut)
      (fun answer => (phasePotential hr scale answer : ℝ≥0∞)) +
      (scale : ℝ≥0∞) / 8 * (if phaseActive hr scale out then 1 else 0) ≤
        (phasePotential hr scale out : ℝ≥0∞) := by
  cases out with
  | none =>
      simp [halvingStep, RTree.eval_pure, CutQueryComplexity.Probability.expect_pure,
        phaseActive, phasePotential]
  | some s =>
      by_cases ha : phaseActive hr scale (some s)
      · rw [halvingStep, if_pos ha, chargeRound_eval]
        exact s.halvingRound_potential hr ho.1 G ho.2.1 ho.2.2 scale T
      · rw [halvingStep_absorbs hr scale T (some s) ha G.toWeighted.cut,
          CutQueryComplexity.Probability.expect_pure]
        simp only [if_neg ha, mul_zero, add_zero, le_refl]

/-- A finite actual query program. Its counter bounds construction, while
stopped states spend zero additional queries; every active round is padded. -/
def halvingIterations (hr : 0 < r) (scale T : ℕ) : (horizon : ℕ) →
    Option (ParallelState π r) →
      RTree (Finset V) ℝ (Option (ParallelState π r))
        (horizon * (scanFairRoundBudget V Q T + 1))
  | 0, out => RTree.pure (PMF.pure out)
  | horizon + 1, out =>
      ((halvingStep hr scale T out).bind (halvingIterations hr scale T horizon)).cast
        (by rw [Nat.succ_mul]; omega)

theorem halvingIterations_eval (hr : 0 < r) (scale T horizon : ℕ)
    (out : Option (ParallelState π r)) (read : Finset V → ℝ) :
    (halvingIterations hr scale T horizon out).eval read =
      FiniteProgress.steps (fun x => (halvingStep hr scale T x).eval read) horizon out := by
  induction horizon generalizing out with
  | zero => simp only [halvingIterations, RTree.eval_pure, FiniteProgress.steps]
  | succ horizon ih =>
      simp only [halvingIterations, RTree.eval_cast, RTree.eval_bind, FiniteProgress.steps, ih]

/-- Finite telescoping for the actual scan/recovery/update program. The
invariant and drift are discharged by its concrete support and one-round
proofs, rather than accepted as phase hypotheses. -/
theorem halvingIterations_potential_visits (hr : 0 < r) (scale T horizon : ℕ)
    (G : SimpleInput V) (out : Option (ParallelState π r)) (ho : HonestResult hr G out) :
    CutQueryComplexity.Probability.expect
      ((halvingIterations hr scale T horizon out).eval G.toWeighted.cut)
      (fun answer => (phasePotential hr scale answer : ℝ≥0∞)) +
      (scale : ℝ≥0∞) / 8 * FiniteProgress.activeVisits
        (fun x => (halvingStep hr scale T x).eval G.toWeighted.cut)
        (phaseActive hr scale) horizon out ≤ (phasePotential hr scale out : ℝ≥0∞) := by
  induction horizon generalizing out with
  | zero =>
      simp only [halvingIterations, RTree.eval_pure,
        CutQueryComplexity.Probability.expect_pure, FiniteProgress.activeVisits,
        mul_zero, add_zero, le_refl]
  | succ horizon ih =>
      let next := fun x : Option (ParallelState π r) => (halvingStep hr scale T x).eval G.toWeighted.cut
      let pot := fun x : Option (ParallelState π r) => (phasePotential hr scale x : ℝ≥0∞)
      let visits := FiniteProgress.activeVisits next (phaseActive hr scale) horizon
      have hh : CutQueryComplexity.Probability.expect (next out)
          (fun x => CutQueryComplexity.Probability.expect
            ((halvingIterations hr scale T horizon x).eval G.toWeighted.cut) pot +
              (scale : ℝ≥0∞) / 8 * visits x) ≤
          CutQueryComplexity.Probability.expect (next out) pot := by
        apply CutQueryComplexity.Probability.expect_mono_on_support
        intro x hx
        exact ih x (halvingStep_honest hr scale T G out ho hx)
      rw [CutQueryComplexity.Probability.expect_add,
        CutQueryComplexity.Probability.expect_const_mul] at hh
      calc
        _ = (CutQueryComplexity.Probability.expect (next out)
              (fun x => CutQueryComplexity.Probability.expect
                ((halvingIterations hr scale T horizon x).eval G.toWeighted.cut) pot) +
                (scale : ℝ≥0∞) / 8 * CutQueryComplexity.Probability.expect (next out) visits) +
              (scale : ℝ≥0∞) / 8 * (if phaseActive hr scale out then 1 else 0) := by
          simp only [halvingIterations, RTree.eval_cast, RTree.eval_bind,
            CutQueryComplexity.Probability.expect_bind, FiniteProgress.activeVisits, mul_add]
          ac_rfl
        _ ≤ CutQueryComplexity.Probability.expect (next out) pot +
              (scale : ℝ≥0∞) / 8 * (if phaseActive hr scale out then 1 else 0) :=
          add_le_add hh le_rfl
        _ ≤ _ := halvingStep_potential hr scale T G out ho

/-- Uniformly over the finite construction horizon and inner recovery fuel,
an actual halving phase executes at most 8r active rounds in expectation. -/
theorem halvingIterations_visits_le (s : ParallelState π r) (hr : 0 < r)
    (hl : s.Laminar) (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (hi : s.InactiveSound hr G.toWeighted) (scale T horizon : ℕ) (hscale : 0 < scale)
    (hcount : (s.liveBlocks (lastIndex hr)).card ≤ scale) :
    FiniteProgress.activeVisits
      (fun x => (halvingStep hr scale T x).eval G.toWeighted.cut)
      (phaseActive hr scale) horizon (some s) ≤ 8 * (r : ℝ≥0∞) := by
  have hh := halvingIterations_potential_visits hr scale T horizon G (some s) ⟨hl, hs, hi⟩
  have hpot : phasePotential hr scale (some s) ≤ r * scale :=
    (phasePotential_le hr scale (some s)).trans
      ((s.livePotential_le hr hl).trans (Nat.mul_le_mul_left r hcount))
  have hvisit : (scale : ℝ≥0∞) / 8 * FiniteProgress.activeVisits
      (fun x => (halvingStep hr scale T x).eval G.toWeighted.cut)
      (phaseActive hr scale) horizon (some s) ≤ (r : ℝ≥0∞) * scale := by
    exact (le_add_of_nonneg_left (show (0 : ℝ≥0∞) ≤ _ from bot_le)).trans
      (hh.trans (by exact_mod_cast hpot))
  have hz : (scale : ℝ≥0∞) / 8 ≠ 0 := by
    exact (ENNReal.div_pos (by exact_mod_cast Nat.ne_of_gt hscale) (by norm_num)).ne'
  have htop : (scale : ℝ≥0∞) / 8 ≠ ∞ := by finiteness
  apply (ENNReal.mul_le_mul_iff_right hz htop).mp
  calc
    _ ≤ (r : ℝ≥0∞) * scale := hvisit
    _ = (scale : ℝ≥0∞) / 8 * (8 * (r : ℝ≥0∞)) := by
      rw [← mul_assoc, ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
      exact mul_comm _ _

/-- A failed actual halving round must contain a failed finite B call. Both
the scan and the successful halving stop add only nonnegative actual cost. -/
theorem halvingRound_none_cost (s : ParallelState π r) (hr : 0 < r) (hl : s.Laminar)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (hi : s.InactiveSound hr G.toWeighted) (scale T cost : ℕ)
    (hout : (none, cost) ∈ (RTree.run G.toWeighted.cut (s.halvingRound hr scale T)).support) :
    3 * T ≤ cost := by
  dsimp only [halvingRound, scanFairRoundBudget] at hout
  by_cases ha : scale / 2 < (s.liveBlocks (lastIndex hr)).card
  · rw [if_pos ha, RTree.run_bind] at hout
    obtain ⟨⟨scan, c⟩, hfirst, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    rw [RTree.run_weaken, RTree.run_ofDeterministic] at hfirst
    have hscan := (PMF.mem_support_pure_iff _ _).mp hfirst
    have hscan' : scan = (s.representativeScan hr).eval G.toWeighted.cut :=
      congrArg Prod.fst hscan
    obtain ⟨⟨result, d⟩, hresult, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
    have heResult : result = none := congrArg Prod.fst he
    have heCost : c + d = cost := congrArg Prod.snd he
    by_cases hb : scale / 2 < (scan.state.liveBlocks (lastIndex hr)).card
    · rw [if_pos hb] at hresult
      rw [hscan', heResult] at hresult
      obtain ⟨htl, hts, hti, hpot, hsep, hpositive⟩ := s.representativeScan_for_batch hr hl G hs hi
      have hc := ((s.representativeScan hr).eval G.toWeighted.cut).state.fairBatch_none_cost
        hr htl G hts hti _ T d hsep hresult
      omega
    · rw [if_neg hb, RTree.run_pure, PMF.pure_map] at hresult
      have hres := (PMF.mem_support_pure_iff _ _).mp hresult
      have hn := congrArg Prod.fst hres
      rw [heResult] at hn
      cases hn
  · rw [if_neg ha, RTree.run_pure, PMF.pure_map] at hout
    have hres := (PMF.mem_support_pure_iff _ _).mp hout
    have hn := congrArg Prod.fst hres
    cases hn

theorem halvingStep_none_cost (s : ParallelState π r) (hr : 0 < r) (hl : s.Laminar)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (hi : s.InactiveSound hr G.toWeighted) (scale T cost : ℕ)
    (hout : (none, cost) ∈
      (RTree.run G.toWeighted.cut (halvingStep hr scale T (some s))).support) :
    3 * T ≤ cost := by
  by_cases ha : phaseActive hr scale (some s)
  · rw [halvingStep, if_pos ha, chargeRound_run] at hout
    obtain ⟨⟨result, c⟩, hrun, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
    have hn : result = none := congrArg Prod.fst he
    have hc : c + 1 = cost := congrArg Prod.snd he
    rw [hn] at hrun
    have hcost := s.halvingRound_none_cost hr hl G hs hi scale T c hrun
    omega
  · rw [halvingStep, if_neg ha, RTree.run_pure, PMF.pure_map] at hout
    have hres := (PMF.mem_support_pure_iff _ _).mp hout
    have hn := congrArg Prod.fst hres
    cases hn

theorem halvingStep_active_back (hr : 0 < r) (scale T : ℕ)
    (out answer : Option (ParallelState π r)) (read : Finset V → ℝ)
    (hanswer : answer ∈ ((halvingStep hr scale T out).eval read).support)
    (ha : phaseActive hr scale answer) : phaseActive hr scale out := by
  by_contra ho
  rw [halvingStep_absorbs hr scale T out ho read] at hanswer
  have he : answer = out := (PMF.mem_support_pure_iff _ _).mp hanswer
  exact ho (he ▸ ha)

/-- Active exhaustion of the actual finite phase has paid for every one
of its rounds, for every oracle. It cannot add an uncharged failure event. -/
theorem halvingIterations_active_cost (hr : 0 < r) (scale T horizon : ℕ)
    (out : Option (ParallelState π r)) (read : Finset V → ℝ)
    {answer : Option (ParallelState π r) × ℕ}
    (hanswer : answer ∈ (RTree.run read (halvingIterations hr scale T horizon out)).support)
    (ha : phaseActive hr scale answer.1) : horizon ≤ answer.2 := by
  induction horizon generalizing out answer with
  | zero => exact Nat.zero_le _
  | succ horizon ih =>
      rw [halvingIterations, RTree.run_cast, RTree.run_bind] at hanswer
      obtain ⟨⟨first, c⟩, hfirst, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hanswer
      obtain ⟨⟨last, d⟩, hlast, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
      have heLast : last = answer.1 := congrArg Prod.fst he
      have heCost : c + d = answer.2 := congrArg Prod.snd he
      have hlastActive : phaseActive hr scale last := heLast.symm ▸ ha
      have hlastEval : last ∈ ((halvingIterations hr scale T horizon first).eval read).support := by
        rw [RTree.eval]
        exact (PMF.mem_support_map_iff _ _ _).mpr ⟨(last, d), hlast, rfl⟩
      rw [halvingIterations_eval] at hlastEval
      have hfirstActive := FiniteProgress.steps_active_back
        (fun x => (halvingStep hr scale T x).eval read) (phaseActive hr scale)
        (fun s t ht => halvingStep_active_back hr scale T s t read ht)
        horizon first last hlastEval hlastActive
      have hfirstEval : first ∈ ((halvingStep hr scale T out).eval read).support := by
        rw [RTree.eval]
        exact (PMF.mem_support_map_iff _ _ _).mpr ⟨(first, c), hfirst, rfl⟩
      have houtActive := halvingStep_active_back hr scale T out first read hfirstEval hfirstActive
      have hc := halvingStep_positive hr scale T out houtActive read hfirst
      have hd := ih first hlast hlastActive
      omega

theorem halvingIterations_honest (hr : 0 < r) (scale T horizon : ℕ)
    (G : SimpleInput V) (out : Option (ParallelState π r)) (ho : HonestResult hr G out)
    {answer : Option (ParallelState π r)}
    (ha : answer ∈ ((halvingIterations hr scale T horizon out).eval G.toWeighted.cut).support) :
    HonestResult hr G answer := by
  induction horizon generalizing out with
  | zero =>
      have he : answer = out := by
        simpa only [halvingIterations, RTree.eval_pure, PMF.mem_support_pure_iff] using ha
      simpa only [he] using ho
  | succ horizon ih =>
      rw [halvingIterations, RTree.eval_cast, RTree.eval_bind] at ha
      obtain ⟨first, hfirst, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp ha
      exact ih first (halvingStep_honest hr scale T G out ho hfirst) hrest

/-- Propagate the actual finite-recovery failure cost through the entire
phase. Stopped failures cost zero later, but retain their earlier 3T queries. -/
theorem halvingIterations_none_cost (s : ParallelState π r) (hr : 0 < r) (hl : s.Laminar)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (hi : s.InactiveSound hr G.toWeighted) (scale T horizon cost : ℕ)
    (hout : (none, cost) ∈
      (RTree.run G.toWeighted.cut (halvingIterations hr scale T horizon (some s))).support) :
    3 * T ≤ cost := by
  induction horizon generalizing s cost with
  | zero =>
      have he : (none, cost) = (some s, 0) := by
        simpa only [halvingIterations, RTree.run_pure, PMF.pure_map, PMF.mem_support_pure_iff]
          using hout
      have hn := congrArg Prod.fst he
      cases hn
  | succ horizon ih =>
      rw [halvingIterations, RTree.run_cast, RTree.run_bind] at hout
      obtain ⟨⟨first, c⟩, hfirst, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
      obtain ⟨⟨last, d⟩, hlast, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
      have heLast : last = none := congrArg Prod.fst he
      have heCost : c + d = cost := congrArg Prod.snd he
      rw [heLast] at hlast
      cases first with
      | none =>
          have hc := s.halvingStep_none_cost hr hl G hs hi scale T c hfirst
          omega
      | some t =>
          have heval : some t ∈ ((halvingStep hr scale T (some s)).eval G.toWeighted.cut).support := by
            rw [RTree.eval]
            exact (PMF.mem_support_map_iff _ _ _).mpr ⟨(some t, c), hfirst, rfl⟩
          have ht := halvingStep_honest hr scale T G (some s) ⟨hl, hs, hi⟩ heval
          have hd := ih t ht.1 ht.2.1 ht.2.2 d hlast
          omega

/-- Public finite phase. Both internal recovery fuel and the round horizon
are tied to the eventual original-query cap. An unhalved output is explicit
failure, with the active-exhaustion cost proved below. -/
def halvingPhase (s : ParallelState π r) (hr : 0 < r) (scale cap : ℕ) :
    RTree (Finset V) ℝ (Option (ParallelState π r))
      ((cap + 1) * (scanFairRoundBudget V Q (cap + 1) + 1)) :=
  (halvingIterations hr scale (cap + 1) (cap + 1) (some s)).map fun out =>
    if phaseActive hr scale out then none else out

theorem halvingPhase_success (s : ParallelState π r) (hr : 0 < r) (hl : s.Laminar)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (hi : s.InactiveSound hr G.toWeighted) (scale cap : ℕ) {t : ParallelState π r}
    (ht : some t ∈ ((s.halvingPhase hr scale cap).eval G.toWeighted.cut).support) :
    t.Laminar ∧ t.usedGraph.IsSubgraph G.toWeighted ∧
      t.InactiveSound hr G.toWeighted ∧ (t.liveBlocks (lastIndex hr)).card ≤ scale / 2 := by
  rw [halvingPhase, RTree.eval_map] at ht
  obtain ⟨out, hout, he⟩ := (PMF.mem_support_map_iff _ _ _).mp ht
  by_cases ha : phaseActive hr scale out
  · rw [if_pos ha] at he
    cases he
  · rw [if_neg ha] at he
    subst out
    have hg := halvingIterations_honest hr scale (cap + 1) (cap + 1) G (some s) ⟨hl, hs, hi⟩ hout
    exact ⟨hg.1, hg.2.1, hg.2.2, Nat.le_of_not_gt ha⟩

/-- For the actual honest input, neither finite B exhaustion nor finite
phase exhaustion can report failure beneath the chosen original-query cap. -/
theorem halvingPhase_none_cost (s : ParallelState π r) (hr : 0 < r) (hl : s.Laminar)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (hi : s.InactiveSound hr G.toWeighted) (scale cap cost : ℕ)
    (hout : (none, cost) ∈ (RTree.run G.toWeighted.cut (s.halvingPhase hr scale cap)).support) :
    cap < cost := by
  rw [halvingPhase, mapped_run] at hout
  obtain ⟨⟨out, c⟩, hrun, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
  have heOut : (if phaseActive hr scale out then none else out) = none := congrArg Prod.fst he
  have heCost : c = cost := congrArg Prod.snd he
  subst c
  by_cases ha : phaseActive hr scale out
  · have hc := halvingIterations_active_cost hr scale (cap + 1) (cap + 1) (some s)
      G.toWeighted.cut hrun ha
    omega
  · rw [if_neg ha] at heOut
    subst out
    have hc := s.halvingIterations_none_cost hr hl G hs hi scale (cap + 1) (cap + 1) cost hrun
    omega

theorem halvingRound_failed (s : ParallelState π r) (hr : 0 < r) (G : SimpleInput V)
    (hs : s.usedGraph.IsSubgraph G.toWeighted) (scale T : ℕ) {t : ParallelState π r}
    (ht : some t ∈ ((s.halvingRound hr scale T).eval G.toWeighted.cut).support) :
    t.failed = s.failed := by
  rw [s.halvingRound_eval hr scale T G.toWeighted.cut] at ht
  by_cases ha : scale / 2 < (s.liveBlocks (lastIndex hr)).card
  · rw [if_pos ha] at ht
    let out := (s.representativeScan hr).eval G.toWeighted.cut
    have hscan : out.state.failed = s.failed := (s.representativeScan_good hr G hs).1
    by_cases hb : scale / 2 < (out.state.liveBlocks (lastIndex hr)).card
    · rw [if_pos hb] at ht
      exact (out.state.fairBatch_failed hr out.vertices T G.toWeighted.cut ht).trans hscan
    · rw [if_neg hb] at ht
      have he : t = out.state := Option.some.inj ((PMF.mem_support_pure_iff _ _).mp ht)
      simpa only [he] using hscan
  · rw [if_neg ha] at ht
    have he : t = s := Option.some.inj ((PMF.mem_support_pure_iff _ _).mp ht)
    exact congrArg ParallelState.failed he

theorem halvingStep_failed (s : ParallelState π r) (hr : 0 < r) (G : SimpleInput V)
    (hs : s.usedGraph.IsSubgraph G.toWeighted) (scale T : ℕ) {t : ParallelState π r}
    (ht : some t ∈ ((halvingStep hr scale T (some s)).eval G.toWeighted.cut).support) :
    t.failed = s.failed := by
  by_cases ha : phaseActive hr scale (some s)
  · rw [halvingStep, if_pos ha, chargeRound_eval] at ht
    exact s.halvingRound_failed hr G hs scale T ht
  · rw [halvingStep_absorbs hr scale T (some s) ha G.toWeighted.cut] at ht
    have he : t = s := Option.some.inj ((PMF.mem_support_pure_iff _ _).mp ht)
    exact congrArg ParallelState.failed he

theorem halvingIterations_absorbs (hr : 0 < r) (scale T horizon : ℕ)
    (out : Option (ParallelState π r)) (ha : ¬phaseActive hr scale out)
    (read : Finset V → ℝ) :
    (halvingIterations hr scale T horizon out).eval read = PMF.pure out := by
  induction horizon with
  | zero => exact RTree.eval_pure _ _
  | succ horizon ih =>
      rw [halvingIterations, RTree.eval_cast, RTree.eval_bind,
        halvingStep_absorbs hr scale T out ha read, PMF.pure_bind, ih]

theorem halvingIterations_failed (s : ParallelState π r) (hr : 0 < r)
    (hl : s.Laminar) (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (hi : s.InactiveSound hr G.toWeighted) (scale T horizon : ℕ) {t : ParallelState π r}
    (ht : some t ∈
      ((halvingIterations hr scale T horizon (some s)).eval G.toWeighted.cut).support) :
    t.failed = s.failed := by
  induction horizon generalizing s with
  | zero =>
      have he : t = s := by
        simpa only [halvingIterations, RTree.eval_pure, PMF.mem_support_pure_iff,
          Option.some.injEq] using ht
      exact congrArg ParallelState.failed he
  | succ horizon ih =>
      rw [halvingIterations, RTree.eval_cast, RTree.eval_bind] at ht
      obtain ⟨first, hfirst, htail⟩ := (PMF.mem_support_bind_iff _ _ _).mp ht
      cases first with
      | none =>
          rw [halvingIterations_absorbs hr scale T horizon none (by simp only [phaseActive, not_false_eq_true])
            G.toWeighted.cut] at htail
          have he := (PMF.mem_support_pure_iff _ _).mp htail
          cases he
      | some u =>
          have hu := halvingStep_honest hr scale T G (some s) ⟨hl, hs, hi⟩ hfirst
          exact (ih u hu.1 hu.2.1 hu.2.2 htail).trans (s.halvingStep_failed hr G hs scale T hfirst)

/-- Successful phases preserve the explicit false failure flag needed by
the final forest-completion program; finite recovery failure stays `none`. -/
theorem halvingPhase_failed (s : ParallelState π r) (hr : 0 < r)
    (hl : s.Laminar) (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (hi : s.InactiveSound hr G.toWeighted) (scale cap : ℕ) {t : ParallelState π r}
    (ht : some t ∈ ((s.halvingPhase hr scale cap).eval G.toWeighted.cut).support) :
    t.failed = s.failed := by
  rw [halvingPhase, RTree.eval_map] at ht
  obtain ⟨out, hout, he⟩ := (PMF.mem_support_map_iff _ _ _).mp ht
  by_cases ha : phaseActive hr scale out
  · rw [if_pos ha] at he
    cases he
  · rw [if_neg ha] at he
    subst out
    exact s.halvingIterations_failed hr hl G hs hi scale (cap + 1) (cap + 1) hout

end ParallelState

#print axioms ParallelState.representativeScan_vertices_card
#print axioms ParallelState.representativeScan_vertices_bounds
#print axioms ParallelState.representativeScan_for_batch
#print axioms ParallelState.scanFairRound_eval
#print axioms ParallelState.scanFairRound_potential
#print axioms ParallelState.halvingRound_eval
#print axioms ParallelState.halvingRound_success
#print axioms ParallelState.halvingRound_potential
#print axioms ParallelState.halvingStep_absorbs
#print axioms ParallelState.halvingStep_positive
#print axioms ParallelState.halvingStep_honest
#print axioms ParallelState.halvingStep_potential
#print axioms ParallelState.halvingIterations_eval
#print axioms ParallelState.halvingIterations_potential_visits
#print axioms ParallelState.halvingIterations_visits_le
#print axioms ParallelState.halvingRound_none_cost
#print axioms ParallelState.halvingStep_none_cost
#print axioms ParallelState.halvingStep_active_back
#print axioms ParallelState.halvingIterations_active_cost
#print axioms ParallelState.halvingIterations_honest
#print axioms ParallelState.halvingIterations_none_cost
#print axioms ParallelState.halvingPhase_success
#print axioms ParallelState.halvingPhase_none_cost
#print axioms ParallelState.halvingRound_failed
#print axioms ParallelState.halvingStep_failed
#print axioms ParallelState.halvingIterations_absorbs
#print axioms ParallelState.halvingIterations_failed
#print axioms ParallelState.halvingPhase_failed

end
end CutQueryComplexity.StarContraction2022.Certificates
