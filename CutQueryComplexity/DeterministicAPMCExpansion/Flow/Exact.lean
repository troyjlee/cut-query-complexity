import CutQueryComplexity.DeterministicAPMCExpansion.Flow.UnitPhase
import CutQueryComplexity.DeterministicAPMCExpansion.Flow.Scaled

/-!
# Exact scaled two-star flow by executed BFS and unit blocking phases

The public program uses only the scale, terminal capacities and oracle
answers. Its last BFS supplies a minimum source shore. The coarse bound in
this module ensures total execution on every transcript; the sharper tail
analysis will bound the honest execution before the final smaller hard cap
is applied. No maximum-flow existence theorem selects the output.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.Flow

open Finset Certificate DirectedCertificate Prog
open DirectedUnitST.Repair
open DirectedUnitST.Blocking (LevelPath IntegralCap)
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A shortest path for a feasible BFS layering is entirely forward. -/
theorem PathAt.tight {H : WeightedDiGraph (NetworkVertex V)}
    {s v : NetworkVertex V} {d : ℕ} (path : PathAt H s v d)
    (level : NetworkVertex V → ℕ) (hs : level s = 0)
    (hrise : ∀ u v, 0 < H.c u v → level v ≤ level u + 1)
    (htight : level v = d) : LevelPath H level s v d := by
  induction path with
  | nil => exact LevelPath.nil
  | @snoc u v d hp he ih =>
      have hprev := hp.level_le level hs hrise
      have hlast := hrise u v he
      have heq : level u = d := by omega
      have hforward : level v = level u + 1 := by omega
      exact LevelPath.snoc (ih heq) he hforward

structure ExactResult (V : Type) where
  flow : NetworkVertex V → NetworkVertex V → ℝ
  shore : Finset (NetworkVertex V)
  events : List PhaseEvent
  finished : Bool

def exactEmpty (f : NetworkVertex V → NetworkVertex V → ℝ)
    (shore : Finset (NetworkVertex V)) (finished : Bool) : ExactResult V :=
  ⟨f, shore, [], finished⟩

def exactPrepend (distance amount : ℕ) (result : ExactResult V) : ExactResult V :=
  { result with events := ⟨distance, amount⟩ :: result.events }

def exactRun (a z : V → ℕ) : ℕ → (NetworkVertex V → NetworkVertex V → ℝ) →
    Prog (Finset V) ℝ (ExactResult V)
  | 0, f => .pure (exactEmpty f {source} false)
  | fuel + 1, f => (bfsProg a z f source).bind fun data =>
      if sink ∈ data.unseen then .pure (exactEmpty f data.unseenᶜ true) else
        (unitPhaseProg a z (bfsLevel data) f).bind fun phase =>
          if phase.finished then
            (exactRun a z fuel phase.flow).map (exactPrepend (bfsLevel data sink) phase.amount)
          else .pure (exactEmpty phase.flow {source} false)

def exactFuel (a : V → ℕ) : ℕ := (∑ v, a v) + 1

def exactProg (a z : V → ℕ) : Prog (Finset V) ℝ (ExactResult V) :=
  exactRun a z (exactFuel a) (fun _ _ => 0)

def scaledExactProg (C : ℕ) (a z : V → ℕ) : Prog (Finset V) ℝ (ExactResult V) :=
  scaleAnswers C (exactProg a z)

structure ExactCertificate (H : WeightedDiGraph (NetworkVertex V))
    (result : ExactResult V) : Prop where
  feasible : H.STFlow source sink result.flow
  integral : IntegralCap (residual H result.flow feasible.1)
  source_mem : source ∈ result.shore
  sink_notMem : sink ∉ result.shore
  residual_zero : (residual H result.flow feasible.1).out result.shore = 0
  finished : result.finished = true

theorem exactRun_correct (G : WeightedGraph V) (a z : V → ℕ) (fuel : ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ)
    (hf : (directed (twoStar G a z)).STFlow source sink f)
    (hint : IntegralCap (residualNetwork G a z f hf.1))
    (hstart : 0 ≤ netOut f source)
    (hfuel : ((∑ v, a v : ℕ) : ℝ) < netOut f source + (fuel : ℝ)) :
    ExactCertificate (directed (twoStar G a z)) ((exactRun a z fuel f).eval G.cut) := by
  induction fuel generalizing f with
  | zero =>
      have hcap := netOut_le_source_capacity G a z f hf.1
      simp only [Nat.cast_zero, add_zero] at hfuel
      linarith
  | succ fuel ih =>
      let data := (bfsProg a z f source).eval G.cut
      have hbi := bfsProg_invariant G a z f hf.1 source
      change BFSInvariant (residualNetwork G a z f hf.1) source data at hbi
      obtain ⟨hsource, hrise, hpath⟩ := bfsProg_level_rise G a z f hf.1 source
      change bfsLevel data source = 0 at hsource
      change ∀ u v, 0 < (residualNetwork G a z f hf.1).c u v →
        bfsLevel data v ≤ bfsLevel data u + 1 at hrise
      change ∀ v, v ∉ data.unseen →
        PathAt (residualNetwork G a z f hf.1) source v (bfsLevel data v) at hpath
      simp only [exactRun, Prog.eval_bind]
      change ExactCertificate _
        ((if sink ∈ data.unseen then Prog.pure (exactEmpty f data.unseenᶜ true) else
          (unitPhaseProg a z (bfsLevel data) f).bind fun phase =>
            if phase.finished then
              (exactRun a z fuel phase.flow).map (exactPrepend (bfsLevel data sink) phase.amount)
            else Prog.pure (exactEmpty phase.flow {source} false)).eval G.cut)
      split_ifs with hunseen
      · simp only [Prog.eval_pure]
        refine ⟨hf, hint, mem_compl.mpr hbi.source_seen, ?_, ?_, rfl⟩
        · exact fun h => (mem_compl.mp h) hunseen
        · exact bfsProg_out_zero G a z f hf.1 source
      · have hlevelPath := (hpath sink hunseen).tight (bfsLevel data) hsource hrise rfl
        let phase := (unitPhaseProg a z (bfsLevel data) f).eval G.cut
        have hp := unitPhaseProg_facts G a z (bfsLevel data) f hf hint
        change UnitPhaseFacts _ _ _ _ _ _ phase at hp
        have hfinished := unitPhaseProg_finishes G a z (bfsLevel data) f hf hint hstart
        have hpositive := unitPhaseProg_amount_pos G a z (bfsLevel data) f hf hint hstart hlevelPath
        change phase.finished = true at hfinished
        change 0 < phase.amount at hpositive
        have hnextStart : 0 ≤ netOut phase.flow source := by
          have hn : (0 : ℝ) ≤ phase.amount := Nat.cast_nonneg _
          linarith [hp.value]
        have hnextFuel : ((∑ v, a v : ℕ) : ℝ) < netOut phase.flow source + (fuel : ℝ) := by
          have ha : (1 : ℝ) ≤ phase.amount := by exact_mod_cast (Nat.succ_le_of_lt hpositive)
          simp only [Nat.cast_add, Nat.cast_one] at hfuel
          linarith [hp.value]
        have hi := ih phase.flow hp.feasible hp.integral hnextStart hnextFuel
        simp only [Prog.eval_bind]
        change ExactCertificate _
          ((if phase.finished then
              (exactRun a z fuel phase.flow).map (exactPrepend (bfsLevel data sink) phase.amount)
            else Prog.pure (exactEmpty phase.flow {source} false)).eval G.cut)
        simp only [hfinished, ↓reduceIte, Prog.eval_map]
        exact ⟨hi.feasible, hi.integral, hi.source_mem, hi.sink_notMem, hi.residual_zero,
          hi.finished⟩

theorem zero_stFlow (G : WeightedGraph V) (a z : V → ℕ) :
    (directed (twoStar G a z)).STFlow source sink (fun _ _ => 0) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro u v; simp
  · intro u v; exact (twoStar G a z).nonneg u v
  · intro v _ _; simp [netOut]

theorem exactProg_correct (G : WeightedGraph V) (hG : IntegralWeights G) (a z : V → ℕ) :
    ExactCertificate (directed (twoStar G a z)) ((exactProg a z).eval G.cut) := by
  apply exactRun_correct G a z (exactFuel a) (fun _ _ => 0) (zero_stFlow G a z)
  · intro u v
    obtain ⟨k, hk⟩ := twoStar_integral hG a z u v
    exact ⟨k, by simpa only [residual_c, sub_zero] using hk⟩
  · simp [netOut]
  · simp [netOut, exactFuel]

theorem scaledExactProg_correct (G : WeightedGraph V) (hG : AllPairsAudit.Unweighted G)
    (C : ℕ) (a z : V → ℕ) :
    ExactCertificate (directed (twoStar (scaledInternal G C) a z))
      ((scaledExactProg C a z).eval G.cut) := by
  rw [scaledExactProg, scaleAnswers_eval, ← scaledInternal_cut G C]
  exact exactProg_correct _ (scaledInternal_integral hG C) a z

theorem ExactCertificate.value_eq_cut {H : WeightedDiGraph (NetworkVertex V)}
    {result : ExactResult V} (hc : ExactCertificate H result) :
    netOut result.flow source = H.out result.shore := by
  have hsum : (∑ u ∈ result.shore, netOut result.flow u) = netOut result.flow source := by
    rw [← sum_erase_add _ _ hc.source_mem]
    have hz : (∑ u ∈ result.shore.erase source, netOut result.flow u) = 0 := by
      apply sum_eq_zero
      intro u hu
      exact hc.feasible.2 u (ne_of_mem_erase hu)
        (fun he => hc.sink_notMem (he ▸ mem_of_mem_erase hu))
    rw [hz, zero_add]
  have hz := hc.residual_zero
  rw [DirectedUnitST.Blocking.residual_out, hsum] at hz
  linarith

theorem ExactCertificate.minimum_shore {H : WeightedDiGraph (NetworkVertex V)}
    {result : ExactResult V} (hc : ExactCertificate H result)
    (S : Finset (NetworkVertex V)) (hs : source ∈ S) (ht : sink ∉ S) :
    H.out result.shore ≤ H.out S := by
  rw [← hc.value_eq_cut]
  exact WeightedDiGraph.netOut_le_out hc.feasible hs ht

theorem ExactCertificate.maximum_flow {H : WeightedDiGraph (NetworkVertex V)}
    {result : ExactResult V} (hc : ExactCertificate H result)
    (g : NetworkVertex V → NetworkVertex V → ℝ) (hg : H.STFlow source sink g) :
    netOut g source ≤ netOut result.flow source := by
  rw [hc.value_eq_cut]
  exact WeightedDiGraph.netOut_le_out hg hc.source_mem hc.sink_notMem

/-- Integrality of the returned signed flow follows from the original and
remaining nonnegative integral capacities. -/
theorem ExactCertificate.flow_integer {H : WeightedDiGraph (NetworkVertex V)}
    {result : ExactResult V} (hc : ExactCertificate H result) (hH : IntegralCap H)
    (u v : NetworkVertex V) : ∃ k : ℤ, result.flow u v = k := by
  obtain ⟨a, ha⟩ := hH u v
  obtain ⟨b, hb⟩ := hc.integral u v
  refine ⟨(a : ℤ) - b, ?_⟩
  simp only [residual_c, ha] at hb
  push_cast
  linarith

/-- Coarse all-answer bound only. The final asymptotic hard cap will use
the separate sharp history bound for honest simple input graphs. -/
def exactCoarseBudget (a : V → ℕ) : ℕ :=
  exactFuel a * (bfsBudget V + exactFuel a * bfsBudget V)

theorem exactRun_cost (read : Finset V → ℝ) (a z : V → ℕ) (fuel : ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ) :
    (exactRun a z fuel f).cost read ≤
      fuel * (bfsBudget V + exactFuel a * bfsBudget V) := by
  induction fuel generalizing f with
  | zero => simp [exactRun]
  | succ fuel ih =>
      simp only [exactRun, Prog.cost_bind]
      have hb := bfsProg_cost read a z f source
      change (bfsProg a z f source).cost read ≤ bfsBudget V at hb
      split_ifs
      · simp only [Prog.cost_pure, Nat.add_zero]
        rw [Nat.succ_mul]
        omega
      · simp only [Prog.cost_bind]
        have hp := unitPhaseRun_cost read a z (bfsLevel ((bfsProg a z f source).eval read))
          source sink (exactFuel a) f ∅
        change (unitPhaseProg a z (bfsLevel ((bfsProg a z f source).eval read)) f).cost read ≤
          exactFuel a * bfsBudget V at hp
        split_ifs
        · simp only [Prog.cost_map]
          have hi := ih ((unitPhaseProg a z (bfsLevel ((bfsProg a z f source).eval read)) f).eval read).flow
          rw [Nat.succ_mul]
          omega
        · simp only [Prog.cost_pure, Nat.add_zero]
          rw [Nat.succ_mul]
          omega

theorem exactProg_cost (read : Finset V → ℝ) (a z : V → ℕ) :
    (exactProg a z).cost read ≤ exactCoarseBudget a :=
  exactRun_cost read a z (exactFuel a) (fun _ _ => 0)

end
end CutQueryComplexity.DeterministicAPMCExpansion.Flow

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.exactRun_correct
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.scaledExactProg_correct
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.ExactCertificate.minimum_shore
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.ExactCertificate.maximum_flow
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.ExactCertificate.flow_integer
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.exactProg_cost
