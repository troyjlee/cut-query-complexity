import CutQueryComplexity.StarContraction2022.Quantum.Forest.Round
import CutQueryComplexity.Probability.Expectation

/-! # Drift of the executed component round

Active components and favorable colors are proof-side events of the actual
residual graph. They are never supplied to the public program. Fresh colors
give a quarter probability for each active component, and the accepted joint
row-recovery failure bound controls all shared row correlations.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Quantum.Forest
noncomputable section
open Finset ProductPrograms
open CutQueryComplexity.Probability
open scoped Classical ENNReal

variable {n : ℕ}

/-- Old components with an actual residual edge leaving the component. -/
def activeComponents (F : State n) (R : _root_.SimpleGraph (Fin n)) :
    Finset F.graph.ConnectedComponent :=
  univ.filter fun c => ∃ u v, F.graph.connectedComponentMk u = c ∧
    R.Adj u v ∧ ¬F.graph.Reachable u v

theorem inactive_component_closed (F : State n) (R : _root_.SimpleGraph (Fin n))
    (u : Fin n) (hu : F.graph.connectedComponentMk u ∉ activeComponents F R) :
    Certificates.Closed R (F.component u) := by
  intro x hx y hxy
  have hux := (F.mem_component u x).mp hx
  by_contra hy
  have hn : ¬F.graph.Reachable x y := fun h => hy ((F.mem_component u y).mpr (hux.trans h))
  apply hu
  exact mem_filter.mpr ⟨mem_univ _, x, y,
    _root_.SimpleGraph.ConnectedComponent.sound hux.symm, hxy, hn⟩

/-- Each inactive old component is already an entire residual component.
Injecting them into residual components bounds the actual component deficit. -/
theorem componentCount_le_active_add (F : State n) (R : _root_.SimpleGraph (Fin n))
    (hFR : F.graph ≤ R) :
    F.componentCount ≤ (activeComponents F R).card + Nat.card R.ConnectedComponent := by
  let inactive := (activeComponents F R)ᶜ
  let f : inactive → R.ConnectedComponent := fun c =>
    _root_.SimpleGraph.ConnectedComponent.map (_root_.SimpleGraph.Hom.ofLE hFR) c.val
  have hinj : Function.Injective f := by
    intro c d he
    obtain ⟨x, hx⟩ := Quot.exists_rep c.val
    obtain ⟨y, hy⟩ := Quot.exists_rep d.val
    change F.graph.connectedComponentMk x = c.val at hx
    change F.graph.connectedComponentMk y = d.val at hy
    have hcx : F.graph.connectedComponentMk x ∉ activeComponents F R := by
      rw [hx]
      exact mem_compl.mp c.property
    have hh : R.connectedComponentMk x = R.connectedComponentMk y := by
      simpa only [f, ← hx, ← hy, _root_.SimpleGraph.ConnectedComponent.map_mk,
        _root_.SimpleGraph.Hom.ofLE_apply] using he
    have hxy : y ∈ F.component x := reachable_mem_of_closed R (F.component x)
      (inactive_component_closed F R x hcx) (by simp)
      (_root_.SimpleGraph.ConnectedComponent.exact hh)
    apply Subtype.ext
    exact hx.symm.trans ((_root_.SimpleGraph.ConnectedComponent.sound
      ((F.mem_component x y).mp hxy)).trans hy)
  have hc := Fintype.card_le_of_injective f hinj
  have ha := Finset.card_le_univ (activeComponents F R)
  simp only [Fintype.card_coe, inactive, card_compl] at hc
  unfold State.componentCount
  simp only [Nat.card_eq_fintype_card]
  omega

def trueResidual (G : CapacityGraph (Fin n) 1) (E : LearnedEdges n) :
    _root_.SimpleGraph (Fin n) := edgeGraph (G.toWeighted.support.edgeFinset \ E)

theorem trueResidual_adj (G : CapacityGraph (Fin n) 1) (E : LearnedEdges n)
    (u v : Fin n) : (trueResidual G E).Adj u v ↔ ResidualNeighbor G E u v := by
  rw [trueResidual, edgeGraph_adj, ← residualNeighbor_iff_mem]
  constructor
  · exact And.left
  · intro h
    refine ⟨h, ?_⟩
    intro he
    subst v
    have hh := h.1
    rw [G.diag] at hh
    cases hh

theorem deficit_le_active (F : State n) (G : CapacityGraph (Fin n) 1)
    (E : LearnedEdges n) (hF : F.ResidualSound G.toWeighted.support E) :
    F.deficit G.toWeighted.support E ≤ (activeComponents F (trueResidual G E)).card := by
  have hc := componentCount_le_active_add F (trueResidual G E)
    (F.residualSound_subgraph G.toWeighted.support E hF)
  change F.componentCount - Nat.card (trueResidual G E).ConnectedComponent ≤ _
  omega

/-- Components that the actual coloring exposes through a red-to-blue
residual edge. Membership is used only in the proof. -/
def favorableComponents (F : State n) (G : CapacityGraph (Fin n) 1)
    (E : LearnedEdges n) (tape : ColorTape n) : Finset F.graph.ConnectedComponent :=
  (activeComponents F (trueResidual G E)).filter fun c => ∃ u v,
    F.graph.connectedComponentMk u = c ∧ u ∈ redVertices F tape ∧
      v ∈ blueVertices F tape ∧ ResidualNeighbor G E u v

theorem favorableComponents_card_le (F : State n) (G : CapacityGraph (Fin n) 1)
    (E : LearnedEdges n) (tape : ColorTape n) : (favorableComponents F G E tape).card ≤ n := by
  have hc := Finset.card_le_univ (favorableComponents F G E tape)
  have hn := F.componentCount_le
  unfold State.componentCount at hn
  simpa only [Nat.card_eq_fintype_card] using hc.trans (by simpa only [Nat.card_eq_fintype_card] using hn)

theorem favorableComponent_mass (F : State n) (G : CapacityGraph (Fin n) 1)
    (E : LearnedEdges n) (c : F.graph.ConnectedComponent)
    (hc : c ∈ activeComponents F (trueResidual G E)) :
    (4 : ℝ≥0∞)⁻¹ ≤ mass (Certificates.componentBits (Q := Fin n))
      (fun tape => c ∈ favorableComponents F G E tape) := by
  obtain ⟨u, v, hu, huv, hn⟩ := (mem_filter.mp hc).2
  rw [← Certificates.componentColor_red_blue F.graph hn]
  apply mass_mono
  intro tape ht
  refine mem_filter.mpr ⟨hc, u, v, hu, ?_, ?_, (trueResidual_adj G E u v).mp huv⟩
  · exact (mem_redVertices ..).mpr ht.1
  · exact (mem_blueVertices ..).mpr ht.2

/-- Linearity alone sums the quarter-probability events. Distinct row events
may be correlated through both colors and the shared recovery samples. -/
theorem favorableComponents_expect (F : State n) (G : CapacityGraph (Fin n) 1)
    (E : LearnedEdges n) :
    ((activeComponents F (trueResidual G E)).card : ℝ≥0∞) / 4 ≤
      CutQueryComplexity.Probability.expect (Certificates.componentBits (Q := Fin n))
        (fun tape => ((favorableComponents F G E tape).card : ℝ≥0∞)) := by
  have hcount (tape : ColorTape n) :
      ((favorableComponents F G E tape).card : ℝ≥0∞) =
        ∑ c ∈ activeComponents F (trueResidual G E),
          if c ∈ favorableComponents F G E tape then 1 else 0 := by
    rw [favorableComponents, card_filter]
    push_cast
    apply sum_congr rfl
    intro c hc
    simp only [mem_filter, hc, true_and]
  simp_rw [hcount]
  rw [CutQueryComplexity.Probability.expect_sum]
  calc
    ((activeComponents F (trueResidual G E)).card : ℝ≥0∞) / 4 =
        ∑ _c ∈ activeComponents F (trueResidual G E), (4 : ℝ≥0∞)⁻¹ := by
      simp [div_eq_mul_inv, nsmul_eq_mul]
    _ ≤ _ := by
      apply sum_le_sum
      intro c hc
      have hind : CutQueryComplexity.Probability.expect (Certificates.componentBits (Q := Fin n))
          (fun tape => if c ∈ favorableComponents F G E tape then 1 else 0) =
          mass (Certificates.componentBits (Q := Fin n))
            (fun tape => c ∈ favorableComponents F G E tape) := by
        rw [CutQueryComplexity.Probability.expect, mass_eq_tsum]
        apply tsum_congr
        intro tape
        by_cases hh : c ∈ favorableComponents F G E tape <;> simp [hh]
      rw [hind]
      exact favorableComponent_mass F G E c hc

theorem favorableComponents_subset_recovered (F : State n) (G : CapacityGraph (Fin n) 1)
    (E : LearnedEdges n) (eta : ℝ) (hE : KnownSubgraph E G)
    (tape : ColorTape n) {rows : RowTable n}
    (hr : rows ∈ ((recoverRows n E (redVertices F tape) (blueVertices F tape) eta).eval
      (productRead G)).support)
    (hcomplete : RowsComplete G E (redVertices F tape) (blueVertices F tape) rows) :
    favorableComponents F G E tape ⊆ recoveredComponents F tape rows := by
  intro c hc
  obtain ⟨u, v, hu, hred, hblue, huv⟩ := (mem_filter.mp hc).2
  have hne := hcomplete u hred ⟨v, mem_filter.mpr ⟨hblue, huv⟩⟩
  cases he : rows u with
  | none => exact False.elim (hne he)
  | some w =>
      have hs := recoverRows_sound G E hE _ _ eta hr he
      exact mem_filter.mpr ⟨mem_univ _, (u, w), hu, hred, hs.2.1, he⟩

/-- Complete recovery inserts at least one edge for each favorable component;
on the failure event the lost contribution is at most the vertex count. -/
theorem roundUpdate_drift_pointwise (F : State n) (G : CapacityGraph (Fin n) 1)
    (E : LearnedEdges n) (eta : ℝ) (hE : KnownSubgraph E G)
    (hF : F.ResidualSound G.toWeighted.support E) (tape : ColorTape n) {rows : RowTable n}
    (hr : rows ∈ ((recoverRows n E (redVertices F tape) (blueVertices F tape) eta).eval
      (productRead G)).support) :
    ((roundUpdate F tape rows).deficit G.toWeighted.support E : ℝ≥0∞) +
      (favorableComponents F G E tape).card ≤
      (F.deficit G.toWeighted.support E : ℝ≥0∞) +
        if ¬RowsComplete G E (redVertices F tape) (blueVertices F tape) rows then (n : ℝ≥0∞) else 0 := by
  have hc := roundUpdate_deficit F G E eta hE hF tape hr
  by_cases hcomplete : RowsComplete G E (redVertices F tape) (blueVertices F tape) rows
  · simp only [not_true_eq_false, hcomplete, ite_false, add_zero]
    have hsub := card_mono (favorableComponents_subset_recovered F G E eta hE tape hr hcomplete)
    have hn : (roundUpdate F tape rows).deficit G.toWeighted.support E +
        (favorableComponents F G E tape).card ≤ F.deficit G.toWeighted.support E := by omega
    exact_mod_cast hn
  · simp only [hcomplete, not_false_eq_true, ite_true]
    apply add_le_add
    · exact_mod_cast (show (roundUpdate F tape rows).deficit G.toWeighted.support E ≤
        F.deficit G.toWeighted.support E by omega)
    · exact_mod_cast favorableComponents_card_le F G E tape

theorem recovery_error_contribution (n : ℕ) (eta : ℝ) (_heta : 0 ≤ eta) :
    (n : ℝ≥0∞) * ENNReal.ofReal (eta / (8 * (n : ℝ))) ≤ ENNReal.ofReal (eta / 8) := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
    apply le_of_eq
    congr 1
    field_simp

/-- Expectation over the actual shared recovery tape, with the actual joint
failure event. The only input correctness premises concern the old forest. -/
theorem recoverRound_drift (F : State n) (G : CapacityGraph (Fin n) 1)
    (E : LearnedEdges n) (eta : ℝ) (hE : KnownSubgraph E G)
    (hF : F.ResidualSound G.toWeighted.support E) (heta : 0 < eta) (tape : ColorTape n) :
    CutQueryComplexity.Probability.expect ((recoverRows n E (redVertices F tape) (blueVertices F tape) eta).eval (productRead G))
        (fun rows => ((roundUpdate F tape rows).deficit G.toWeighted.support E : ℝ≥0∞)) +
      (favorableComponents F G E tape).card ≤
        (F.deficit G.toWeighted.support E : ℝ≥0∞) + ENNReal.ofReal (eta / 8) := by
  let law := (recoverRows n E (redVertices F tape) (blueVertices F tape) eta).eval (productRead G)
  have hp := CutQueryComplexity.Probability.expect_mono_on_support law
    (fun rows hr => roundUpdate_drift_pointwise F G E eta hE hF tape hr)
  have hi : CutQueryComplexity.Probability.expect law (fun rows =>
      if ¬RowsComplete G E (redVertices F tape) (blueVertices F tape) rows then (n : ℝ≥0∞) else 0) =
      (n : ℝ≥0∞) * mass law
        (fun rows => ¬RowsComplete G E (redVertices F tape) (blueVertices F tape) rows) := by
    rw [CutQueryComplexity.Probability.expect, mass_eq_tsum, ← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro rows
    by_cases hh : RowsComplete G E (redVertices F tape) (blueVertices F tape) rows <;>
      simp [hh, mul_comm]
  rw [CutQueryComplexity.Probability.expect_add, CutQueryComplexity.Probability.expect_const, CutQueryComplexity.Probability.expect_add, CutQueryComplexity.Probability.expect_const, hi] at hp
  apply hp.trans
  apply add_le_add_right
  calc
    _ ≤ (n : ℝ≥0∞) * ENNReal.ofReal (eta / (8 * (n : ℝ))) := by
      exact mul_le_mul le_rfl
        (recoverRows_failure G E hE _ _ eta (red_blue_disjoint F tape) heta)
        (by positivity) (by positivity)
    _ ≤ _ := recovery_error_contribution n eta heta.le

/-- The fresh public component coloring gives the quarter-deficit reduction
for the law actually returned by `forestRound`, not an assumed transition. -/
theorem forestRound_drift (F : State n) (G : CapacityGraph (Fin n) 1)
    (E : LearnedEdges n) (eta : ℝ) (hE : KnownSubgraph E G)
    (hF : F.ResidualSound G.toWeighted.support E) (heta : 0 < eta) :
    CutQueryComplexity.Probability.expect ((forestRound F E eta).eval (productRead G))
      (fun H => (H.deficit G.toWeighted.support E : ℝ≥0∞)) ≤
      (3 / 4 : ℝ≥0∞) * F.deficit G.toWeighted.support E + ENNReal.ofReal (eta / 8) := by
  let z : ℝ≥0∞ := F.deficit G.toWeighted.support E
  have ha : z / 4 ≤ CutQueryComplexity.Probability.expect (Certificates.componentBits (Q := Fin n))
      (fun tape => ((favorableComponents F G E tape).card : ℝ≥0∞)) := by
    apply le_trans ?_ (favorableComponents_expect F G E)
    simp only [div_eq_mul_inv]
    have hz : z ≤ ((activeComponents F (trueResidual G E)).card : ℝ≥0∞) := by
      dsimp [z]
      exact_mod_cast deficit_le_active F G E hF
    exact mul_le_mul hz le_rfl (by positivity) (by positivity)
  have hp := CutQueryComplexity.Probability.expect_le_of_le_on_support (Certificates.componentBits (Q := Fin n))
    (fun tape _ => recoverRound_drift F G E eta hE hF heta tape)
  rw [CutQueryComplexity.Probability.expect_add] at hp
  have he := forestRound_eval F E eta (productRead G)
  rw [he, CutQueryComplexity.Probability.expect_bind]
  simp only [CutQueryComplexity.Probability.expect_map]
  apply (ENNReal.add_le_add_iff_right (show z / 4 ≠ ⊤ by finiteness)).mp
  apply le_trans (add_le_add_right ha _) (hp.trans_eq ?_)
  change z + ENNReal.ofReal (eta / 8) =
    (3 / 4 : ℝ≥0∞) * z + ENNReal.ofReal (eta / 8) + z / 4
  have hz : (3 / 4 : ℝ≥0∞) * z + (1 / 4 : ℝ≥0∞) * z = z := by
    rw [← add_mul]
    have hc : (3 / 4 : ℝ≥0∞) + 1 / 4 = 1 := by
      rw [div_eq_mul_inv, div_eq_mul_inv, ← add_mul]
      norm_num
      exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
    rw [hc, one_mul]
  calc
    _ = ((3 / 4 : ℝ≥0∞) * z + (1 / 4 : ℝ≥0∞) * z) + ENNReal.ofReal (eta / 8) := by rw [hz]
    _ = _ := by
      have he : (1 / 4 : ℝ≥0∞) * z = z / 4 := by simp [div_eq_mul_inv, mul_comm]
      rw [he, add_right_comm]

/-- Every color and every recovery sample, including unsuccessful trials.
With the answer function this determines every queried shore and every reply. -/
abbrev FullRoundTape (n : ℕ) (eta : ℝ) := ColorTape n × RecoveryTape n eta

def fullRoundLaw (F : State n) (eta : ℝ) : PMF (FullRoundTape n eta) :=
  (Certificates.componentBits (Q := Fin n)).bind fun color =>
    (recoveryTape (blueVertices F color) eta).map fun trials => (color, trials)

def fullRoundState (F : State n) (E : LearnedEdges n) (eta : ℝ)
    (read : Finset (Fin n) → ProductAnswer n 1) (tape : FullRoundTape n eta) : State n :=
  roundUpdate F tape.1 (recoverResult E (redVertices F tape.1) (blueVertices F tape.1)
    tape.2 (fun i => read (rowQuery tape.2 i)))

/-- The full-tape refinement is exactly the existing executed round law. -/
theorem forestRound_eval_full (F : State n) (E : LearnedEdges n) (eta : ℝ)
    (read : Finset (Fin n) → ProductAnswer n 1) :
    (forestRound F E eta).eval read =
      (fullRoundLaw F eta).map (fullRoundState F E eta read) := by
  rw [forestRound_eval]
  simp_rw [recoverRows_eval E _ _ eta (red_blue_disjoint F _) read]
  simp only [fullRoundLaw, PMF.map_bind, PMF.map_comp, Function.comp_def, fullRoundState]

theorem fullRoundState_residualSound (F : State n) (G : CapacityGraph (Fin n) 1)
    (E : LearnedEdges n) (eta : ℝ) (hE : KnownSubgraph E G)
    (hF : F.ResidualSound G.toWeighted.support E) {tape : FullRoundTape n eta}
    (ht : tape ∈ (fullRoundLaw F eta).support) :
    (fullRoundState F E eta (productRead G) tape).ResidualSound G.toWeighted.support E := by
  apply forestRound_residualSound F G E eta hE hF
  rw [forestRound_eval_full]
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨tape, ht, rfl⟩

/-- Proof-side replay of the complete past transcript; this defines no
multi-round query program or assumed transition oracle. -/
def fullHistoryState (F : State n) (E : LearnedEdges n) (eta : ℝ)
    (read : Finset (Fin n) → ProductAnswer n 1) : List (FullRoundTape n eta) → State n
  | [] => F
  | tape :: history => fullHistoryState (fullRoundState F E eta read tape) E eta read history

/-- Reachability is actual support membership at each fresh-tape draw. It
contains no correctness, success, progress, or budget assumptions. -/
def ReachableFullHistory (F : State n) (E : LearnedEdges n) (eta : ℝ)
    (read : Finset (Fin n) → ProductAnswer n 1) : List (FullRoundTape n eta) → Prop
  | [] => True
  | tape :: history => tape ∈ (fullRoundLaw F eta).support ∧
      ReachableFullHistory (fullRoundState F E eta read tape) E eta read history

theorem fullHistoryState_residualSound (F : State n) (G : CapacityGraph (Fin n) 1)
    (E : LearnedEdges n) (eta : ℝ) (hE : KnownSubgraph E G)
    (hF : F.ResidualSound G.toWeighted.support E) (history : List (FullRoundTape n eta))
    (hh : ReachableFullHistory F E eta (productRead G) history) :
    (fullHistoryState F E eta (productRead G) history).ResidualSound G.toWeighted.support E := by
  induction history generalizing F with
  | nil => exact hF
  | cons tape history ih =>
      exact ih _ (fullRoundState_residualSound F G E eta hE hF hh.1) hh.2

/-- Uniform conditional drift after every full reachable random-and-answer
history, including all failed isolation trials. The next draw is the fresh
law of the actual public program at the replayed state. -/
theorem forestRound_drift_at_full_history (F : State n) (G : CapacityGraph (Fin n) 1)
    (E : LearnedEdges n) (eta : ℝ) (hE : KnownSubgraph E G)
    (hF : F.ResidualSound G.toWeighted.support E) (heta : 0 < eta)
    (history : List (FullRoundTape n eta))
    (hh : ReachableFullHistory F E eta (productRead G) history) :
    let H := fullHistoryState F E eta (productRead G) history
    CutQueryComplexity.Probability.expect ((forestRound H E eta).eval (productRead G))
      (fun K => (K.deficit G.toWeighted.support E : ℝ≥0∞)) ≤
        (3 / 4 : ℝ≥0∞) * H.deficit G.toWeighted.support E + ENNReal.ofReal (eta / 8) := by
  exact forestRound_drift _ G E eta hE
    (fullHistoryState_residualSound F G E eta hE hF history hh) heta

/-- One public tree, before every hidden input, with its actual cap,
supported correctness, and quantitative next-law guarantee together. -/
theorem forestRound_progress_public (F : State n) (E : LearnedEdges n) (eta : ℝ)
    (heta : 0 < eta) :
    ∃ T : ProductTree n (State n) (recoverBudget n eta),
      (∀ read out, out ∈ (RTree.run read T).support → out.2 ≤ recoverBudget n eta) ∧
      ∀ G : CapacityGraph (Fin n) 1, KnownSubgraph E G →
        F.ResidualSound G.toWeighted.support E →
        (∀ H ∈ (T.eval (productRead G)).support, H.ResidualSound G.toWeighted.support E) ∧
        CutQueryComplexity.Probability.expect (T.eval (productRead G))
          (fun H => (H.deficit G.toWeighted.support E : ℝ≥0∞)) ≤
            (3 / 4 : ℝ≥0∞) * F.deficit G.toWeighted.support E + ENNReal.ofReal (eta / 8) := by
  refine ⟨forestRound F E eta, fun read _ h => forestRound_cost F E eta read h, ?_⟩
  intro G hE hF
  exact ⟨fun _ hH => forestRound_residualSound F G E eta hE hF hH,
    forestRound_drift F G E eta hE hF heta⟩

#print axioms componentCount_le_active_add
#print axioms deficit_le_active
#print axioms favorableComponents_expect
#print axioms favorableComponents_subset_recovered
#print axioms roundUpdate_drift_pointwise
#print axioms recoverRound_drift
#print axioms forestRound_drift
#print axioms forestRound_eval_full
#print axioms fullRoundState_residualSound
#print axioms fullHistoryState_residualSound
#print axioms forestRound_drift_at_full_history
#print axioms forestRound_progress_public

end
end CutQueryComplexity.StarContraction2022.Quantum.Forest
