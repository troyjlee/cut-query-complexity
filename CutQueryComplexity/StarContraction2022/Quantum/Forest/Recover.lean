import CutQueryComplexity.StarContraction2022.Quantum.Forest.Budget
import CutQueryComplexity.StarContraction2022.Quantum.Forest.Decode
import CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.Counts

/-! # Actual bounded shared-sample residual row recovery

Public random bits choose a blue subset for each scale and repetition. Each
subset is queried once in full and once per label bit. All rows share those
queries. The public decoder subtracts learned edges, checks count one and
all bit counts, and chooses a decoded endpoint only in a red row. Overlapping
red/blue sets fail before any query. No hidden graph enters a constructor.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Quantum.Forest
noncomputable section
open Finset ProductPrograms
open CutQueryComplexity.Probability
open scoped Classical ENNReal

abbrev RowTable (n : ℕ) := Fin n → Option (Fin n)
abbrev TrialIndex (n : ℕ) (eta : ℝ) := Fin (logWidth n) × Fin (rowTrials n eta)
abbrev RowQueryIndex (n : ℕ) (eta : ℝ) := TrialIndex n eta × Option (Fin (logWidth n))
abbrev RecoveryTape (n : ℕ) (eta : ℝ) :=
  Fin (logWidth n) → Fin (rowTrials n eta) → Finset (Fin n)

variable {n : ℕ} {eta : ℝ}

/-- The actual finite product of fresh repetitions at every public scale. -/
def recoveryTape (blue : Finset (Fin n)) (eta : ℝ) : PMF (RecoveryTape n eta) :=
  Probability.product fun j : Fin (logWidth n) =>
    isolationTrials blue (dyadicProbability j.val)
      (dyadicProbability_pos j.val).le (dyadicProbability_le_one j.val) (rowTrials n eta)

theorem recoveryTape_supported_subset (blue : Finset (Fin n)) (eta : ℝ)
    {tape : RecoveryTape n eta} (ht : tape ∈ (recoveryTape blue eta).support)
    (j : Fin (logWidth n)) (k : Fin (rowTrials n eta)) : tape j k ⊆ blue := by
  have hj := (Probability.mem_support_product _ _).mp ht j
  have hk := (Probability.mem_support_product _ _).mp hj k
  exact sampleBlue_supported_subset blue _ _ _ hk

def rowQuery (tape : RecoveryTape n eta) (i : RowQueryIndex n eta) : Finset (Fin n) :=
  match i.2 with
  | none => tape i.1.1 i.1.2
  | some b => tape i.1.1 i.1.2 ∩ bitMask n (logWidth n) b

/-- Query every position of an explicit public vector, with one call per
position even when the answer is malformed. -/
private def queryVector : (q : ℕ) → (Fin q → Finset (Fin n)) →
    ProductTree n (Fin q → ProductAnswer n 1) q
  | 0, _ => RTree.pure (PMF.pure Fin.elim0)
  | q + 1, queries => RTree.query (queries 0) fun answer =>
      RTree.map (Fin.cases answer) (queryVector q (fun i => queries i.succ))

private theorem queryVector_eval (q : ℕ) (queries : Fin q → Finset (Fin n))
    (read : Finset (Fin n) → ProductAnswer n 1) :
    (queryVector q queries).eval read = PMF.pure (fun i => read (queries i)) := by
  induction q with
  | zero =>
      simp only [queryVector, RTree.eval_pure]
      congr 1
      funext i
      exact Fin.elim0 i
  | succ q ih =>
      simp only [queryVector, RTree.eval_query, RTree.eval_map, ih, PMF.pure_map]
      congr 1
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl

private def queryTable {I : Type} [Fintype I] (queries : I → Finset (Fin n)) :
    ProductTree n (I → ProductAnswer n 1) (Fintype.card I) :=
  RTree.map (fun answers i => answers (Fintype.equivFin I i))
    (queryVector (Fintype.card I) (fun i => queries ((Fintype.equivFin I).symm i)))

private theorem queryTable_eval {I : Type} [Fintype I] (queries : I → Finset (Fin n))
    (read : Finset (Fin n) → ProductAnswer n 1) :
    (queryTable queries).eval read = PMF.pure (fun i => read (queries i)) := by
  simp only [queryTable, RTree.eval_map, queryVector_eval, PMF.pure_map,
    Equiv.symm_apply_apply]

theorem rowQueryIndex_card (n : ℕ) (eta : ℝ) :
    Fintype.card (RowQueryIndex n eta) = recoverBudget n eta := by
  simp [RowQueryIndex, TrialIndex, recoverBudget, Nat.add_comm]

def decodedTrial (E : LearnedEdges n) (blue : Finset (Fin n))
    (tape : RecoveryTape n eta) (answers : RowQueryIndex n eta → ProductAnswer n 1)
    (a : TrialIndex n eta) (u : Fin n) : Option (Fin n) :=
  decodeRow blue u (residualCount E (tape a.1 a.2) (answers (a, none)) u)
    (fun b => residualCount E (tape a.1 a.2 ∩ bitMask n (logWidth n) b)
      (answers (a, some b)) u)

/-- Finite selection uses only decoded answer data; there is no hidden-edge
test in this choice. -/
def selectRow (red : Finset (Fin n)) (trials : TrialIndex n eta → RowTable n)
    (u : Fin n) : Option (Fin n) :=
  if u ∈ red then
    if h : ∃ v, ∃ a, trials a u = some v then some h.choose else none
  else none

theorem selectRow_some (red : Finset (Fin n)) (trials : TrialIndex n eta → RowTable n)
    {u v : Fin n} (h : selectRow red trials u = some v) :
    u ∈ red ∧ ∃ a, trials a u = some v := by
  unfold selectRow at h
  split_ifs at h with hu hex
  · have hv := Option.some.inj h
    exact ⟨hu, hv ▸ hex.choose_spec⟩

theorem selectRow_ne_none_iff (red : Finset (Fin n))
    (trials : TrialIndex n eta → RowTable n) (u : Fin n) :
    selectRow red trials u ≠ none ↔ u ∈ red ∧ ∃ v, ∃ a, trials a u = some v := by
  constructor
  · intro h
    cases he : selectRow red trials u with
    | none => exact False.elim (h he)
    | some v =>
        obtain ⟨hu, a, ha⟩ := selectRow_some red trials he
        exact ⟨hu, v, a, ha⟩
  · rintro ⟨hu, hx⟩
    simp only [selectRow, ite_eq_left hu, dite_eq_left hx, ne_eq,
      reduceCtorEq, not_false_eq_true]

def recoverResult (E : LearnedEdges n) (red blue : Finset (Fin n))
    (tape : RecoveryTape n eta) (answers : RowQueryIndex n eta → ProductAnswer n 1) : RowTable n :=
  selectRow red (decodedTrial E blue tape answers)

/-- The whole public randomized tree. Sampling is unconditional; neither
successful decoding nor graph correctness conditions the random tape. -/
def recoverRows (n : ℕ) (E : LearnedEdges n) (red blue : Finset (Fin n)) (eta : ℝ) :
    ProductTree n (RowTable n) (recoverBudget n eta) :=
  if Disjoint red blue then
    RTree.mix ((recoveryTape blue eta).map fun tape =>
      RTree.cast (rowQueryIndex_card n eta)
        (RTree.map (recoverResult E red blue tape) (queryTable (rowQuery tape))))
  else RTree.pure (PMF.pure (fun _ => none))

theorem recoverRows_eval (E : LearnedEdges n) (red blue : Finset (Fin n)) (eta : ℝ)
    (hdis : Disjoint red blue) (read : Finset (Fin n) → ProductAnswer n 1) :
    (recoverRows n E red blue eta).eval read =
      (recoveryTape blue eta).map (fun tape =>
        recoverResult E red blue tape (fun i => read (rowQuery tape i))) := by
  simp only [recoverRows, ite_eq_left hdis, RTree.eval_mix, PMF.bind_map, Function.comp_def,
    RTree.eval_cast, RTree.eval_map, queryTable_eval, PMF.pure_map]
  rfl

theorem recoverRows_eval_overlap (E : LearnedEdges n) (red blue : Finset (Fin n)) (eta : ℝ)
    (hdis : ¬ Disjoint red blue) (read : Finset (Fin n) → ProductAnswer n 1) :
    (recoverRows n E red blue eta).eval read = PMF.pure (fun _ => none) := by
  simp only [recoverRows, ite_eq_right hdis, RTree.eval_pure]

/-- Every finite answer function, including malformed replies, obeys the
public cap; the type index also bounds every query continuation. -/
theorem recoverRows_cost (E : LearnedEdges n) (red blue : Finset (Fin n)) (eta : ℝ)
    (read : Finset (Fin n) → ProductAnswer n 1) {out : RowTable n × ℕ}
    (h : out ∈ (RTree.run read (recoverRows n E red blue eta)).support) :
    out.2 ≤ logWidth n * rowTrials n eta * (logWidth n + 1) :=
  RTree.cost_le _ read h

def residualRow (G : CapacityGraph (Fin n) 1) (E : LearnedEdges n)
    (blue : Finset (Fin n)) (u : Fin n) : Finset (Fin n) :=
  blue.filter (ResidualNeighbor G E u)

theorem residualRow_inter (G : CapacityGraph (Fin n) 1) (E : LearnedEdges n)
    (blue S : Finset (Fin n)) (u : Fin n) (hS : S ⊆ blue) :
    residualRow G E blue u ∩ S = S.filter (ResidualNeighbor G E u) := by
  ext v
  simp only [residualRow, mem_inter, mem_filter]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hS h.1, h.2⟩, h.1⟩⟩

theorem decodedTrial_honest (G : CapacityGraph (Fin n) 1) (E : LearnedEdges n)
    (hE : KnownSubgraph E G) (blue : Finset (Fin n)) (tape : RecoveryTape n eta)
    (a : TrialIndex n eta) (u : Fin n) (hu : u ∉ blue) (hS : tape a.1 a.2 ⊆ blue) :
    decodedTrial E blue tape (fun i => productRead G (rowQuery tape i)) a u =
      decodeRow blue u (residualRow G E blue u ∩ tape a.1 a.2).card
        (maskCounts (width := logWidth n) (residualRow G E blue u ∩ tape a.1 a.2)) := by
  have huS : u ∉ tape a.1 a.2 := fun h => hu (hS h)
  have hm (b : Fin (logWidth n)) : u ∉ tape a.1 a.2 ∩ bitMask n (logWidth n) b :=
    fun h => huS (mem_inter.mp h).1
  simp only [decodedTrial, rowQuery, residualCount_eq_card hE _ huS,
    residualCount_eq_card hE _ (hm _), residualRow_inter G E blue _ u hS]
  congr 1
  funext b
  unfold maskCounts
  congr 1
  ext v
  simp only [mem_filter, mem_inter]
  tauto

theorem decodedTrial_honest_some_iff (G : CapacityGraph (Fin n) 1) (E : LearnedEdges n)
    (hE : KnownSubgraph E G) (blue : Finset (Fin n)) (tape : RecoveryTape n eta)
    (a : TrialIndex n eta) (u v : Fin n) (hu : u ∉ blue) (hS : tape a.1 a.2 ⊆ blue) :
    decodedTrial E blue tape (fun i => productRead G (rowQuery tape i)) a u = some v ↔
      residualRow G E blue u ∩ tape a.1 a.2 = {v} := by
  rw [decodedTrial_honest G E hE blue tape a u hu hS]
  apply decodeRow_honest (logarithmic_width n) blue _ u v _ hu
  exact inter_subset_left.trans (filter_subset _ _)

theorem recoverResult_sound (G : CapacityGraph (Fin n) 1) (E : LearnedEdges n)
    (hE : KnownSubgraph E G) (red blue : Finset (Fin n)) (hdis : Disjoint red blue)
    {tape : RecoveryTape n eta} (ht : tape ∈ (recoveryTape blue eta).support)
    {u v : Fin n}
    (h : recoverResult E red blue tape (fun i => productRead G (rowQuery tape i)) u = some v) :
    u ∈ red ∧ v ∈ blue ∧ ResidualNeighbor G E u v := by
  obtain ⟨hu, a, ha⟩ := selectRow_some red _ h
  have hub : u ∉ blue := fun hb => (Finset.disjoint_left.mp hdis) hu hb
  have he := (decodedTrial_honest_some_iff G E hE blue tape a u v hub
    (recoveryTape_supported_subset blue eta ht a.1 a.2)).mp ha
  have hv : v ∈ residualRow G E blue u ∩ tape a.1 a.2 := by rw [he]; simp
  have hv' := mem_filter.mp (mem_inter.mp hv).1
  exact ⟨hu, hv'.1, hv'.2⟩

theorem recoverRows_sound (G : CapacityGraph (Fin n) 1) (E : LearnedEdges n)
    (hE : KnownSubgraph E G) (red blue : Finset (Fin n)) (eta : ℝ) {rows : RowTable n}
    (hr : rows ∈ ((recoverRows n E red blue eta).eval (productRead G)).support)
    {u v : Fin n} (huv : rows u = some v) :
    u ∈ red ∧ v ∈ blue ∧ ResidualNeighbor G E u v := by
  by_cases hdis : Disjoint red blue
  · rw [recoverRows_eval E red blue eta hdis] at hr
    obtain ⟨tape, ht, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
    exact recoverResult_sound G E hE red blue hdis ht huv
  · rw [recoverRows_eval_overlap E red blue eta hdis] at hr
    have he := (PMF.mem_support_pure_iff _ _).mp hr
    subst rows
    cases huv

theorem recoverRows_empty_row (G : CapacityGraph (Fin n) 1) (E : LearnedEdges n)
    (hE : KnownSubgraph E G) (red blue : Finset (Fin n)) (eta : ℝ) {rows : RowTable n}
    (hr : rows ∈ ((recoverRows n E red blue eta).eval (productRead G)).support)
    (u : Fin n) (hempty : residualRow G E blue u = ∅) : rows u = none := by
  cases he : rows u with
  | none => rfl
  | some v =>
      have hs := recoverRows_sound G E hE red blue eta hr he
      have hv : v ∈ residualRow G E blue u := mem_filter.mpr ⟨hs.2.1, hs.2.2⟩
      rw [hempty] at hv
      exact False.elim (notMem_empty v hv)

private theorem mass_product_coordinate {I A : Type} [Fintype I] [Fintype A]
    (laws : I → PMF A) (i : I) (P : A → Prop) :
    mass (Probability.product laws) (fun tape => P (tape i)) = mass (laws i) P := by
  have he : (fun tape : I → A => P (tape i)) =
      (fun tape => ∀ j, j = i → P (tape j)) := by
    funext tape
    exact propext ⟨fun h j hj => hj ▸ h, fun h => h i rfl⟩
  rw [he, Probability.mass_product laws (fun j x => j = i → P x), Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

/-- A successful count-one trial forces the public selector to return a
neighbor, regardless of all other trials' outcomes. -/
theorem recoverResult_ne_none_of_isolated (G : CapacityGraph (Fin n) 1)
    (E : LearnedEdges n) (hE : KnownSubgraph E G) (red blue : Finset (Fin n))
    (hdis : Disjoint red blue) {tape : RecoveryTape n eta}
    (ht : tape ∈ (recoveryTape blue eta).support) {u : Fin n} (hu : u ∈ red)
    (a : TrialIndex n eta)
    (hisolated : (residualRow G E blue u ∩ tape a.1 a.2).card = 1) :
    recoverResult E red blue tape (fun i => productRead G (rowQuery tape i)) u ≠ none := by
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hisolated
  have hub : u ∉ blue := fun hb => (Finset.disjoint_left.mp hdis) hu hb
  apply (selectRow_ne_none_iff red _ u).mpr
  exact ⟨hu, v, a, (decodedTrial_honest_some_iff G E hE blue tape a u v hub
    (recoveryTape_supported_subset blue eta ht a.1 a.2)).mpr hv⟩

/-- The selected dyadic scale is a proof witness only. The public tree runs
all scales and samples exactly their unconditioned finite product law. -/
theorem recoverResult_row_failure_le (G : CapacityGraph (Fin n) 1)
    (E : LearnedEdges n) (hE : KnownSubgraph E G) (red blue : Finset (Fin n))
    (eta : ℝ) (hdis : Disjoint red blue) {u : Fin n} (hu : u ∈ red)
    (hrow : (residualRow G E blue u).Nonempty) :
    mass (recoveryTape blue eta) (fun tape =>
      recoverResult E red blue tape (fun i => productRead G (rowQuery tape i)) u = none) ≤
        (7 / 8 : ℝ≥0∞) ^ rowTrials n eta := by
  let N := residualRow G E blue u
  have hcard : N.card ≤ n := by simpa only [Fintype.card_fin] using card_le_univ N
  have hs := dyadic_scale (card_pos.mpr hrow) hcard
  let j : Fin (logWidth n) := ⟨Nat.clog 2 N.card, hs.1⟩
  calc
    _ ≤ mass (recoveryTape blue eta) (fun tape => ∀ k, (N ∩ tape j k).card ≠ 1) := by
      apply mass_mono_on_support
      intro tape ht hnone k hisolated
      exact (recoverResult_ne_none_of_isolated G E hE red blue hdis ht hu (j, k)
        hisolated) hnone
    _ = mass (isolationTrials blue (dyadicProbability j.val)
          (dyadicProbability_pos j.val).le (dyadicProbability_le_one j.val) (rowTrials n eta))
        (fun samples => ∀ k, (N ∩ samples k).card ≠ 1) := by
      simpa only [recoveryTape] using
        (mass_product_coordinate
          (fun b : Fin (logWidth n) => isolationTrials blue (dyadicProbability b.val)
            (dyadicProbability_pos b.val).le (dyadicProbability_le_one b.val) (rowTrials n eta))
          j (fun samples => ∀ k, (N ∩ samples k).card ≠ 1))
    _ ≤ _ := isolationTrials_failure_le blue N (dyadicProbability j.val)
      (dyadicProbability_pos j.val).le (dyadicProbability_le_one j.val)
      (filter_subset _ _) hrow hs.2.1 hs.2.2 (rowTrials n eta)

def RowsComplete (G : CapacityGraph (Fin n) 1) (E : LearnedEdges n)
    (red blue : Finset (Fin n)) (rows : RowTable n) : Prop :=
  ∀ u ∈ red, (residualRow G E blue u).Nonempty → rows u ≠ none

/-- Simultaneous error of the actual executed recovery tree. The union bound
allows arbitrary dependence between rows sharing the same sample. -/
theorem recoverRows_failure (G : CapacityGraph (Fin n) 1) (E : LearnedEdges n)
    (hE : KnownSubgraph E G) (red blue : Finset (Fin n)) (eta : ℝ)
    (hdis : Disjoint red blue) (heta : 0 < eta) :
    mass ((recoverRows n E red blue eta).eval (productRead G))
      (fun rows => ¬RowsComplete G E red blue rows) ≤ ENNReal.ofReal (eta / (8 * (n : ℝ))) := by
  by_cases hn : 0 < n
  · rw [recoverRows_eval E red blue eta hdis, mass_map]
    have hb (u : Fin n) (hu : u ∈ red) :
        mass (recoveryTape blue eta) (fun tape => ¬((residualRow G E blue u).Nonempty →
          recoverResult E red blue tape (fun i => productRead G (rowQuery tape i)) u ≠ none)) ≤
            (7 / 8 : ℝ≥0∞) ^ rowTrials n eta := by
      by_cases hrow : (residualRow G E blue u).Nonempty
      · simpa only [hrow, true_implies, not_not] using
          recoverResult_row_failure_le G E hE red blue eta hdis hu hrow
      · simp only [hrow, false_implies, not_true_eq_false, mass_false]
        exact bot_le
    have hu := mass_failure_le_card_mul (recoveryTape blue eta) red
      (fun u tape => (residualRow G E blue u).Nonempty →
        recoverResult E red blue tape (fun i => productRead G (rowQuery tape i)) u ≠ none)
      (fun tape => RowsComplete G E red blue
        (recoverResult E red blue tape (fun i => productRead G (rowQuery tape i))))
      ((7 / 8 : ℝ≥0∞) ^ rowTrials n eta) (fun _ _ h => h) hb
    have hred : (red.card : ℝ≥0∞) ≤ n := by
      exact_mod_cast (show red.card ≤ n by simpa only [Fintype.card_fin] using card_le_univ red)
    exact hu.trans ((mul_le_mul hred le_rfl (by positivity) (by positivity)).trans
      (rowTrials_union_error hn heta))
  · have hn0 : n = 0 := by omega
    subst n
    simp [RowsComplete]

theorem recoverRows_successProb (G : CapacityGraph (Fin n) 1) (E : LearnedEdges n)
    (hE : KnownSubgraph E G) (red blue : Finset (Fin n)) (eta : ℝ)
    (hdis : Disjoint red blue) (heta : 0 < eta) :
    1 - eta / (8 * (n : ℝ)) ≤
      (recoverRows n E red blue eta).successProb (productRead G) (RowsComplete G E red blue) := by
  rw [RTree.successProb_eq]
  exact success_of_failure_le _ _ (by positivity)
    (recoverRows_failure G E hE red blue eta hdis heta)

/-- The tree is chosen from public inputs before the hidden graph. Both its
cap and error guarantee are proved properties of this concrete tree. -/
theorem recoverRows_public (n : ℕ) (E : LearnedEdges n) (red blue : Finset (Fin n))
    (eta : ℝ) (hdis : Disjoint red blue) (heta : 0 < eta) :
    ∃ T : ProductTree n (RowTable n) (recoverBudget n eta),
      (∀ read out, out ∈ (RTree.run read T).support →
        out.2 ≤ logWidth n * rowTrials n eta * (logWidth n + 1)) ∧
      ∀ G : CapacityGraph (Fin n) 1, KnownSubgraph E G →
        (∀ rows ∈ (T.eval (productRead G)).support, ∀ u v, rows u = some v →
          u ∈ red ∧ v ∈ blue ∧ ResidualNeighbor G E u v) ∧
        (∀ rows ∈ (T.eval (productRead G)).support, ∀ u,
          residualRow G E blue u = ∅ → rows u = none) ∧
        mass (T.eval (productRead G)) (fun rows => ¬RowsComplete G E red blue rows) ≤
          ENNReal.ofReal (eta / (8 * (n : ℝ))) := by
  refine ⟨recoverRows n E red blue eta, ?_, ?_⟩
  · intro read out hout
    exact recoverRows_cost E red blue eta read hout
  · intro G hE
    exact ⟨fun _ hr _ _ huv => recoverRows_sound G E hE red blue eta hr huv,
      fun _ hr u he => recoverRows_empty_row G E hE red blue eta hr u he,
      recoverRows_failure G E hE red blue eta hdis heta⟩

open QuantumQueryComplexity
open scoped Matrix
attribute [local instance] ProductPrograms.basisDecidableEq ProductPrograms.workspaceDecidableEq

/-- The actual compiled routine has a fixed physical cut-query schedule. -/
theorem recoverRows_physical_length (E : LearnedEdges n) (red blue : Finset (Fin n)) (eta : ℝ) :
    (productTreeRoutine (recoverRows n E red blue eta)).len =
      12 * productBits n 1 * recoverBudget n eta := rfl

theorem recoverRows_physical_normalized (E : LearnedEdges n)
    (red blue : Finset (Fin n)) (eta : ℝ) (read : Finset (Fin n) → CutAnswer n 1) :
    IsQState ((productTreeRoutine (recoverRows n E red blue eta)).run read *ᵥ
      (productTreeAlg (recoverRows n E red blue eta)).init) :=
  productTreeRoutine_isQState _ read

/-- Exact Born law for the concrete program, not a specification of an
unsupplied recovery oracle. -/
theorem recoverRows_physical_prob (G : CapacityGraph (Fin n) 1) (E : LearnedEdges n)
    (red blue : Finset (Fin n)) (eta : ℝ) (hdis : Disjoint red blue) (rows : RowTable n) :
    (productTreeAlg (recoverRows n E red blue eta)).prob (capacityRead G)
      (physicalQueries n (recoverBudget n eta)) rows =
      (((recoveryTape blue eta).map (fun tape =>
        recoverResult E red blue tape (fun i => productRead G (rowQuery tape i)))) rows).toReal := by
  rw [productTreeAlg_prob]
  change (((recoverRows n E red blue eta).eval (productRead G)) rows).toReal = _
  rw [recoverRows_eval E red blue eta hdis]

theorem recoverRows_physical_successProb (G : CapacityGraph (Fin n) 1) (E : LearnedEdges n)
    (hE : KnownSubgraph E G) (red blue : Finset (Fin n)) (eta : ℝ)
    (hdis : Disjoint red blue) (heta : 0 < eta) :
    1 - eta / (8 * (n : ℝ)) ≤
      goodProb (productTreeAlg (recoverRows n E red blue eta)).readout (RowsComplete G E red blue)
        ((productTreeAlg (recoverRows n E red blue eta)).state (capacityRead G)
          (physicalQueries n (recoverBudget n eta))) := by
  rw [productTreeAlg_successProb]
  exact recoverRows_successProb G E hE red blue eta hdis heta

#print axioms recoveryTape_supported_subset
#print axioms rowQueryIndex_card
#print axioms selectRow_some
#print axioms selectRow_ne_none_iff
#print axioms recoverRows_eval
#print axioms recoverRows_eval_overlap
#print axioms recoverRows_cost
#print axioms decodedTrial_honest
#print axioms decodedTrial_honest_some_iff
#print axioms recoverResult_sound
#print axioms recoverRows_sound
#print axioms recoverRows_empty_row
#print axioms recoverResult_ne_none_of_isolated
#print axioms recoverResult_row_failure_le
#print axioms recoverRows_failure
#print axioms recoverRows_successProb
#print axioms recoverRows_public
#print axioms recoverRows_physical_length
#print axioms recoverRows_physical_normalized
#print axioms recoverRows_physical_prob
#print axioms recoverRows_physical_successProb

end
end CutQueryComplexity.StarContraction2022.Quantum.Forest
