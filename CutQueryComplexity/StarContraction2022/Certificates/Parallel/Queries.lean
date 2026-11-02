import CutQueryComplexity.StarContraction2022.Certificates.ParallelState
import CutQueryComplexity.StarContraction2022.Recovery.Decode
import CutQueryComplexity.Model.RandomizedReduction
import CutQueryComplexity.Probability.Truncation
import CutQueryComplexity.Probability.Expectation

/-! # Actual original-residual queries and sparse recovery

Part of the parallel threshold certificate. No full parallel algorithm,
expected C_P bound, or endpoint is asserted in this module.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Certificates

noncomputable section
open scoped Classical ENNReal

variable {V Q : Type} [Fintype V] [DecidableEq V] [Fintype Q] [DecidableEq Q]
variable {π : PublicQuotient V Q} {r : ℕ}

theorem det_cost_bind {I A O P : Type} {b c : ℕ}
    (T : DTree I A O b) (f : O → DTree I A P c) (read : I → A) :
    (T.bind f).cost read = T.cost read + (f (T.eval read)).cost read := by
  simp only [DTree.cost, DTree.run_bind]

theorem det_cost_cast {I A O : Type} {b c : ℕ}
    (T : DTree I A O b) (h : b = c) (read : I → A) :
    (T.cast h).cost read = T.cost read := by simp only [DTree.cost, DTree.run_cast]

theorem det_cost_pure {I A O : Type} {b : ℕ} (o : O) (read : I → A) :
    (DTree.pure (I := I) (A := A) (q := b) o).cost read = 0 := by
  simp only [DTree.cost, DTree.run_pure]

theorem det_cost_map {I A O P : Type} {b : ℕ}
    (T : DTree I A O b) (f : O → P) (read : I → A) :
    (T.map f).cost read = T.cost read := by simp only [DTree.cost, DTree.run_map]

set_option backward.isDefEq.respectTransparency false in
private theorem rtree_substitute_run_exact {I A J B O : Type} {q k : ℕ}
    (call : J → DTree I A B k) (read : I → A) (virtual : J → B)
    (hcall : ∀ j, DTree.run read (call j) = (virtual j, k)) (T : RTree J B O q) :
    RTree.run read (T.substitute call) =
      (RTree.run virtual T).map (fun out => (out.1, out.2 * k)) := by
  induction q with
  | zero => simp [RTree.substitute, RTree.run_pure, RTree.run, PMF.map_comp, Function.comp_def]
  | succ q ih =>
      simp only [RTree.substitute, RTree.run_mix, PMF.bind_map, Function.comp_def,
        RTree.run, PMF.map_bind]
      congr 1
      funext action
      rcases action with o | ⟨j, next⟩
      · simp [RTree.run_pure, PMF.pure_map]
      · simp only [RTree.run_cast, RTree.run_bind, RTree.run_ofDeterministic, hcall,
          PMF.pure_bind, ih, PMF.map_comp, Function.comp_def]
        congr 1
        funext out
        congr 1
        ring

namespace ParallelState

section SparseResidual

variable {R C : Type} [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C]

/-- Only the original residual is Boolean. This hidden table is used in proofs;
the public decoder below takes the state and endpoint embeddings alone. -/
def residualMatrix (s : ParallelState π r) (row : R ↪ V) (col : C ↪ V)
    (G : SimpleInput V) : Recovery.BooleanMatrix R C :=
  fun u v => decide (0 < (G.toWeighted.subtract s.usedGraph).w (row u) (col v))

theorem residualMatrix_entry (s : ParallelState π r) (row : R ↪ V) (col : C ↪ V)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted) (u : R) (v : C) :
    (if s.residualMatrix row col G u v then (1 : ℝ) else 0) =
      (G.toWeighted.subtract s.usedGraph).w (row u) (col v) := by
  rcases s.residual_unit G hs (row u) (col v) with hz | ho
  · simp [residualMatrix, hz]
  · simp [residualMatrix, ho]

theorem residualMatrix_bilinear (s : ParallelState π r) (row : R ↪ V) (col : C ↪ V)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (q : Recovery.BipartiteQuery R C) :
    (Recovery.bilinear (s.residualMatrix row col G) q : ℝ) =
      (G.toWeighted.subtract s.usedGraph).cross (q.1.map row) (q.2.map col) := by
  simp only [Recovery.bilinear, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero, WeightedGraph.cross, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  exact s.residualMatrix_entry row col G hs u v

theorem residualMatrix_row (s : ParallelState π r) (row : R ↪ V) (col : C ↪ V)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted) (u : R) :
    (Recovery.measure Finset.univ
      (Recovery.rowVector (s.residualMatrix row col G) u) : ℝ) =
      (G.toWeighted.subtract s.usedGraph).cross {row u} (Finset.univ.map col) := by
  simpa only [Recovery.bilinear, Finset.sum_singleton, Finset.map_singleton,
    Recovery.measure, Recovery.rowVector] using
    s.residualMatrix_bilinear row col G hs ({u}, Finset.univ)

/-- Each decoder measurement is implemented by three genuine original cuts.
The known used capacities are subtracted locally before validation. -/
def residualBilinearCall (s : ParallelState π r) (row : R ↪ V) (col : C ↪ V)
    (q : Recovery.BipartiteQuery R C) : DTree (Finset V) ℝ ℝ 3 :=
  s.residualCrossQuery (q.1.map row) (q.2.map col)

theorem residualBilinearCall_honest (s : ParallelState π r)
    (row : R ↪ V) (col : C ↪ V) (hdis : ∀ u v, row u ≠ col v)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (q : Recovery.BipartiteQuery R C) :
    (s.residualBilinearCall row col q).eval G.toWeighted.cut =
      (Recovery.bilinear (s.residualMatrix row col G) q : ℝ) := by
  rw [residualBilinearCall, s.residualCrossQuery_eval G.toWeighted hs,
    ← s.residualMatrix_bilinear row col G hs q]
  apply Finset.disjoint_left.mpr
  intro v hv hw
  obtain ⟨a, ha, hea⟩ := Finset.mem_map.mp hv
  obtain ⟨b, hb, heb⟩ := Finset.mem_map.mp hw
  exact hdis a b (hea.trans heb.symm)

/-- Exact cost is true on every answer path, not a supplied adapter bound. -/
theorem residualBilinearCall_run (s : ParallelState π r) (row : R ↪ V) (col : C ↪ V)
    (read : Finset V → ℝ) (q : Recovery.BipartiteQuery R C) :
    DTree.run read (s.residualBilinearCall row col q) =
      ((s.residualBilinearCall row col q).eval read, 3) := rfl

/-- Randomized recovery is compiled through the same actual three original
residual cuts as the deterministic decoder. The constructor takes no graph. -/
def simulateResidual {O : Type} {b : ℕ} (s : ParallelState π r)
    (row : R ↪ V) (col : C ↪ V) (T : RTree (Recovery.BipartiteQuery R C) ℝ O b) :
    RTree (Finset V) ℝ O (b * 3) := T.substitute (s.residualBilinearCall row col)

theorem simulateResidual_run {O : Type} {b : ℕ} (s : ParallelState π r)
    (row : R ↪ V) (col : C ↪ V) (T : RTree (Recovery.BipartiteQuery R C) ℝ O b)
    (read : Finset V → ℝ) :
    RTree.run read (s.simulateResidual row col T) =
      (RTree.run (fun q => (s.residualBilinearCall row col q).eval read) T).map
        (fun out => (out.1, out.2 * 3)) :=
  rtree_substitute_run_exact _ _ _ (s.residualBilinearCall_run row col read) T

theorem simulateResidual_honest {O : Type} {b : ℕ} (s : ParallelState π r)
    (row : R ↪ V) (col : C ↪ V) (hdis : ∀ u v, row u ≠ col v)
    (T : RTree (Recovery.BipartiteQuery R C) ℝ O b)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted) :
    RTree.run G.toWeighted.cut (s.simulateResidual row col T) =
      (RTree.run (fun q => (Recovery.bilinear (s.residualMatrix row col G) q : ℝ)) T).map
        (fun out => (out.1, out.2 * 3)) := by
  rw [s.simulateResidual_run row col T]
  have he : (fun q => (s.residualBilinearCall row col q).eval G.toWeighted.cut) =
      (fun q => (Recovery.bilinear (s.residualMatrix row col G) q : ℝ)) :=
    funext (s.residualBilinearCall_honest row col hdis G hs)
  rw [he]

/-- The sharp virtual-recovery estimate incurs exactly the proved factor
three when implemented by cuts, for every supplied original oracle. -/
theorem simulateResidual_expected {O : Type} {b : ℕ} (s : ParallelState π r)
    (row : R ↪ V) (col : C ↪ V) (T : RTree (Recovery.BipartiteQuery R C) ℝ O b)
    (read : Finset V → ℝ) :
    (s.simulateResidual row col T).expectedQueries read =
      3 * T.expectedQueries (fun q => (s.residualBilinearCall row col q).eval read) := by
  change CutQueryComplexity.Probability.expect
    (RTree.run read (s.simulateResidual row col T)) (fun out => (out.2 : ℝ≥0∞)) = _
  rw [s.simulateResidual_run row col T, CutQueryComplexity.Probability.expect_map]
  simp only [Nat.cast_mul, Nat.cast_ofNat, CutQueryComplexity.Probability.expect_mul_const]
  exact mul_comm _ _

theorem simulateResidual_every_oracle {O : Type} {b : ℕ} (s : ParallelState π r)
    (row : R ↪ V) (col : C ↪ V) (T : RTree (Recovery.BipartiteQuery R C) ℝ O b)
    (read : Finset V → ℝ) {out : O × ℕ}
    (hout : out ∈ (RTree.run read (s.simulateResidual row col T)).support) :
    out.2 ≤ b * 3 := RTree.cost_le _ _ hout

/-- Actual sparse measurement and finite decoding, including the small-row
and low-degree cases. No linear equation other than a compiled cut is used. -/
def residualDecode (s : ParallelState π r) (row : R ↪ V) (col : C ↪ V) (ell : ℕ) :
    DTree (Finset V) ℝ (Option (Recovery.BooleanMatrix R C))
      (Recovery.sparseRawBudget R C ell * 3) :=
  (Recovery.sparseBilinearProgram ell).substitute (s.residualBilinearCall row col)

theorem residualDecode_correct (s : ParallelState π r) (row : R ↪ V) (col : C ↪ V)
    (ell : ℕ) (hdis : ∀ u v, row u ≠ col v)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (hdegree : Recovery.RowSparse ell (s.residualMatrix row col G)) :
    (s.residualDecode row col ell).eval G.toWeighted.cut =
      some (s.residualMatrix row col G) := by
  rw [residualDecode, DTree.eval_substitute]
  have he : (fun q => (s.residualBilinearCall row col q).eval G.toWeighted.cut) =
      (fun q => (Recovery.bilinear (s.residualMatrix row col G) q : ℝ)) :=
    funext (s.residualBilinearCall_honest row col hdis G hs)
  rw [he]
  exact Recovery.sparseBilinearProgram_correct _ hdegree

theorem residualDecode_cost (s : ParallelState π r) (row : R ↪ V) (col : C ↪ V)
    (ell : ℕ) (read : Finset V → ℝ) :
    (s.residualDecode row col ell).cost read ≤ Recovery.sparseRawBudget R C ell * 3 :=
  DTree.cost_le _ _

/-- The sharp row-count denominator survives the three-cut implementation. -/
theorem residualDecode_cost_bound (s : ParallelState π r) (row : R ↪ V) (col : C ↪ V)
    (ell : ℕ) (hm : 1 ≤ Fintype.card R) (hell : 1 ≤ ell)
    (heln : ell ≤ Fintype.card C) (read : Finset V → ℝ) :
    ((s.residualDecode row col ell).cost read : ℝ) ≤
      50331648 * ell * Fintype.card R * Real.log (2 * (Fintype.card C : ℝ)) /
        Real.log (2 * (Fintype.card R : ℝ)) := by
  have hcost : ((s.residualDecode row col ell).cost read : ℝ) ≤
      (Recovery.sparseRawBudget R C ell : ℝ) * 3 := by
    exact_mod_cast s.residualDecode_cost row col ell read
  have hb := Recovery.sparseRawBudget_bound (R := R) (C := C) ell hm hell heln
  have hh := mul_le_mul_of_nonneg_right hb (by norm_num : (0 : ℝ) ≤ 3)
  exact hcost.trans (by convert hh using 1 <;> ring)

private theorem rowSparse_dimension (M : Recovery.BooleanMatrix R C) :
    Recovery.RowSparse (Fintype.card C) M := by
  intro u
  calc
    Recovery.measure Finset.univ (Recovery.rowVector M u) ≤
        ∑ _c : C, (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro c hc
      simp only [Recovery.rowVector]
      split <;> omega
    _ = _ := by simp

def lowDegreeResidual (s : ParallelState π r) (row : R ↪ V) (col : C ↪ V) :
    DTree (Finset V) ℝ (Option (Recovery.BooleanMatrix R C))
      (Recovery.sparseRawBudget R C (min 20 (Fintype.card C)) * 3) :=
  s.residualDecode row col (min 20 (Fintype.card C))

/-- Degrees below 10, and in fact every row of degree at most 20, use the
proved sparse decoder directly. Even one representative is covered. -/
theorem lowDegreeResidual_correct (s : ParallelState π r) (row : R ↪ V) (col : C ↪ V)
    (hdis : ∀ u v, row u ≠ col v)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (hdegree : Recovery.RowSparse 20 (s.residualMatrix row col G)) :
    (s.lowDegreeResidual row col).eval G.toWeighted.cut =
      some (s.residualMatrix row col G) := by
  apply s.residualDecode_correct row col _ hdis G hs
  intro u
  exact le_min (hdegree u) (rowSparse_dimension _ u)

theorem lowDegreeResidual_cost (s : ParallelState π r) (row : R ↪ V) (col : C ↪ V)
    (hm : 1 ≤ Fintype.card R) (hc : 1 ≤ Fintype.card C) (read : Finset V → ℝ) :
    ((s.lowDegreeResidual row col).cost read : ℝ) ≤
      1006632960 * Fintype.card R * Real.log (2 * (Fintype.card C : ℝ)) /
        Real.log (2 * (Fintype.card R : ℝ)) := by
  have hmR : (1 : ℝ) ≤ Fintype.card R := by exact_mod_cast hm
  have hcR : (1 : ℝ) ≤ Fintype.card C := by exact_mod_cast hc
  have hd : 0 < Real.log (2 * (Fintype.card R : ℝ)) := Real.log_pos (by linarith)
  have hl : 0 ≤ Real.log (2 * (Fintype.card C : ℝ)) := Real.log_nonneg (by linarith)
  have hell : ((min 20 (Fintype.card C) : ℕ) : ℝ) ≤ 20 := by
    exact_mod_cast min_le_left 20 (Fintype.card C)
  apply (s.residualDecode_cost_bound row col (min 20 (Fintype.card C)) hm
    (by omega) (min_le_right _ _) read).trans
  calc
    _ ≤ 50331648 * (20 : ℝ) * Fintype.card R * Real.log (2 * (Fintype.card C : ℝ)) /
        Real.log (2 * (Fintype.card R : ℝ)) := by gcongr
    _ = _ := by ring

/-- Query all row degrees before selecting a low-degree bucket. Only derived
residual bilinear values are tested; original cut answers are unrestricted. -/
def residualDegrees (s : ParallelState π r) (row : R ↪ V) (col : C ↪ V) :
    DTree (Finset V) ℝ (R → ℝ) (Fintype.card R * 3) :=
  (DTree.queryAll (fun u : R => (({u}, Finset.univ) : Recovery.BipartiteQuery R C))
    (fun _ => (0 : ℝ))).substitute (s.residualBilinearCall row col)

theorem residualDegrees_honest (s : ParallelState π r) (row : R ↪ V) (col : C ↪ V)
    (hdis : ∀ u v, row u ≠ col v) (G : SimpleInput V)
    (hs : s.usedGraph.IsSubgraph G.toWeighted) :
    (s.residualDegrees row col).eval G.toWeighted.cut =
      fun u => (Recovery.measure Finset.univ
        (Recovery.rowVector (s.residualMatrix row col G) u) : ℝ) := by
  rw [residualDegrees, DTree.eval_substitute]
  simp only [DTree.eval, DTree.queryAll_run]
  funext u
  rw [← DTree.eval, s.residualBilinearCall_honest row col hdis G hs]
  simp only [Recovery.bilinear, Finset.sum_singleton, Recovery.measure, Recovery.rowVector]

/-- A complete low-degree branch, with its degree premise discharged by
actual queries. A high-degree row causes explicit rejection. -/
def checkedLowDegreeResidual (s : ParallelState π r) (row : R ↪ V) (col : C ↪ V) :
    DTree (Finset V) ℝ (Option (Recovery.BooleanMatrix R C))
      (Fintype.card R * 3 + Recovery.sparseRawBudget R C (min 20 (Fintype.card C)) * 3) :=
  (s.residualDegrees row col).bind fun degree =>
    if ∀ u, degree u ≤ 20 then s.lowDegreeResidual row col else DTree.pure none

/-- Every successful low-degree output is the actual original residual
matrix; no sparsity premise is needed by this soundness statement. -/
theorem checkedLowDegreeResidual_sound (s : ParallelState π r)
    (row : R ↪ V) (col : C ↪ V) (hdis : ∀ u v, row u ≠ col v)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    {M : Recovery.BooleanMatrix R C}
    (hout : (s.checkedLowDegreeResidual row col).eval G.toWeighted.cut = some M) :
    M = s.residualMatrix row col G := by
  rw [checkedLowDegreeResidual, DTree.eval_bind,
    s.residualDegrees_honest row col hdis G hs] at hout
  split at hout
  next hdegree =>
    have hd : Recovery.RowSparse 20 (s.residualMatrix row col G) := by
      intro u
      have hu := hdegree u
      change (Recovery.measure Finset.univ
        (Recovery.rowVector (s.residualMatrix row col G) u) : ℝ) ≤ 20 at hu
      exact_mod_cast hu
    rw [s.lowDegreeResidual_correct row col hdis G hs hd] at hout
    exact (Option.some.inj hout).symm
  next hdegree => simp at hout

theorem checkedLowDegreeResidual_correct (s : ParallelState π r)
    (row : R ↪ V) (col : C ↪ V) (hdis : ∀ u v, row u ≠ col v)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (hdegree : Recovery.RowSparse 20 (s.residualMatrix row col G)) :
    (s.checkedLowDegreeResidual row col).eval G.toWeighted.cut =
      some (s.residualMatrix row col G) := by
  rw [checkedLowDegreeResidual, DTree.eval_bind,
    s.residualDegrees_honest row col hdis G hs]
  have hd : ∀ u, (Recovery.measure Finset.univ
      (Recovery.rowVector (s.residualMatrix row col G) u) : ℝ) ≤ 20 := by
    intro u
    exact_mod_cast hdegree u
  rw [if_pos hd]
  exact s.lowDegreeResidual_correct row col hdis G hs hdegree

theorem checkedLowDegreeResidual_cost (s : ParallelState π r)
    (row : R ↪ V) (col : C ↪ V) (read : Finset V → ℝ) :
    (s.checkedLowDegreeResidual row col).cost read ≤
      Fintype.card R * 3 + Recovery.sparseRawBudget R C (min 20 (Fintype.card C)) * 3 :=
  DTree.cost_le _ _

/-- The operational degree test adds only three original queries per row
to the sharp sparse-decoder estimate. It does not remove its denominator. -/
theorem checkedLowDegreeResidual_cost_bound (s : ParallelState π r)
    (row : R ↪ V) (col : C ↪ V) (hm : 1 ≤ Fintype.card R)
    (hc : 1 ≤ Fintype.card C) (read : Finset V → ℝ) :
    ((s.checkedLowDegreeResidual row col).cost read : ℝ) ≤
      3 * Fintype.card R +
        1006632960 * Fintype.card R * Real.log (2 * (Fintype.card C : ℝ)) /
          Real.log (2 * (Fintype.card R : ℝ)) := by
  have hd : ((s.residualDegrees row col).cost read : ℝ) ≤ 3 * Fintype.card R := by
    have hh := DTree.cost_le (s.residualDegrees row col) read
    exact_mod_cast (hh.trans_eq (Nat.mul_comm _ _))
  rw [checkedLowDegreeResidual, det_cost_bind, Nat.cast_add]
  split
  · exact add_le_add hd (s.lowDegreeResidual_cost row col hm hc read)
  · rw [det_cost_pure, Nat.cast_zero, add_zero]
    apply hd.trans
    have hmR : (1 : ℝ) ≤ Fintype.card R := by exact_mod_cast hm
    have hcR : (1 : ℝ) ≤ Fintype.card C := by exact_mod_cast hc
    have hlogm : 0 < Real.log (2 * (Fintype.card R : ℝ)) := Real.log_pos (by linarith)
    have hlogc : 0 ≤ Real.log (2 * (Fintype.card C : ℝ)) := Real.log_nonneg (by linarith)
    exact le_add_of_nonneg_right (by positivity)

end SparseResidual

/-- A residual original row is Boolean and therefore has a natural bounded sum. -/
theorem residual_row_count (s : ParallelState π r) (G : SimpleInput V)
    (hs : s.usedGraph.IsSubgraph G.toWeighted) (v : V) (A : Finset V) :
    ∃ k : ℕ, k ≤ Fintype.card V ∧
      (G.toWeighted.subtract s.usedGraph).cross {v} A = k := by
  let H := G.toWeighted.subtract s.usedGraph
  let N := A.filter (fun w => 0 < H.w v w)
  refine ⟨N.card, (Finset.card_filter_le _ _).trans (Finset.card_le_univ A), ?_⟩
  change (∑ u ∈ ({v} : Finset V), ∑ w ∈ A, H.w u w) = (N.card : ℝ)
  rw [Finset.sum_singleton]
  calc
    _ = ∑ w ∈ A, if 0 < H.w v w then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro w hw
      rcases s.residual_unit G hs v w with hz | ho
      · change H.w v w = 0 at hz
        simp [hz]
      · change H.w v w = 1 at ho
        simp [ho]
    _ = _ := by simpa only [N] using
      (Finset.sum_boole (R := ℝ) (fun w => 0 < H.w v w) A)

end ParallelState

#print axioms ParallelState.residualMatrix_entry
#print axioms ParallelState.residualMatrix_bilinear
#print axioms ParallelState.residualMatrix_row
#print axioms ParallelState.residualBilinearCall_honest
#print axioms ParallelState.residualBilinearCall_run
#print axioms ParallelState.simulateResidual_run
#print axioms ParallelState.simulateResidual_honest
#print axioms ParallelState.simulateResidual_expected
#print axioms ParallelState.simulateResidual_every_oracle
#print axioms ParallelState.residualDecode_correct
#print axioms ParallelState.residualDecode_cost_bound
#print axioms ParallelState.lowDegreeResidual_correct
#print axioms ParallelState.lowDegreeResidual_cost
#print axioms ParallelState.residualDegrees_honest
#print axioms ParallelState.checkedLowDegreeResidual_sound
#print axioms ParallelState.checkedLowDegreeResidual_correct
#print axioms ParallelState.checkedLowDegreeResidual_cost
#print axioms ParallelState.checkedLowDegreeResidual_cost_bound
#print axioms ParallelState.residual_row_count

end
end CutQueryComplexity.StarContraction2022.Certificates
