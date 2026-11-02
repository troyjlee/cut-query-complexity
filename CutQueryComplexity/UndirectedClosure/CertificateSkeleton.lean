import CutQueryComplexity.UndirectedClosure.ConicSupport
import CutQueryComplexity.Sparsification.OutputEdges
import CutQueryComplexity.Certificate.Main
import CutQueryComplexity.TwoRespecting.TreeCover

/-! # Public sparse completion and the certificate-to-skeleton bridge

The decoder receives only queried shores and their answers.  Its output has
at most as many unordered positive edges as queried shores, even on infeasible
transcripts, where it returns zero.  Hidden graphs occur only in correctness
proofs.  Neither a linear-programming oracle nor containment in a hidden
support is an input to this construction.
-/

set_option autoImplicit false

namespace CutQueryComplexity.UndirectedClosure

noncomputable section
open scoped Classical
open Finset WeightedGraph Certificate

variable {V : Type} [Fintype V] [DecidableEq V]

theorem cut_finiteSum {E : Type*} (t : Finset E) (F : E → WeightedGraph V)
    (S : Finset V) : (finiteSum t F).cut S = ∑ e ∈ t, (F e).cut S := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [finiteSum, cut]
  | @insert e t he ih =>
    have hadd : finiteSum (insert e t) F = F e + finiteSum t F := by
      ext u v
      simp [finiteSum, he]
    rw [hadd, cut_addition, ih, sum_insert he]

omit [DecidableEq V] in
theorem finiteSum_edgeCount_le {E : Type*} (t : Finset E) (F : E → WeightedGraph V)
    (hF : ∀ e ∈ t, (F e).edgeCount ≤ 1) : (finiteSum t F).edgeCount ≤ t.card := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have hzero : finiteSum (∅ : Finset E) F = 0 := by ext; simp [finiteSum]
    simp [hzero, edgeCount_zero]
  | @insert e t he ih =>
    have hadd : finiteSum (insert e t) F = F e + finiteSum t F := by
      ext u v
      simp [finiteSum, he]
    have hrest := ih (fun i hi => hF i (mem_insert_of_mem hi))
    have hedge := hF e (mem_insert_self _ _)
    rw [hadd, card_insert_of_notMem he]
    exact (edgeCount_add_le _ _).trans (by omega)

/-- The cut column of a named unit edge. Both orientations name the same
undirected edge; the output edge-count bound does not count them twice. -/
def cutColumn (e : EdgeIndex V) (S : Finset V) : ℝ :=
  (edgeGraph e 1 zero_le_one).cut S

theorem cut_edgeGraph_eq_mul_column (e : EdgeIndex V) (x : ℝ) (hx : 0 ≤ x)
    (S : Finset V) : (edgeGraph e x hx).cut S = x * cutColumn e S := by
  unfold cutColumn
  rw [cut_edgeGraph, cut_edgeGraph]
  split <;> simp

/-- Existing counted-edge decomposition, specialized to all original edges.
The coefficients are half the weight on each orientation. -/
theorem full_bucket_graph (G : WeightedGraph V) :
    finiteSum univ (fun e => edgeGraph e (bucketWeight G id univ e)
      (bucketWeight_nonneg G id univ e)) = G := by
  have hsum : finiteSum univ (fun e => edgeGraph e (bucketWeight G id univ e)
      (bucketWeight_nonneg G id univ e)) = bucketGraph G id univ := by
    convert (bucketWeight_graph G (id : V → V) (univ : Finset V)) using 1 <;>
      congr 1 <;> ext <;> simp
  rw [hsum]
  ext u v
  by_cases huv : u = v
  · subst v
    simp [bucketGraph, G.diag]
  · simp [bucketGraph, huv]

/-- Feasibility is a property of public shores and answers. -/
def TranscriptFeasible (Q : Finset (Finset V)) (answers : Q → ℝ) : Prop :=
  ∃ F : WeightedGraph V, ∀ S : Q, F.cut S.val = answers S

/-- Every feasible cut transcript has a nonnegative completion with at most
one positive undirected edge per measured shore. -/
theorem exists_sparse_completion (Q : Finset (Finset V)) (answers : Q → ℝ)
    (hfeas : TranscriptFeasible Q answers) :
    ∃ F : WeightedGraph V, F.edgeCount ≤ Q.card ∧
      ∀ S : Q, F.cut S.val = answers S := by
  obtain ⟨G, hG⟩ := hfeas
  let A : EdgeIndex V → Q → ℝ := fun e S => cutColumn e S.val
  have hrows : ∃ x : EdgeIndex V → ℝ, (∀ e, 0 ≤ x e) ∧
      ∀ S : Q, (∑ e, x e * A e S) = answers S := by
    refine ⟨bucketWeight G id univ, bucketWeight_nonneg G id univ, ?_⟩
    intro S
    calc
      (∑ e, bucketWeight G id univ e * A e S) =
          (finiteSum univ (fun e => edgeGraph e (bucketWeight G id univ e)
            (bucketWeight_nonneg G id univ e))).cut S.val := by
        rw [cut_finiteSum]
        apply sum_congr rfl
        intro e _
        exact (cut_edgeGraph_eq_mul_column e _ _ _).symm
      _ = answers S := by rw [full_bucket_graph]; exact hG S
  obtain ⟨t, y, ht, hy, hanswer⟩ := exists_nonneg_sparse_rows A answers hrows
  refine ⟨finiteSum t (fun e => edgeGraph e (y e) (hy e)), ?_, ?_⟩
  · exact (finiteSum_edgeCount_le t _ (fun e _ => edgeCount_edgeGraph_le e _ _)).trans
      (by simpa only [Fintype.card_coe] using ht)
  · intro S
    rw [cut_finiteSum]
    simpa only [cut_edgeGraph_eq_mul_column, A] using hanswer S

/-- Offline decoder of a public transcript. Infeasible answers use the zero
graph; no hidden graph occurs among the selector's arguments. -/
def sparseCompletion (Q : Finset (Finset V)) (answers : Q → ℝ) : WeightedGraph V :=
  if h : TranscriptFeasible Q answers then Classical.choose (exists_sparse_completion Q answers h)
  else 0

/-- The support cap holds on every transcript, including inconsistent ones. -/
theorem sparseCompletion_edgeCount (Q : Finset (Finset V)) (answers : Q → ℝ) :
    (sparseCompletion Q answers).edgeCount ≤ Q.card := by
  unfold sparseCompletion
  split_ifs with h
  · exact (Classical.choose_spec (exists_sparse_completion Q answers h)).1
  · simp [edgeCount_zero]

theorem sparseCompletion_answers (Q : Finset (Finset V)) (answers : Q → ℝ)
    (hfeas : TranscriptFeasible Q answers) (S : Q) :
    (sparseCompletion Q answers).cut S.val = answers S := by
  unfold sparseCompletion
  rw [dite_eq_left hfeas]
  exact (Classical.choose_spec (exists_sparse_completion Q answers hfeas)).2 S

theorem sparseCompletion_consistent (G : WeightedGraph V) (Q : Finset (Finset V)) :
    Consistent G (sparseCompletion Q (fun S => G.cut S.val)) Q := by
  intro S hS
  exact sparseCompletion_answers Q _ ⟨G, fun _ => rfl⟩ ⟨S, hS⟩

/-- Once the transcript is supplied, completion uses zero further queries. -/
def sparseCompletionProg (Q : Finset (Finset V)) (answers : Q → ℝ) :
    DTree (Finset V) ℝ (WeightedGraph V) 0 := DTree.pure (sparseCompletion Q answers)

theorem sparseCompletionProg_eval (Q : Finset (Finset V)) (answers : Q → ℝ)
    (read : Finset V → ℝ) :
    (sparseCompletionProg Q answers).eval read = sparseCompletion Q answers := rfl

theorem sparseCompletionProg_cost (Q : Finset (Finset V)) (answers : Q → ℝ)
    (read : Finset V → ℝ) : (sparseCompletionProg Q answers).cost read = 0 := rfl

theorem minCut_cut_eq_value {G : WeightedGraph V} {S : Finset V} (hS : IsMinCut G S) :
    G.cut S = mincutValue G := by
  obtain ⟨T, hT, hval⟩ := exists_isMinCut G ⟨S, (mem_properShores S).mpr hS.1⟩
  exact le_antisymm (hval ▸ hS.2 T hT.1) (mincutValue_le G hS.1)

/-- Paper 01, Proposition `bridge`: a weighted-robust certificate containing
an optimum gives an exact sparse completion, and a weak skeleton when the
original minimum is positive. The query family is supplied, not discovered. -/
theorem certificate_to_skeleton (G : WeightedGraph V) (Q : Finset (Finset V))
    (S : Finset V) (hQ : IsMinCutCertificate G Q) (hS : IsMinCut G S) (hmem : S ∈ Q) :
    let F := sparseCompletion Q (fun T => G.cut T.val)
    F.edgeCount ≤ Q.card ∧ Consistent G F Q ∧
      mincutValue F = mincutValue G ∧ F.cut S = mincutValue G ∧
      (0 < mincutValue G → TwoRespecting.IsWeakSkeleton G F) := by
  dsimp only
  have hc := sparseCompletion_consistent G Q
  have hv := hQ _ hc
  have hs : (sparseCompletion Q (fun T => G.cut T.val)).cut S = mincutValue G :=
    (hc S hmem).trans (minCut_cut_eq_value hS)
  refine ⟨sparseCompletion_edgeCount Q _, hc, hv, hs, ?_⟩
  intro hpos
  refine ⟨by rw [hv]; exact hpos, S, hS, ?_⟩
  rw [hs, hv]
  linarith

/-- The repository's witness certificates instantiate the bridge directly. -/
theorem witnessCertificate_to_skeleton (G : WeightedGraph V) (Q : Finset (Finset V))
    (S : Finset V) (hQ : IsMinCutWitnessCertificate G Q S) :
    let F := sparseCompletion Q (fun T => G.cut T.val)
    F.edgeCount ≤ Q.card ∧ Consistent G F Q ∧
      mincutValue F = mincutValue G ∧ F.cut S = mincutValue G ∧
      (0 < mincutValue G → TwoRespecting.IsWeakSkeleton G F) :=
  certificate_to_skeleton G Q S hQ.isMinCutCertificate
    (hQ.2 G (fun _ _ => rfl)) hQ.1

/-- Near-linear certificates yield graph-dependent near-linear sparse
consistent skeletons. This does not select the certificate by queries. -/
theorem exists_certificate_sparse_skeleton (G : WeightedGraph V)
    (hn : 2 ≤ Fintype.card V) (hpos : 0 < mincutValue G) :
    ∃ Q : Finset (Finset V), Q.card ≤
      18 * Fintype.card V * (Nat.clog 2 (2 * Fintype.card V)) ^ 2 ∧
      (sparseCompletion Q (fun S => G.cut S.val)).edgeCount ≤ Q.card ∧
      Consistent G (sparseCompletion Q (fun S => G.cut S.val)) Q ∧
      TwoRespecting.IsWeakSkeleton G (sparseCompletion Q (fun S => G.cut S.val)) := by
  obtain ⟨Q, S, hcard, hQ⟩ := exists_minCut_witnessCertificate G hn
  have h := witnessCertificate_to_skeleton G Q S hQ
  exact ⟨Q, hcard, h.1, h.2.1, h.2.2.2.2 hpos⟩

#print axioms exists_sparse_completion
#print axioms sparseCompletion_edgeCount
#print axioms sparseCompletion_answers
#print axioms sparseCompletion_consistent
#print axioms sparseCompletionProg_eval
#print axioms sparseCompletionProg_cost
#print axioms certificate_to_skeleton
#print axioms witnessCertificate_to_skeleton
#print axioms exists_certificate_sparse_skeleton

end
end CutQueryComplexity.UndirectedClosure
