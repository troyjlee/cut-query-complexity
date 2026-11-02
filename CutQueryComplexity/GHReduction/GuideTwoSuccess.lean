import CutQueryComplexity.GHReduction.GuideTwoProgram

/-! # Semantic success conditions of the concrete guide branches

These propositions are used only in proofs about program outputs. In particular,
they are not additional algorithmic inputs to `CanonicalSTFamily`.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical ENNReal
open Probability WeightedGraph

variable {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]

def GuideTwoSuccess (G : WeightedGraph V) (T : GuideTree V N) (output : V → Option ℝ) : Prop :=
  (∀ t, EstimateAbove (stValue G t T.source) (output t)) ∧
    ∀ t ∈ T.realVertices, (∃ S, IsSTMinCut G t T.source S ∧ T.RespectsCut S 2) →
      output t = some (stValue G t T.source)

def HasPruningWitness (G : WeightedGraph V) (T : GuideTree V N) (t : N) : Prop :=
  ∃ keep delete : frontierProxies T.tree T.centroid,
    keep ≠ delete ∧ T.sourceNode ∉ frontierBranch T.tree T.centroid delete ∧
    t ∈ frontierBranch T.tree T.centroid keep ∧
    ∃ S : Finset V, IsSTMinCut G (T.label t) T.source S ∧
      ∃ A : Finset N, (∀ v ∈ T.real, v ∈ A ↔ T.label v ∈ S) ∧
        (T.tree.crossSet A).card ≤ 2 ∧
        ∃ e ∈ T.tree.crossSet A, branchTouchesEdge T.tree T.centroid delete e

def PruningSuccess (G : WeightedGraph V) (T : GuideTree V N) (output : V → Option ℝ) : Prop :=
  (∀ t, EstimateAbove (stValue G t T.source) (output t)) ∧
    ∀ t ∈ T.real, HasPruningWitness G T t → output (T.label t) = some (stValue G (T.label t) T.source)

theorem guidePruneTrialsTree_simultaneous {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) (trials : ℕ) :
    mass ((guidePruneTrialsTree family n trials T).eval G.cut)
      (fun output => ¬PruningSuccess G T output) ≤
        (T.real.card : ℝ≥0∞) * ENNReal.ofReal (3 / 4 : ℝ) ^ trials := by
  apply mass_failure_le_card_mul _ T.real
    (fun t output => HasPruningWitness G T t →
      output (T.label t) = some (stValue G (T.label t) T.source))
    (PruningSuccess G T) _
  · intro output hout hgood
    exact ⟨guidePruneTrialsTree_above family G hG T hvn hQ trials hout, hgood⟩
  · intro t ht
    by_cases hw : HasPruningWitness G T t
    · obtain ⟨keep, delete, hne, hs, htkeep, S, hS, A, hA, hk, e, he, heB⟩ := hw
      have h := guidePruneTrialsTree_failure_le family G hG T hvn hQ trials keep delete
        hne hs t ht htkeep S hS A hA hk e he heB
      apply le_trans (mass_mono _ ?_) h
      intro output hbad heq
      exact hbad (fun _ => heq)
    · simp [hw]

def SourceBranchSuccess (G : WeightedGraph V) (T : GuideTree V N) (output : V → Option ℝ) : Prop :=
  if hs : T.sourceNode ≠ T.centroid then
    SourceSwitchSuccess G T (frontierBranch T.tree T.centroid (T.sourceBranch hs)) output
  else ∀ t, output t = none

theorem SourceBranchSuccess.above (G : WeightedGraph V) (T : GuideTree V N)
    {output : V → Option ℝ} (h : SourceBranchSuccess G T output) (t : V) :
    EstimateAbove (stValue G t T.source) (output t) := by
  by_cases hs : T.sourceNode ≠ T.centroid
  · rw [SourceBranchSuccess, dite_eq_left hs] at h
    exact h.1 t
  · rw [SourceBranchSuccess, dite_eq_right hs] at h
    intro value hvalue
    rw [h t] at hvalue
    cases hvalue

theorem guideSourceBranchTree_failure_le {M n scale : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (hnscale : n ≤ scale) (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (levels exponent : ℕ) (hlevels : thresholdLevels n ≤ levels) :
    mass ((guideSourceBranchTree family n T levels scale exponent).eval G.cut)
      (fun output => ¬SourceBranchSuccess G T output) ≤
        (Nat.clog 2 (M + 1) : ℝ≥0∞) * ((((scale + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ exponent) := by
  by_cases hs : T.sourceNode ≠ T.centroid
  · unfold guideSourceBranchTree guideSwitchBudget
    rw [dite_eq_left hs]
    simp_rw [SourceBranchSuccess, dite_eq_left hs]
    apply guideSwitchTree_failure_le family hvn hQ hnscale G hG T _ levels exponent hlevels
    · exact mem_frontierProxy_branch T.tree T.centroid T.sourceNode hs
    · exact frontierBranch_isCentroidBranch T.tree T.centroid _
    · exact T.outside_branch_nonempty _
  · unfold guideSourceBranchTree guideSwitchBudget
    rw [dite_eq_right hs]
    simp_rw [SourceBranchSuccess, dite_eq_right hs]
    simp

def GuideChildSuccess {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (T : GuideTree V N) (P : T.parts) (output : V → Option ℝ) : Prop :=
  let S := Prog.eval G.cut (centroidShoreProgram family T) P
  (∀ t, EstimateAbove (stValue G t T.source) (output t)) ∧
    ∀ (htrace : S ∩ T.realVertices = T.graphGroup P.val) t, t ∈ T.realVertices →
      (∃ X : Finset (ShoreVertex S), IsSTMinCut G t T.source (pull (shoreMap S) X) ∧
        (childGuide T P S htrace).RespectsCut X 2) → output t = some (stValue G t T.source)

theorem guideChildSuccess_of_child {M : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (G : WeightedGraph V) (T : GuideTree V N) (P : T.parts)
    (htrace : (Prog.eval G.cut (centroidShoreProgram family T) P) ∩ T.realVertices = T.graphGroup P.val)
    (output : ShoreVertex (Prog.eval G.cut (centroidShoreProgram family T) P) → Option ℝ)
    (hchild : GuideTwoSuccess (G.contract (shoreMap (Prog.eval G.cut (centroidShoreProgram family T) P)))
      (childGuide T P _ htrace) output) :
    GuideChildSuccess family G T P
      (fun t => pullEstimate (shoreMap (Prog.eval G.cut (centroidShoreProgram family T) P))
        T.source t output) := by
  let S := Prog.eval G.cut (centroidShoreProgram family T) P
  refine ⟨?_, ?_⟩
  · intro t
    apply pullEstimate_above G
    simpa only [childGuide_source] using hchild.1 (shoreMap S t)
  · intro htrace' t ht hrepresented
    obtain ⟨X, hX, hrespect⟩ := hrepresented
    apply pullEstimate_exact G _ hX output
    have hcut := minCut_contract_of_pull G (shoreMap S) hX rfl
    have hexact := hchild.2 (shoreMap S t) (childGuide_map_real T P S htrace ht)
      ⟨X, by simpa only [childGuide_source] using hcut, hrespect⟩
    simpa only [childGuide_source] using hexact

theorem guideTwoCombine_success {M : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (hlarge : 2 < T.real.card)
    (children : T.parts → V → Option ℝ) (pruned switched : V → Option ℝ)
    (hchildren : ∀ P, GuideChildSuccess family G T P (children P))
    (hpruned : PruningSuccess G T pruned) (hswitched : SourceBranchSuccess G T switched) :
    GuideTwoSuccess G T (guideTwoCombine T
      (Prog.eval G.cut (centroidPairProgram family T)) children pruned switched) := by
  let initial := Prog.eval G.cut (centroidPairProgram family T)
  have hinit : ∀ C, initial = some C → C.value = G.cut C.shore :=
    fun C hC => centroidPairProgram_value family G T hC
  have hall (t : V) : ∀ a ∈ (candidateEstimate (filterCandidate T.source t initial) ::
      pruned t :: switched t :: Finset.univ.toList.map (fun P : T.parts => children P t)),
      EstimateAbove (stValue G t T.source) a := by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact candidateEstimate_above G (fun C hC => filterCandidate_valid G T.source t hinit hC)
    · rcases List.mem_cons.mp ha with rfl | ha
      · exact hpruned.1 t
      · rcases List.mem_cons.mp ha with rfl | ha
        · exact hswitched.above G T t
        · obtain ⟨P, _, rfl⟩ := List.mem_map.mp ha
          exact (hchildren P).1 t
  refine ⟨fun t => bestEstimates_above _ (hall t), ?_⟩
  intro t ht hrespect
  obtain ⟨v, hv, hvt⟩ := Finset.mem_image.mp ht
  obtain ⟨S, hS, A, hA, hk⟩ := hrespect
  apply bestEstimates_exact _ (hall t)
  by_cases hvc : v = T.centroid
  · have hc : T.centroid ∈ T.real := hvc ▸ hv
    have hst : T.source ≠ T.label T.centroid := by
      intro he
      have het : T.label T.centroid = t := by simpa only [hvc] using hvt
      exact hS.2.1 ((he.trans het).symm ▸ hS.1)
    obtain ⟨C, hC, hCexact⟩ := pairCandidateProgram_exact family G hG hst
    have hlabel : T.label T.centroid = t := by simpa only [hvc] using hvt
    have hi : initial = some C := by
      simpa only [initial, centroidPairProgram, hc, ite_true] using hC
    have hcvalid : CandidateValid G T.source t C := by
      simpa only [hlabel] using hCexact.valid G
    have hcexact : CandidateExact G T.source t C := by simpa only [hlabel] using hCexact
    have he : candidateEstimate (filterCandidate T.source t initial) = some (stValue G t T.source) := by
      rw [hi, filterCandidate_of_valid G hcvalid]
      exact candidateEstimate_exact G hcexact
    exact List.mem_cons.mpr (Or.inl he.symm)
  · obtain ⟨targetBranch, htarget⟩ := exists_frontierBranch T.tree T.centroid v hvc
    rcases guideTwo_crossing_cases T A targetBranch with hallCross | hprune | hswitch
    · obtain ⟨P, htrace, X, hX, hrespectX⟩ :=
        singleBranch_child family G hG T hlarge targetBranch ht hS hA hk hallCross
      have hchild := (hchildren P).2 htrace t ht ⟨X, hX, hrespectX⟩
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_map.mpr ⟨P, by simp, hchild⟩
    · obtain ⟨delete, hne, hs, e, he, heB⟩ := hprune
      have hw : HasPruningWitness G T v := by
        refine ⟨targetBranch, delete, Ne.symm hne, hs, htarget, S, ?_, A, hA, hk, e, he, heB⟩
        simpa only [hvt] using hS
      have hexact : pruned t = some (stValue G t T.source) := by
        simpa only [hvt] using hpruned.2 v hv hw
      exact List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl hexact.symm))
    · obtain ⟨delete, hne, hs, e, he, heB⟩ := hswitch
      have hsource : T.sourceNode ≠ T.centroid := by
        intro heq
        have hc : T.centroid ∈ frontierBranch T.tree T.centroid delete := by
          simpa only [heq] using hs
        exact frontierBranch_excludes T.tree T.centroid delete hc
      have hbranchEq := T.sourceBranch_eq hsource delete hs
      have hsuccess : SourceSwitchSuccess G T (frontierBranch T.tree T.centroid delete) switched := by
        rw [SourceBranchSuccess, dite_eq_left hsource, hbranchEq] at hswitched
        exact hswitched
      have hvout : v ∉ frontierBranch T.tree T.centroid delete := by
        intro hvdel
        exact Finset.disjoint_left.mp (frontierBranches_disjoint T.tree T.centroid hne) hvdel htarget
      have hexact := hsuccess.2 v hv hvout S (by simpa only [hvt] using hS) A hA hk e he heB
      have heq : switched t = some (stValue G t T.source) := by simpa only [hvt] using hexact
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl heq.symm)))

end
end CutQueryComplexity.GHReduction
