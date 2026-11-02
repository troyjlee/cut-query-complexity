import CutQueryComplexity.GHReduction.GuideOneGlobal
import CutQueryComplexity.GHReduction.FrontierContraction
import CutQueryComplexity.Spanner.Random

/-! # Actual fair-coin pruning of centroid branches

The source branch and the centroid are always retained. All other branches
are sampled independently. Retaining a target branch while deleting a distinct
crossed branch has probability one quarter. On that event the implemented
one-respecting call returns an exact candidate, so one trial fails with
probability at most three quarters. Fake guide nodes add no graph vertices.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical ENNReal
open Probability

variable {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]

theorem frontierBranch_isCentroidBranch (T : RootedTree N) (c : N)
    (e : frontierProxies T c) : IsCentroidBranch T c (frontierBranch T c e) := by
  refine ⟨frontierBranch_excludes T c e, ?_⟩
  intro v hv hvc hpc
  by_cases hec : e.val = c
  · simp only [frontierBranch, hec, ite_true, Finset.mem_compl]
    apply not_congr
    simp only [RootedTree.mem_D, T.isAnc_iff_of_ne_root hv, Ne.symm hvc, false_or]
  · have hep := ((mem_frontierProxies T c e.val).mp e.property).2.resolve_left hec
    have hev : e.val ≠ v := by
      intro he
      exact hpc (by rw [← he, hep])
    simp only [frontierBranch, hec, ite_false, RootedTree.mem_D,
      T.isAnc_iff_of_ne_root hv, hev, false_or]

abbrev GuidePruneSeed (T : GuideTree V N) := frontierProxies T.tree T.centroid → Bool

def GuideTree.keptBranches (T : GuideTree V N) (seed : GuidePruneSeed T) : Finset N :=
  Finset.univ.filter (fun x => x = T.centroid ∨
    ∃ e : frontierProxies T.tree T.centroid,
      x ∈ frontierBranch T.tree T.centroid e ∧
        (T.sourceNode ∈ frontierBranch T.tree T.centroid e ∨ seed e = true))

theorem GuideTree.source_kept (T : GuideTree V N) (seed : GuidePruneSeed T) :
    T.sourceNode ∈ T.keptBranches seed := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  by_cases hs : T.sourceNode = T.centroid
  · exact Or.inl hs
  · obtain ⟨e, he⟩ := exists_frontierBranch T.tree T.centroid T.sourceNode hs
    exact Or.inr ⟨e, he, Or.inl he⟩

theorem GuideTree.branch_kept (T : GuideTree V N) (seed : GuidePruneSeed T)
    (e : frontierProxies T.tree T.centroid) (he : seed e = true)
    {x : N} (hx : x ∈ frontierBranch T.tree T.centroid e) : x ∈ T.keptBranches seed :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨e, hx, Or.inr he⟩⟩

theorem GuideTree.discarded_branch_disjoint (T : GuideTree V N) (seed : GuidePruneSeed T)
    (e : frontierProxies T.tree T.centroid) (he : seed e = false)
    (hs : T.sourceNode ∉ frontierBranch T.tree T.centroid e) :
    Disjoint (T.keptBranches seed) (frontierBranch T.tree T.centroid e) := by
  apply Finset.disjoint_left.mpr
  intro x hx hxe
  rcases (Finset.mem_filter.mp hx).2 with hxc | ⟨d, hxd, hd⟩
  · exact frontierBranch_excludes T.tree T.centroid e (hxc ▸ hxe)
  · have hde : d = e := by
      by_contra hne
      exact Finset.disjoint_left.mp (frontierBranches_disjoint T.tree T.centroid hne) hxd hxe
    subst d
    rcases hd with hd | hd
    · exact hs hd
    · simp only [he, Bool.false_eq_true] at hd

def GuideTree.pruned (T : GuideTree V N) (seed : GuidePruneSeed T) : GuideTree V N :=
  T.retain (T.keptBranches seed) T.sourceNode
    (Finset.mem_inter.mpr ⟨T.source_real, T.source_kept seed⟩)

@[simp] theorem GuideTree.pruned_source (T : GuideTree V N) (seed : GuidePruneSeed T) :
    (T.pruned seed).source = T.source := rfl

theorem GuideTree.pruned_real_mem (T : GuideTree V N) (seed : GuidePruneSeed T)
    {x : N} (hx : x ∈ T.real) (e : frontierProxies T.tree T.centroid)
    (hxe : x ∈ frontierBranch T.tree T.centroid e) (he : seed e = true) :
    T.label x ∈ (T.pruned seed).realVertices :=
  Finset.mem_image.mpr ⟨x, Finset.mem_inter.mpr ⟨hx, T.branch_kept seed e he hxe⟩, rfl⟩

theorem GuideTree.pruned_respects (T : GuideTree V N) (seed : GuidePruneSeed T)
    (branch : frontierProxies T.tree T.centroid) (hseed : seed branch = false)
    (hs : T.sourceNode ∉ frontierBranch T.tree T.centroid branch)
    {S : Finset V} {A : Finset N}
    (hA : ∀ v ∈ T.real, v ∈ A ↔ T.label v ∈ S)
    (hcross : (T.tree.crossSet A).card ≤ 2)
    (e : N) (he : e ∈ T.tree.crossSet A)
    (heB : e ∈ frontierBranch T.tree T.centroid branch ∨
      T.tree.parent e ∈ frontierBranch T.tree T.centroid branch) :
    (T.pruned seed).RespectsCut S 1 := by
  let B := frontierBranch T.tree T.centroid branch
  have hdisj := T.discarded_branch_disjoint seed branch hseed hs
  refine ⟨collapseBranch T.centroid B A, ?_, ?_⟩
  · intro v hv
    obtain ⟨hvr, hvkeep⟩ := Finset.mem_inter.mp hv
    have hvB : v ∉ B := fun hb => Finset.disjoint_left.mp hdisj hvkeep hb
    change v ∈ collapseBranch T.centroid B A ↔ T.label v ∈ S
    simpa only [mem_collapseBranch, hvB, ite_false] using hA v hvr
  · have h := collapseBranch_crossing_decreases T.tree T.centroid B A
      (frontierBranch_isCentroidBranch T.tree T.centroid branch) he heB
    change (T.tree.crossSet (collapseBranch T.centroid B A)).card ≤ 1
    omega

theorem mass_prune_keep_delete (T : GuideTree V N)
    (keep delete : frontierProxies T.tree T.centroid) (hne : keep ≠ delete) :
    mass (Spanner.coinPMF (frontierProxies T.tree T.centroid))
      (fun seed : GuidePruneSeed T => seed keep = true ∧ seed delete = false) =
        ENNReal.ofReal (1 / 4 : ℝ) := by
  have h := Spanner.mass_coins_eq ({keep, delete} : Finset (frontierProxies T.tree T.centroid))
    (fun e => if e = keep then true else false)
  have hcoin : mass (Spanner.coinPMF (frontierProxies T.tree T.centroid))
      (fun seed : GuidePruneSeed T => seed keep = true ∧ seed delete = false) =
        (2⁻¹ : ℝ≥0∞) ^ 2 := by
    simpa [hne, Ne.symm hne] using h
  rw [hcoin]
  rw [← ENNReal.inv_pow, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
  norm_num [div_eq_mul_inv]

def guidePruneTree {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n : ℕ) (T : GuideTree V N) :
    RTree (Finset V) ℝ (V → Option (CutCandidate V)) (guideOneGlobalBudget Q n) :=
  RTree.mix ((Spanner.coinPMF (frontierProxies T.tree T.centroid)).map (fun seed =>
    RTree.ofDeterministic ((guideOneGlobalTree family n (T.pruned seed)).map
      (fun output => output.getD (fun _ => none)))))

theorem guidePruneTree_eval {M n : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (hG : InputPromise M G) (T : GuideTree V N)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) :
    (guidePruneTree family n T).eval G.cut =
      (Spanner.coinPMF (frontierProxies T.tree T.centroid)).map (fun seed =>
        Prog.eval G.cut (guideOneProgram family (Nat.clog 2 (n + 1)) (T.pruned seed))) := by
  simp only [guidePruneTree, RTree.eval_mix, PMF.bind_map, Function.comp_def]
  have he (seed : GuidePruneSeed T) :
      (RTree.ofDeterministic ((guideOneGlobalTree family n (T.pruned seed)).map
        (fun output => output.getD (fun _ => none)))).eval G.cut =
      PMF.pure (Prog.eval G.cut
        (guideOneProgram family (Nat.clog 2 (n + 1)) (T.pruned seed))) := by
    simp only [RTree.eval, RTree.run_ofDeterministic, PMF.pure_map]
    apply congrArg PMF.pure
    change ((guideOneGlobalTree family n (T.pruned seed)).map
      (fun output => output.getD (fun _ => none))).eval G.cut = _
    rw [DTree.eval_map, guideOneGlobalTree_eval family G hG (T.pruned seed) hvn hQ]
    rfl
  simp_rw [he]
  rfl

theorem guidePruneTree_valid {M n : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (hG : InputPromise M G) (T : GuideTree V N)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    {output : V → Option (CutCandidate V)}
    (hout : output ∈ ((guidePruneTree family n T).eval G.cut).support)
    {t : V} {C : CutCandidate V} (hC : output t = some C) : CandidateValid G T.source t C := by
  rw [guidePruneTree_eval family G hG T hvn hQ] at hout
  obtain ⟨seed, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
  exact guideOneProgram_valid family _ G (T.pruned seed) t C hC

/-- The hidden minimum shore and its crossed branch appear only in the proof
of this fixed public randomized program. This bound can be conditioned on
any successful earlier history without assuming global independence. -/
theorem guidePruneTree_failure_le {M n : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (hG : InputPromise M G) (T : GuideTree V N)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (keep delete : frontierProxies T.tree T.centroid) (hne : keep ≠ delete)
    (hs : T.sourceNode ∉ frontierBranch T.tree T.centroid delete)
    (t : N) (ht : t ∈ T.real) (htkeep : t ∈ frontierBranch T.tree T.centroid keep)
    (S : Finset V) (hS : IsSTMinCut G (T.label t) T.source S)
    (A : Finset N) (hA : ∀ v ∈ T.real, v ∈ A ↔ T.label v ∈ S)
    (hcross : (T.tree.crossSet A).card ≤ 2)
    (e : N) (he : e ∈ T.tree.crossSet A)
    (heB : e ∈ frontierBranch T.tree T.centroid delete ∨
      T.tree.parent e ∈ frontierBranch T.tree T.centroid delete) :
    mass ((guidePruneTree family n T).eval G.cut)
      (fun output => ¬∃ C, output (T.label t) = some C ∧ CandidateExact G T.source (T.label t) C) ≤
        ENNReal.ofReal (3 / 4 : ℝ) := by
  rw [guidePruneTree_eval family G hG T hvn hQ, mass_map]
  apply failure_le_of_success _ _ (by norm_num : (0 : ℝ) ≤ 3 / 4)
  have hgood (seed : GuidePruneSeed T) (hseed : seed keep = true ∧ seed delete = false) :
      ∃ C, Prog.eval G.cut (guideOneProgram family (Nat.clog 2 (n + 1)) (T.pruned seed))
        (T.label t) = some C ∧ CandidateExact G T.source (T.label t) C := by
    have ht' := T.pruned_real_mem seed ht keep htkeep hseed.1
    have hrespect := T.pruned_respects seed delete hseed.2 hs hA hcross e he heB
    have hdepth := ((T.pruned seed).real_card_le.trans hvn).trans (initial_fuel_bound n)
    exact guideOneProgram_complete family _ G hG (T.pruned seed) hdepth (T.label t) ht'
      ⟨S, hS, hrespect⟩
  have hm := mass_mono (Spanner.coinPMF (frontierProxies T.tree T.centroid)) hgood
  rw [mass_prune_keep_delete T keep delete hne] at hm
  have hr := ENNReal.toReal_mono (mass_ne_top _ _) hm
  norm_num at hr ⊢
  exact hr

end
end CutQueryComplexity.GHReduction
