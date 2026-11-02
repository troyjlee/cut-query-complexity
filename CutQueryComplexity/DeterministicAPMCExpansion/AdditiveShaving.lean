import CutQueryComplexity.DeterministicAPMCExpansion.Basic
import CutQueryComplexity.AllPairs.Shaving
import CutQueryComplexity.AllPairs.Representation

/-!
# Actual shaving and recovery from a supplied additive partition

This is a conditional integration milestone. `partitionAnswers` is an actual
graph-independent, hard-capped deterministic query tree. Its correctness here
assumes the additive and boundary invariants of its supplied public map. The
final decomposition constructor must discharge those invariants.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion

open Finset WeightedGraph AllPairsAudit AllPairs
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

theorem additive_retained_no_split {G : WeightedGraph V} (hG : Unweighted G)
    {W S : Finset V} {b R β N : ℕ}
    (hb : 0 < b) (hR : 0 < R) (hβ : 0 < β) (hN : N ≤ b * β)
    (hexpand : AdditiveExpands G W b R β)
    (hf : Friendly G S) (hcut : G.cut S ≤ 2 * (N : ℝ)) {x y : V}
    (hxS : x ∈ S) (hyS : y ∉ S)
    (hxd : 60 * (shavingScale R β : ℝ) ≤ G.degree x)
    (hyd : 60 * (shavingScale R β : ℝ) ≤ G.degree y)
    (hxb : 24 * incident G x Wᶜ ≤ G.degree x)
    (hyb : 24 * incident G y Wᶜ ≤ G.degree y) : False := by
  have hτ : (0 : ℝ) < shavingScale R β := by
    exact_mod_cast shavingScale_pos hR hβ
  have hl := retained_side_card hG hτ.le hf hxS hxd hxb
  have hr := retained_side_card hG hτ.le ((friendly_compl G S).mpr hf)
    (mem_compl.mpr hyS) hyd hyb
  have hright : W \ S = W ∩ Sᶜ := by ext v; simp
  have hmin : 6 * (shavingScale R β : ℝ) ≤
      min ((W ∩ S).card : ℝ) ((W \ S).card : ℝ) := by
    rw [hright]
    exact le_min hl hr
  have hsmall := additive_small_cut_side hb hN hexpand hcut
  linarith

theorem shaveMap_respects_of_additive {G : WeightedGraph V} (hG : Unweighted G)
    (p : V → V) (d boundary : V → ℝ)
    (hd : ∀ v, d v = G.degree v)
    (hboundary : ∀ v, boundary v = incident G v (fiber p (p v))ᶜ)
    {b R β : ℕ} (hb : 0 < b) (hR : 0 < R) (hβ : 0 < β)
    (hN : Fintype.card V ≤ b * β) (hexpand : AdditivePartition G p b R β)
    {S : Finset V} (hf : Friendly G S) (hcut : G.cut S ≤ 2 * Fintype.card V) :
    Respects (shaveMap p d boundary (shavingScale R β)) S := by
  intro u v he
  by_cases huv : u = v
  · subst v
    rfl
  obtain ⟨hu, hv, hp⟩ := shaveMap_eq_cases p d boundary (shavingScale R β) huv he
  simp only [Keep, hd, hboundary] at hu hv
  have hvb : 24 * incident G v (fiber p (p u))ᶜ ≤ G.degree v := by
    simpa only [hp] using hv.2
  constructor
  · intro hus
    by_contra hvs
    exact additive_retained_no_split hG hb hR hβ hN (hexpand (p u)) hf hcut
      hus hvs hu.1 hv.1 hu.2 hvb
  · intro hvs
    by_contra hus
    exact additive_retained_no_split hG hb hR hβ hN (hexpand (p u)) hf hcut
      hvs hus hv.1 hu.1 hvb hu.2

theorem shaveProgram_preservesFriendly_of_additive {G : WeightedGraph V}
    (hG : Unweighted G) (p : V → V) {b R β : ℕ}
    (hb : 0 < b) (hR : 0 < R) (hβ : 0 < β)
    (hN : Fintype.card V ≤ b * β) (hexpand : AdditivePartition G p b R β) :
    PreservesFriendly G ((shaveProgram p (shavingScale R β)).eval G.cut) := by
  intro S hf hcut
  rw [shaveProgram_eval]
  exact shaveMap_respects_of_additive hG p _ _ (fun _ => rfl) (fun _ => rfl)
    hb hR hβ hN hexpand hf hcut

/-- Half of the proved sum of final block-cut values. This is public. -/
def edgeCap (N b R β : ℕ) : ℕ :=
  49 * b * N * Nat.clog 2 N + 60 * N * shavingScale R β

theorem shaveProgram_edge_cap_of_boundary (G : WeightedGraph V) (p : V → V)
    (b R β : ℕ)
    (hboundary : (∑ v, G.cut (fiber p v)) ≤
      2 * (b : ℝ) * Fintype.card V * Nat.clog 2 (Fintype.card V)) :
    (∑ v, G.cut (fiber ((shaveProgram p (shavingScale R β)).eval G.cut) v)) ≤
      2 * (edgeCap (Fintype.card V) b R β : ℝ) := by
  have h := shaveProgram_boundary_le G p
    (show (0 : ℝ) ≤ shavingScale R β by positivity)
  simp only [edgeCap, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  linarith

def partitionRecoveryBudget (V : Type) [Fintype V] (b R β : ℕ) : ℕ :=
  3 * Fintype.card V + starRecoveryBudget V (edgeCap (Fintype.card V) b R β)

/-- All parameters precede the hidden graph. Shaving and reconstruction are
executed by the existing concrete query programs, not assumed as oracles. -/
def partitionAnswers (p : V → V) (b R β : ℕ) :
    DTree (Finset V) ℝ (Option (Answers V)) (partitionRecoveryBudget V b R β) :=
  (shaveProgram p (shavingScale R β)).bind fun shaved =>
    recoverAnswers shaved (edgeCap (Fintype.card V) b R β)

theorem partitionAnswers_cost (p : V → V) (b R β : ℕ) (oracle : Finset V → ℝ) :
    (partitionAnswers p b R β).cost oracle ≤ partitionRecoveryBudget V b R β :=
  DTree.cost_le _ _

theorem partitionRecoveryBudget_eq (b R β : ℕ) :
    partitionRecoveryBudget V b R β =
      5 * Fintype.card V +
        (Fintype.card V + 2 * edgeCap (Fintype.card V) b R β) *
          ((searchDepth V + 1) * 3) := by
  simp only [partitionRecoveryBudget, starRecoveryBudget, recoveryBudget]
  omega

/-- CONDITIONAL milestone: the partition constructor has not been supplied
by this theorem. Correctness has no residual solver or recovery premise. -/
theorem partitionAnswers_correct {G : WeightedGraph V} (hG : Unweighted G)
    (hdegree : ∀ v, 2 ≤ G.degree v) (p : V → V) {b R β : ℕ}
    (hb : 0 < b) (hR : 0 < R) (hβ : 0 < β)
    (hN : Fintype.card V ≤ b * β) (hexpand : AdditivePartition G p b R β)
    (hboundary : (∑ v, G.cut (fiber p v)) ≤
      2 * (b : ℝ) * Fintype.card V * Nat.clog 2 (Fintype.card V)) :
    ∃ out, (partitionAnswers p b R β).eval G.cut = some out ∧ allPairsGood G out := by
  have hpres := shaveProgram_preservesFriendly_of_additive hG p hb hR hβ hN hexpand
  have hcap := shaveProgram_edge_cap_of_boundary G p b R β hboundary
  obtain ⟨out, heval, hgood⟩ := recoverAnswers_correct hG hdegree _ hpres
    (edgeCap (Fintype.card V) b R β) hcap
  refine ⟨out, ?_, hgood⟩
  exact (DTree.eval_bind (shaveProgram p (shavingScale R β))
    (fun shaved => recoverAnswers shaved (edgeCap (Fintype.card V) b R β)) G.cut).trans heval

/-- A public fallback makes the tree's output type total on every transcript.
It is used only on transcripts outside the proved input/invariant class. -/
def emptyAnswers : Answers V := fun _ _ => ⟨∅, 0⟩

def totalPartitionAnswers (p : V → V) (b R β : ℕ) :
    DTree (Finset V) ℝ (Answers V) (partitionRecoveryBudget V b R β) :=
  (partitionAnswers p b R β).map (fun result => result.getD emptyAnswers)

/-- This remains a supplied-partition theorem. The fallback is unreachable
under these invariants; every pair's witness and value are exact. -/
theorem totalPartitionAnswers_correct {G : WeightedGraph V} (hG : Unweighted G)
    (hdegree : ∀ v, 2 ≤ G.degree v) (p : V → V) {b R β : ℕ}
    (hb : 0 < b) (hR : 0 < R) (hβ : 0 < β)
    (hN : Fintype.card V ≤ b * β) (hexpand : AdditivePartition G p b R β)
    (hboundary : (∑ v, G.cut (fiber p v)) ≤
      2 * (b : ℝ) * Fintype.card V * Nat.clog 2 (Fintype.card V)) :
    allPairsGood G ((totalPartitionAnswers p b R β).eval G.cut) := by
  obtain ⟨out, heval, hgood⟩ :=
    partitionAnswers_correct hG hdegree p hb hR hβ hN hexpand hboundary
  simpa only [totalPartitionAnswers, DTree.eval_map, heval, Option.getD_some] using hgood

theorem totalPartitionAnswers_cost (p : V → V) (b R β : ℕ) (oracle : Finset V → ℝ) :
    (totalPartitionAnswers p b R β).cost oracle ≤ partitionRecoveryBudget V b R β :=
  DTree.cost_le _ _

end
end CutQueryComplexity.DeterministicAPMCExpansion

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.shaveProgram_preservesFriendly_of_additive
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.shaveProgram_edge_cap_of_boundary
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.partitionAnswers_correct
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.partitionAnswers_cost
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.totalPartitionAnswers_correct
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.totalPartitionAnswers_cost
