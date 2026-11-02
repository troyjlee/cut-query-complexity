import CutQueryComplexity.AllPairs.Recovery
import CutQueryComplexity.AllPairsAudit.Endpoint

/-!
# Construct the explicit star from measured degrees and recovered edges

Every argument of the constructor is public. The original internal edges are
never enumerated: each spoke is the measured degree minus the recovered
external degree. Clipping at zero makes the constructor total for arbitrary
answer sequences. Offline minimization then returns all terminal shores and
their exact numerical values at once, without an additional input-query factor.
-/

set_option autoImplicit false

namespace CutQueryComplexity.AllPairs

open Finset WeightedGraph AllPairsAudit
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

def publicSpoke (R : WeightedGraph V) (d : V → ℝ) (v : V) : ℝ :=
  max 0 (d v - R.degree v)

def publicStar (p : V → V) (R : WeightedGraph V) (d : V → ℝ) : WeightedGraph (V ⊕ V) where
  w
    | .inl u, .inl v => if p u = p v then 0 else R.w u v
    | .inl u, .inr b => if p u = b then publicSpoke R d u else 0
    | .inr b, .inl v => if p v = b then publicSpoke R d v else 0
    | .inr _, .inr _ => 0
  symm u v := by cases u <;> cases v <;> simp [eq_comm, R.symm]
  nonneg u v := by
    have hs (x : V) : 0 ≤ publicSpoke R d x := le_max_left _ _
    cases u <;> cases v <;> dsimp <;> (try split) <;> simp_all [R.nonneg]
  diag u := by cases u <;> simp

theorem publicSpoke_correct (G : WeightedGraph V) (p : V → V) (v : V) :
    publicSpoke (G.residual p) G.degree v = internalDegree G p v := by
  have hn : 0 ≤ internalDegree G p v := by
    apply sum_nonneg
    intro u _
    split <;> simp [G.nonneg]
  have he := internalDegree_from_external G p v
  change internalDegree G p v = G.degree v - (G.residual p).degree v at he
  rw [publicSpoke, ← he, max_eq_right hn]

theorem publicStar_correct (G : WeightedGraph V) (p : V → V) :
    publicStar p (G.residual p) G.degree = star G p := by
  ext u v
  cases u <;> cases v <;>
    simp only [publicStar, AllPairsAudit.star, publicSpoke_correct] <;>
    simp [residual] <;> (intro h h'; exact False.elim (h' h))

abbrev starRecoveryBudget (V : Type) [Fintype V] (M : ℕ) : ℕ :=
  Fintype.card V + recoveryBudget V M

/-- A capped, actual original-cut program returning the complete explicit star. -/
def recoverStar (p : V → V) (M : ℕ) :
    DTree (Finset V) ℝ (Option (WeightedGraph (V ⊕ V))) (starRecoveryBudget V M) :=
  (DTree.queryAll (fun v : V => ({v} : Finset V)) (fun _ => (0 : ℝ))).bind fun d =>
    (recoverCapped p M).map (Option.map fun R => publicStar p R d)

theorem recoverStar_correct (G : WeightedGraph V) (hG : Unweighted G)
    (p : V → V) (M : ℕ) (hM : (∑ b, G.cut (fiber p b)) ≤ 2 * (M : ℝ)) :
    (recoverStar p M).eval G.cut = some (star G p) := by
  have hd : (DTree.queryAll (fun v : V => ({v} : Finset V)) (fun _ => (0 : ℝ))).eval
      G.cut = G.degree := by simp [DTree.eval, DTree.queryAll_run]
  simp only [recoverStar, DTree.eval_bind, hd, DTree.eval_map,
    recoverCapped_correct G hG p M hM, Option.map_some, publicStar_correct]

theorem recoverStar_cost (p : V → V) (M : ℕ) (oracle : Finset V → ℝ) :
    (recoverStar p M).cost oracle ≤ starRecoveryBudget V M := DTree.cost_le _ _

/-- Select a minimum from a fully explicit graph by finite offline computation. -/
def offlineST (H : WeightedGraph V) (s t : V) : Finset V :=
  if h : s ≠ t then Classical.choose (exists_st_minimum H h) else ∅

theorem offlineST_correct (H : WeightedGraph V) {s t : V} (hst : s ≠ t) :
    IsSTMinCut H s t (offlineST H s t) := by
  simp only [offlineST, dite_eq_left hst]
  exact Classical.choose_spec (exists_st_minimum H hst)

/-- Both fields are computed from the recovered explicit graph. -/
structure STAnswer (V : Type) where
  shore : Finset V
  value : ℝ

abbrev Answers (V : Type) := V → V → STAnswer V

def allPairsGood (G : WeightedGraph V) (out : Answers V) : Prop :=
  ∀ s t, s ≠ t → IsSTMinCut G s t (out s t).shore ∧
    (out s t).value = G.cut (out s t).shore

def starAnswers (H : WeightedGraph (V ⊕ V)) : Answers V :=
  fun s t =>
    let A := offlineST H (.inl s) (.inl t)
    ⟨originalShore A, H.cut A⟩

theorem starAnswers_correct {G : WeightedGraph V} (hG : Unweighted G)
    (hdeg : ∀ v, 2 ≤ G.degree v) (p : V → V) (hp : PreservesFriendly G p) :
    allPairsGood G (starAnswers (star G p)) := by
  intro s t hst
  have he : (Sum.inl s : V ⊕ V) ≠ .inl t := by simpa using hst
  exact star_minimum_extract hG hdeg p hp hst (offlineST_correct _ he)

/-- Solve all pairs from the one recovered representation; no input queries
are used in the final finite minimizations. -/
def recoverAnswers (p : V → V) (M : ℕ) :
    DTree (Finset V) ℝ (Option (Answers V)) (starRecoveryBudget V M) :=
  (recoverStar p M).map (Option.map starAnswers)

theorem recoverAnswers_correct {G : WeightedGraph V} (hG : Unweighted G)
    (hdeg : ∀ v, 2 ≤ G.degree v) (p : V → V) (hp : PreservesFriendly G p)
    (M : ℕ) (hM : (∑ b, G.cut (fiber p b)) ≤ 2 * (M : ℝ)) :
    ∃ out, (recoverAnswers p M).eval G.cut = some out ∧ allPairsGood G out := by
  refine ⟨starAnswers (star G p), ?_, starAnswers_correct hG hdeg p hp⟩
  simp [recoverAnswers, recoverStar_correct G hG p M hM]

end
end CutQueryComplexity.AllPairs

#print axioms CutQueryComplexity.AllPairs.recoverStar_correct
#print axioms CutQueryComplexity.AllPairs.recoverStar_cost
#print axioms CutQueryComplexity.AllPairs.recoverAnswers_correct
