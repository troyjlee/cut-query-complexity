import CutQueryComplexity.AllPairs.Partition
import CutQueryComplexity.AllPairs.Shaving
import CutQueryComplexity.AllPairs.Padding
import CutQueryComplexity.AllPairs.Representation
import CutQueryComplexity.Sparsification.WeightedParams
import Mathlib.Data.Nat.Sqrt

/-!
# The direct randomized all-pairs cut-query program

An actual weighted cut sparsifier is followed by offline expanding partition,
measured shaving, capped original-edge recovery, and offline minimization on
the reconstructed star. Public triangle padding removes the degree promise.
The only random failure is the already proved sparsifier failure. No
Appendix-A/GKYY reduction or assumed partition/algorithm interface is used.
-/

set_option autoImplicit false

namespace CutQueryComplexity.AllPairs

open Finset WeightedGraph AllPairsAudit Probability
open scoped Classical ENNReal
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

def publicThreshold (V : Type) [Fintype V] : ℕ := Nat.sqrt (2 * Fintype.card V) + 1

def publicEdgeCap (V : Type) [Fintype V] : ℕ :=
  (98 * Nat.clog 2 (Fintype.card V) + 60) * Fintype.card V * publicThreshold V

omit [DecidableEq V] in
theorem publicThreshold_pos : 0 < (publicThreshold V : ℝ) := by
  unfold publicThreshold
  positivity

omit [DecidableEq V] in
theorem publicThreshold_scale : 2 * (Fintype.card V : ℝ) ≤ (publicThreshold V : ℝ) ^ 2 := by
  have h := (Nat.lt_succ_sqrt' (2 * Fintype.card V)).le
  have h' : 2 * Fintype.card V ≤ (publicThreshold V) ^ 2 := by
    simpa [publicThreshold, Nat.succ_eq_add_one] using h
  exact_mod_cast h'

/-- The block map is produced by original cut queries from the explicit K. -/
def friendlyProgram (K : WeightedGraph V) :
    DTree (Finset V) ℝ (V → V) (3 * Fintype.card V) :=
  shaveProgram (partitionMap K (publicThreshold V)) (publicThreshold V)

theorem friendlyProgram_good {G K : WeightedGraph V} (hG : Unweighted G)
    (hK : IsCutSparsifier (1 / 2) G K) :
    PreservesFriendly G ((friendlyProgram K).eval G.cut) ∧
      (∑ b, G.cut (fiber ((friendlyProgram K).eval G.cut) b)) ≤
        2 * (publicEdgeCap V : ℝ) := by
  have hτ := publicThreshold_pos (V := V)
  constructor
  · intro S hf hs
    exact shaveProgram_respects hG hK _ hτ publicThreshold_scale
      (partitionMap_expands K hτ.le) hf hs
  · have h := shaveProgram_sparse_bound hK _ hτ.le (partitionMap_boundary_le K hτ.le)
    change (∑ b, G.cut (fiber ((shaveProgram
      (partitionMap K (publicThreshold V)) (publicThreshold V)).eval G.cut) b)) ≤ _
    convert h using 1
    unfold publicEdgeCap
    push_cast
    ring

abbrev postBudget (V : Type) [Fintype V] : ℕ :=
  3 * Fintype.card V + starRecoveryBudget V (publicEdgeCap V)

def afterSparsifier (K : WeightedGraph V) :
    DTree (Finset V) ℝ (Option (Answers V)) (postBudget V) :=
  (friendlyProgram K).bind fun p => recoverAnswers p (publicEdgeCap V)

theorem afterSparsifier_correct {G K : WeightedGraph V} (hG : Unweighted G)
    (hdeg : ∀ v, 2 ≤ G.degree v) (hK : IsCutSparsifier (1 / 2) G K) :
    ∃ out, (afterSparsifier K).eval G.cut = some out ∧ allPairsGood G out := by
  obtain ⟨hp, hM⟩ := friendlyProgram_good hG hK
  obtain ⟨out, ho, hg⟩ := recoverAnswers_correct hG hdeg _ hp (publicEdgeCap V) hM
  exact ⟨out, by simpa only [afterSparsifier, DTree.eval_bind] using ho, hg⟩

abbrev sparsifierBudget (V : Type) [Fintype V] (s : ℝ) : ℕ :=
  capQ V (paramρ V s) (paramc V s (1 / 2))

def initialSparsifier (V : Type) [Fintype V] (s : ℝ) :
    RTree (Finset V) ℝ (Option (WeightedGraph V)) (sparsifierBudget V s) :=
  sparsify (paramρ V s) (paramc V s (1 / 2)) (paramR V s)
    ⌈2 * paramc V s (1 / 2) * (Fintype.card V : ℝ) ^ 2⌉₊ (sparsifierBudget V s)

theorem initialSparsifier_failure (G : WeightedGraph V) (hn : 1 ≤ Fintype.card V)
    {s : ℝ} (hs : 0 ≤ s) :
    mass ((initialSparsifier V s).eval G.cut)
      (fun o => ¬∃ K, o = some K ∧
        IsSparseCutSparsifier (1 / 2) (edgeBound V (paramc V s (1 / 2))) G K) ≤
      ENNReal.ofReal (baseB V ^ (-s)) := by
  obtain rfl := Subsingleton.elim (inferInstance : DecidableEq V) (Classical.decEq V)
  have h := sparsify_whp G hn (s := s) (ε := (1 / 2 : ℝ)) hs
    (by norm_num) (by norm_num)
  simpa only [initialSparsifier, sparsifierBudget] using h

abbrev minDegreeBudget (V : Type) [Fintype V] (s : ℝ) : ℕ :=
  sparsifierBudget V s + postBudget V

def minDegreeProgram (s : ℝ) :
    RTree (Finset V) ℝ (Option (Answers V)) (minDegreeBudget V s) :=
  (initialSparsifier V s).bind fun answer => match answer with
    | none => RTree.pure (PMF.pure none)
    | some K => RTree.ofDeterministic (afterSparsifier K)

def Successful (G : WeightedGraph V) (o : Option (Answers V)) : Prop :=
  ∃ out, o = some out ∧ allPairsGood G out

/-- Finite capped execution; every combinatorial interface is constructed. -/
theorem minDegreeProgram_failure (G : WeightedGraph V) (hG : Unweighted G)
    (hn : 1 ≤ Fintype.card V) (hdeg : ∀ v, 2 ≤ G.degree v)
    {s : ℝ} (hs : 0 ≤ s) :
    mass ((minDegreeProgram s).eval G.cut) (fun o => ¬Successful G o) ≤
      ENNReal.ofReal (baseB V ^ (-s)) := by
  rw [minDegreeProgram, RTree.eval_bind]
  refine (mass_bind_le_add ((initialSparsifier V s).eval G.cut) _
    (fun o => ¬∃ K, o = some K ∧
      IsSparseCutSparsifier (1 / 2) (edgeBound V (paramc V s (1 / 2))) G K)
    (fun o => ¬Successful G o)
    (δ := ENNReal.ofReal (baseB V ^ (-s))) (ε := 0)
    (initialSparsifier_failure G hn hs) ?_).trans (by simp)
  intro answer hg
  obtain ⟨K, rfl, hK⟩ := not_not.mp hg
  obtain ⟨out, ho, hgood⟩ := afterSparsifier_correct hG hdeg hK.1
  simp only [RTree.eval_ofDeterministic, ho, mass_pure]
  have hsuccess : Successful G (some out) := ⟨out, rfl, hgood⟩
  simp [hsuccess]

def originalAnswers (out : Answers (Padded V)) : Answers V :=
  fun s t => ⟨originalShore (out (.inl s) (.inl t)).shore,
    (out (.inl s) (.inl t)).value⟩

theorem originalAnswers_correct (G : WeightedGraph V)
    {out : Answers (Padded V)}
    (ho : allPairsGood (paddedGraph G) out) : allPairsGood G (originalAnswers out) := by
  intro s t hst
  have he : (Sum.inl s : Padded V) ≠ .inl t := by simpa using hst
  obtain ⟨hmin, hvalue⟩ := ho _ _ he
  obtain ⟨hmin', hvalue'⟩ := padded_minimum_extract G hmin
  exact ⟨hmin', hvalue.trans hvalue'⟩

abbrev allPairsBudget (V : Type) [Fintype V] (s : ℝ) : ℕ :=
  minDegreeBudget (Padded V) s

/-- All original terminal pairs, using a single shared randomized transcript. -/
def allPairsProgram (s : ℝ) :
    RTree (Finset V) ℝ (Option (Answers V)) (allPairsBudget V s) :=
  (((minDegreeProgram (V := Padded V) s).substitute paddedQuery).map
    (Option.map originalAnswers)).cast (by simp)

/-- No minimum-degree or connectivity promise on the original unit graph. -/
theorem allPairsProgram_failure (G : WeightedGraph V) (hG : Unweighted G)
    (hn : 1 ≤ Fintype.card V) {s : ℝ} (hs : 0 ≤ s) :
    mass ((allPairsProgram s).eval G.cut) (fun o => ¬Successful G o) ≤
      ENNReal.ofReal (baseB (Padded V) ^ (-s)) := by
  rw [allPairsProgram, RTree.eval_cast, RTree.eval_map, padded_substitute_eval, mass_map]
  have hN : 1 ≤ Fintype.card (Padded V) := by rw [padded_card]; omega
  refine (Probability.mass_mono _
    (P := fun answer => ¬Successful G (Option.map originalAnswers answer))
    (Q := fun answer => ¬Successful (paddedGraph G) answer)
    (fun answer hbad hgood => ?_)).trans
    (minDegreeProgram_failure (paddedGraph G) (padded_unweighted hG) hN
      (padded_min_degree G) hs)
  obtain ⟨out, rfl, ho⟩ := hgood
  exact hbad ⟨originalAnswers out, rfl, originalAnswers_correct G ho⟩

/-- A single failure event controls every original terminal pair, including
both the reported shore and its exact numerical cut value. -/
theorem allPairsProgram_failure_explicit (G : WeightedGraph V) (hG : Unweighted G)
    (hn : 1 ≤ Fintype.card V) {s : ℝ} (hs : 0 ≤ s) :
    mass ((allPairsProgram s).eval G.cut) (fun o => ¬Successful G o) ≤
      ENNReal.ofReal ((6 * (Fintype.card V : ℝ) + 2) ^ (-s)) := by
  have hb : baseB (Padded V) = 6 * (Fintype.card V : ℝ) + 2 := by
    simp only [baseB, padded_card, Nat.cast_mul, Nat.cast_ofNat]
    ring
  simpa only [hb] using allPairsProgram_failure G hG hn hs

/-- This query cap holds for every supported execution, including all failed
sparsifier histories, and has no extra factor for the number of terminal pairs. -/
theorem allPairsProgram_cost (s : ℝ) (oracle : Finset V → ℝ)
    {out : Option (Answers V) × ℕ}
    (ho : out ∈ (RTree.run oracle (allPairsProgram s)).support) :
    out.2 ≤ allPairsBudget V s := RTree.cost_le _ _ ho

end
end CutQueryComplexity.AllPairs

#print axioms CutQueryComplexity.AllPairs.friendlyProgram_good
#print axioms CutQueryComplexity.AllPairs.initialSparsifier_failure
#print axioms CutQueryComplexity.AllPairs.minDegreeProgram_failure
#print axioms CutQueryComplexity.AllPairs.allPairsProgram_failure
#print axioms CutQueryComplexity.AllPairs.allPairsProgram_failure_explicit
#print axioms CutQueryComplexity.AllPairs.allPairsProgram_cost
