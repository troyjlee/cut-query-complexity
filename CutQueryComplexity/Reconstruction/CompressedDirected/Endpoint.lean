import CutQueryComplexity.Reconstruction.CompressedDirected.Program
import CutQueryComplexity.Reconstruction.DirectedData
import CutQueryComplexity.Model.Randomized

/-!
# Directed-unit classical table endpoints

One public outgoing-cut program reconstructs the exact cut-equivalent data.
Finite offline minimization supplies original global/all-pairs minimum shores
and numerical values. Deterministic and randomized executions have the same
worst-case `O(n²/log(2n))` bound. The compressed certificates restrict competing
arc capacities to 0 or 1; they do not claim weighted-robust reconstruction.
-/

set_option autoImplicit false

namespace CutQueryComplexity.Reconstruction.CompressedDirected

open Finset DirectedCertificate
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Proof-only description of the correct output, never supplied to a program. -/
def honestData (G : WeightedDiGraph V) : DirectedData V := ⟨G.sym, G.imbalance⟩

/-- Public reconstruction constructor with no hidden graph argument. -/
def reconstruct : DTree (Finset V) ℝ (DirectedData V) (budget V) :=
  (program (V := V)).map fun x => ⟨x.1, x.2⟩

theorem reconstruct_run (G : WeightedDiGraph V) (hG : Unit G) :
    DTree.run G.out (reconstruct (V := V)) = (honestData G, budget V) := by
  simp only [reconstruct, DTree.run_map, program_run G hG, honestData]

theorem reconstruct_cost (oracle : Finset V → ℝ) :
    (reconstruct (V := V)).cost oracle = budget V := by
  simpa only [reconstruct, DTree.cost, DTree.run_map] using program_cost oracle

/-- Exact reconstruction of every outgoing cut, not of the original orientation. -/
theorem reconstruct_cut (G : WeightedDiGraph V) (hG : Unit G) (S : Finset V) :
    ((reconstruct (V := V)).eval G.out).cut S = G.out S := by
  rw [DTree.eval, reconstruct_run G hG]
  exact DirectedData.cut_correct _ G rfl rfl S

def globalProgram : DTree (Finset V) ℝ (AllPairs.STAnswer V) (budget V) :=
  (reconstruct (V := V)).map DirectedData.globalAnswer

def allPairsProgram : DTree (Finset V) ℝ (AllPairs.Answers V) (budget V) :=
  (reconstruct (V := V)).map DirectedData.allPairsAnswers

/-- Exact original shore and value contract for a directed global minimum. -/
def globalGood (G : WeightedDiGraph V) (out : AllPairs.STAnswer V) : Prop :=
  IsGlobalMinCut G out.shore ∧ out.value = G.out out.shore ∧ out.value = G.minValue

/-- All terminal pairs are handled simultaneously; `s=t` is excluded. -/
def allPairsGood (G : WeightedDiGraph V) (out : AllPairs.Answers V) : Prop :=
  ∀ s t, s ≠ t → s ∈ (out s t).shore ∧ t ∉ (out s t).shore ∧
    (out s t).value = G.out (out s t).shore ∧
    ∀ T, s ∈ T → t ∉ T → G.out (out s t).shore ≤ G.out T

theorem globalProgram_run (G : WeightedDiGraph V) (hG : Unit G) :
    DTree.run G.out (globalProgram (V := V)) = ((honestData G).globalAnswer, budget V) := by
  simp only [globalProgram, DTree.run_map, reconstruct_run G hG]

theorem allPairsProgram_run (G : WeightedDiGraph V) (hG : Unit G) :
    DTree.run G.out (allPairsProgram (V := V)) = ((honestData G).allPairsAnswers, budget V) := by
  simp only [allPairsProgram, DTree.run_map, reconstruct_run G hG]

theorem globalProgram_correct (G : WeightedDiGraph V) (hG : Unit G)
    (hn : 2 ≤ Fintype.card V) : globalGood G ((globalProgram (V := V)).eval G.out) := by
  rw [DTree.eval, globalProgram_run G hG]
  exact DirectedData.globalAnswer_correct _ G rfl rfl hn

theorem allPairsProgram_correct (G : WeightedDiGraph V) (hG : Unit G) :
    allPairsGood G ((allPairsProgram (V := V)).eval G.out) := by
  rw [DTree.eval, allPairsProgram_run G hG]
  exact DirectedData.allPairsAnswers_correct _ G rfl rfl

theorem globalProgram_cost (oracle : Finset V → ℝ) :
    (globalProgram (V := V)).cost oracle = budget V := by
  simpa only [globalProgram, DTree.cost, DTree.run_map] using reconstruct_cost oracle

theorem allPairsProgram_cost (oracle : Finset V → ℝ) :
    (allPairsProgram (V := V)).cost oracle = budget V := by
  simpa only [allPairsProgram, DTree.cost, DTree.run_map] using reconstruct_cost oracle

/-- Exact probability-one embedding of the same public all-pairs program. -/
def allPairsRandomized : RTree (Finset V) ℝ (AllPairs.Answers V) (budget V) :=
  RTree.ofDeterministic (allPairsProgram (V := V))

theorem allPairsRandomized_run (G : WeightedDiGraph V) (hG : Unit G) :
    RTree.run G.out (allPairsRandomized (V := V)) =
      PMF.pure ((honestData G).allPairsAnswers, budget V) := by
  simp only [allPairsRandomized, RTree.run_ofDeterministic, allPairsProgram_run G hG]

theorem allPairsRandomized_success (G : WeightedDiGraph V) (hG : Unit G) :
    (allPairsRandomized (V := V)).successProb G.out (allPairsGood G) = 1 := by
  have hg : allPairsGood G (honestData G).allPairsAnswers :=
    DirectedData.allPairsAnswers_correct _ G rfl rfl
  simp [RTree.successProb, allPairsRandomized_run G hG, PMF.toOuterMeasure_pure_apply, hg]

/-- The numerical constant is universal, with no hidden dependence on the input. -/
def headlineConstant : ℝ := 4 + 32768 * Real.log 3

theorem headlineConstant_pos : 0 < headlineConstant := by
  have h : 0 < Real.log 3 := Real.log_pos (by norm_num)
  unfold headlineConstant
  positivity

/-- Global deterministic table export: actual public program, all-reply cap,
then exact correctness uniformly over every unit input. -/
theorem global_deterministic (n : ℕ) (hn : 2 ≤ n) :
    (∀ oracle : Finset (Fin n) → ℝ,
      ((globalProgram (V := Fin n)).cost oracle : ℝ) ≤
        headlineConstant * (n : ℝ)^2 / Real.log (2 * (n : ℝ))) ∧
    (∀ G : WeightedDiGraph (Fin n), Unit G →
      globalGood G ((globalProgram (V := Fin n)).eval G.out)) := by
  constructor
  · intro oracle
    rw [globalProgram_cost]
    simpa [headlineConstant] using budget_bound (V := Fin n) (by simp; omega)
  · intro G hG
    exact globalProgram_correct G hG (by simpa using hn)

/-- Deterministic all-pairs table export with simultaneous original values. -/
theorem allPairs_deterministic (n : ℕ) (hn : 1 ≤ n) :
    (∀ oracle : Finset (Fin n) → ℝ,
      ((allPairsProgram (V := Fin n)).cost oracle : ℝ) ≤
        headlineConstant * (n : ℝ)^2 / Real.log (2 * (n : ℝ))) ∧
    (∀ G : WeightedDiGraph (Fin n), Unit G →
      allPairsGood G ((allPairsProgram (V := Fin n)).eval G.out)) := by
  constructor
  · intro oracle
    rw [allPairsProgram_cost]
    simpa [headlineConstant] using budget_bound (V := Fin n) (by simpa using hn)
  · exact fun G hG => allPairsProgram_correct G hG

/-- Randomized all-pairs table export; every supported execution is capped on
all real reply oracles, and each honest unit input succeeds with probability one. -/
theorem allPairs_randomized (n : ℕ) (hn : 1 ≤ n) :
    (∀ (oracle : Finset (Fin n) → ℝ) (p : AllPairs.Answers (Fin n) × ℕ),
      p ∈ (RTree.run oracle (allPairsRandomized (V := Fin n))).support →
        (p.2 : ℝ) ≤ headlineConstant * (n : ℝ)^2 / Real.log (2 * (n : ℝ))) ∧
    (∀ G : WeightedDiGraph (Fin n), Unit G →
      (allPairsRandomized (V := Fin n)).successProb G.out (allPairsGood G) = 1) := by
  constructor
  · intro oracle p hp
    have hcost : (p.2 : ℝ) ≤ budget (Fin n) := by
      exact_mod_cast RTree.cost_le (allPairsRandomized (V := Fin n)) oracle hp
    exact hcost.trans (by
      simpa [headlineConstant] using budget_bound (V := Fin n) (by simpa using hn))
  · exact fun G hG => allPairsRandomized_success G hG

/-- A compressed certificate consists of the same public measured shores. -/
def queries (V : Type) [Fintype V] [DecidableEq V] : Finset (Finset V) :=
  univ.image (shore (V := V))

theorem queries_card : (queries V).card ≤ budget V := by
  exact card_image_le.trans (by simpa only [card_univ] using (index_card (V := V)).le)

/-- Unit competitors agreeing on this family have the entire same outgoing-cut
function, though their individual arc orientations may differ. -/
theorem queries_cut_equivalent (G H : WeightedDiGraph V) (hG : Unit G) (hH : Unit H)
    (h : Consistent G H (queries V)) : ∀ S, H.out S = G.out S := by
  have ht : (fun i : Index V => H.out (shore i)) = fun i => G.out (shore i) := by
    funext i
    exact h _ (mem_image_of_mem _ (mem_univ i))
  have hs : H.sym = G.sym := by
    rw [← decodeSym_correct H hH, ht, decodeSym_correct G hG]
  have hb : H.imbalance = G.imbalance := by
    rw [← decodeImbalance_correct H, ht, decodeImbalance_correct G]
  intro S
  have hh := H.two_mul_out S
  rw [hs, hb] at hh
  linarith [G.two_mul_out S]

/-- The same original optimum answers remain valid in each unit competitor. -/
theorem allPairs_certificate (n : ℕ) (hn : 1 ≤ n)
    (G : WeightedDiGraph (Fin n)) (hG : Unit G) :
    ∃ Q : Finset (Finset (Fin n)),
      (Q.card : ℝ) ≤ headlineConstant * (n : ℝ)^2 / Real.log (2 * (n : ℝ)) ∧
      ∃ out : AllPairs.Answers (Fin n), allPairsGood G out ∧
        ∀ H : WeightedDiGraph (Fin n), Unit H → Consistent G H Q →
          (∀ S, H.out S = G.out S) ∧ allPairsGood H out := by
  refine ⟨queries (Fin n), ?_, (honestData G).allPairsAnswers,
    DirectedData.allPairsAnswers_correct _ G rfl rfl, ?_⟩
  · have hcard : ((queries (Fin n)).card : ℝ) ≤ budget (Fin n) := by
      exact_mod_cast queries_card (V := Fin n)
    exact hcard.trans (by
      simpa [headlineConstant] using budget_bound (V := Fin n) (by simpa using hn))
  · intro H hH h
    have he := queries_cut_equivalent G H hG hH h
    refine ⟨he, ?_⟩
    have hg : allPairsGood G (honestData G).allPairsAnswers :=
      DirectedData.allPairsAnswers_correct _ G rfl rfl
    intro s t hst
    simpa only [he] using hg s t hst

end
end CutQueryComplexity.Reconstruction.CompressedDirected
