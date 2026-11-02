import CutQueryComplexity.Graph.IndependentSum
import CutQueryComplexity.Probability.Categorical
import Mathlib.Tactic.FieldSimp

/-! # Count every weight-proportional sample

A positive-mass bucket takes a positive, fixed number of independent draws.
Each selected edge contributes mass/count, and repeated edges are added.
Buckets may use either orientation as an edge name. Their reference graphs
add all listed weights, so no disjointness or orientation convention is hidden.
This file defines the sampling law; query programs and adaptive bucket
construction are separate obligations.
-/

namespace CutQueryComplexity.WeightedGraph
noncomputable section
open scoped Classical ENNReal
open Probability

structure CountedBucket (V : Type) [Fintype V] where
  weight : EdgeIndex V → ℝ
  nonneg : ∀ e, 0 ≤ weight e
  positive : 0 < ∑ e, weight e
  count : ℕ
  count_pos : 0 < count

namespace CountedBucket
variable {V : Type} [Fintype V]

def mass (b : CountedBucket V) : ℝ := ∑ e, b.weight e

theorem mass_pos (b : CountedBucket V) : 0 < b.mass := b.positive

def graph (b : CountedBucket V) : WeightedGraph V :=
  finiteSum Finset.univ (fun e => edgeGraph e (b.weight e) (b.nonneg e))

def drawLaw (b : CountedBucket V) : PMF (WeightedGraph V) :=
  (categorical b.weight b.nonneg b.positive).map
    (fun e => edgeGraph e (b.mass / b.count) (div_nonneg b.mass_pos.le (Nat.cast_nonneg _)))

theorem mem_support_drawLaw (b : CountedBucket V) (X : WeightedGraph V) :
    X ∈ b.drawLaw.support ↔ ∃ e, 0 < b.weight e ∧
      edgeGraph e (b.mass / b.count) (div_nonneg b.mass_pos.le (Nat.cast_nonneg _)) = X := by
  simp only [drawLaw, PMF.mem_support_map_iff, mem_support_categorical]

/-- One occurrence has mean equal to one count-th of the bucket graph. -/
theorem drawLaw_mean (b : CountedBucket V) :
    HasMean b.drawLaw (b.graph.scale (1 / b.count) (by positivity)) := by
  intro u v
  rw [drawLaw, expect_map, expect_categorical _ _ _ _ (fun e => (edgeGraph e _ _).nonneg u v)]
  apply congrArg ENNReal.ofReal
  change (∑ e, b.weight e * (edgeGraph e (b.mass / b.count) _).w u v) / b.mass =
    (1 / b.count) * ∑ e, (edgeGraph e (b.weight e) (b.nonneg e)).w u v
  rw [Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  have hm : b.mass ≠ 0 := ne_of_gt b.mass_pos
  have hr : (b.count : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt b.count_pos
  simp only [edgeGraph]
  split_ifs <;> field_simp <;> ring

/-- One list entry for each draw, with bucket-dependent counts. -/
def expanded (bs : List (CountedBucket V)) : List (CountedBucket V) :=
  bs.flatMap (fun b => List.replicate b.count b)

def reference (bs : List (CountedBucket V)) : WeightedGraph V := sumGraphs (bs.map graph)

def sampleLaw (bs : List (CountedBucket V)) : PMF (WeightedGraph V) :=
  independentGraphSum ((expanded bs).map drawLaw)

@[simp] theorem expanded_length (bs : List (CountedBucket V)) :
    (expanded bs).length = (bs.map count).sum := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      change (List.replicate b.count b ++ expanded bs).length = b.count + (bs.map count).sum
      rw [List.length_append, List.length_replicate, ih]

theorem mem_of_mem_expanded {bs : List (CountedBucket V)} {b : CountedBucket V}
    (hb : b ∈ expanded bs) : b ∈ bs := by
  obtain ⟨a, ha, hb⟩ := List.mem_flatMap.mp hb
  have he := (List.mem_replicate.mp hb).2
  simpa only [he] using ha

theorem sum_draw_means (bs : List (CountedBucket V)) :
    sumGraphs ((expanded bs).map (fun b => b.graph.scale (1 / b.count) (by positivity))) =
      reference bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      change sumGraphs ((List.replicate b.count b ++ expanded bs).map _) =
        b.graph + reference bs
      rw [List.map_append, List.map_replicate, sumGraphs_append,
        sumGraphs_replicate_scale b.graph b.count_pos, ih]

/-- The aggregated sampler is unbiased, including for an empty bucket list. -/
theorem sampleLaw_mean (bs : List (CountedBucket V)) : HasMean (sampleLaw bs) (reference bs) := by
  have h := hasMean_independentGraphSum (expanded bs) drawLaw
    (fun b => b.graph.scale (1 / b.count) (by positivity)) (fun b _ => b.drawLaw_mean)
  rwa [sum_draw_means] at h

theorem sampleLaw_support (bs : List (CountedBucket V)) {X : WeightedGraph V}
    (hX : X ∈ (sampleLaw bs).support) : X.support ≤ (reference bs).support :=
  (sampleLaw_mean bs).support hX

@[simp] theorem sampleLaw_nil : sampleLaw ([] : List (CountedBucket V)) = PMF.pure 0 := rfl

end CountedBucket
end
end CutQueryComplexity.WeightedGraph
