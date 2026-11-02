import CutQueryComplexity.Graph.EdgeSum
import CutQueryComplexity.Graph.CutConcentration

/-! # Independent sums of random weighted graphs

Graph addition keeps every sampled occurrence. Additive real observables of
the sum have exactly the independent-sum law of their individual observables.
-/

namespace CutQueryComplexity.WeightedGraph
noncomputable section
open scoped Classical ENNReal
open Probability
variable {V : Type}

def independentGraphSum : List (PMF (WeightedGraph V)) → PMF (WeightedGraph V)
  | [] => PMF.pure 0
  | p :: ps => p.bind (fun X => (independentGraphSum ps).map (fun Y => X + Y))

theorem map_independentGraphSum (ps : List (PMF (WeightedGraph V)))
    (f : WeightedGraph V → ℝ) (hzero : f 0 = 0)
    (hadd : ∀ X Y, f (X + Y) = f X + f Y) :
    (independentGraphSum ps).map f = independentSum (ps.map (fun p => p.map f)) := by
  induction ps with
  | nil => simp [independentGraphSum, independentSum, PMF.pure_map, hzero]
  | cons p ps ih =>
      simp only [independentGraphSum, List.map_cons, independentSum, PMF.map_bind,
        PMF.bind_map, Function.comp_def]
      congr 1
      funext X
      calc
        _ = ((independentGraphSum ps).map f).map (fun y => f X + y) := by
          simp only [PMF.map_comp, Function.comp_def, hadd]
        _ = _ := by rw [ih]

theorem HasMean.independent_add {p q : PMF (WeightedGraph V)} {G H : WeightedGraph V}
    (hp : HasMean p G) (hq : HasMean q H) :
    HasMean (p.bind (fun X => q.map (fun Y => X + Y))) (G + H) := by
  intro u v
  have he (X Y : WeightedGraph V) : ENNReal.ofReal ((X + Y).w u v) =
      ENNReal.ofReal (X.w u v) + ENNReal.ofReal (Y.w u v) :=
    ENNReal.ofReal_add (X.nonneg u v) (Y.nonneg u v)
  simp only [expect_bind, expect_map, he, expect_add, expect_const, hp u v, hq u v]

theorem hasMean_independentGraphSum {α : Type*} (xs : List α)
    (p : α → PMF (WeightedGraph V)) (G : α → WeightedGraph V)
    (h : ∀ x ∈ xs, HasMean (p x) (G x)) :
    HasMean (independentGraphSum (xs.map p)) (sumGraphs (xs.map G)) := by
  induction xs with
  | nil => exact hasMean_pure 0
  | cons x xs ih =>
      exact (h x (by simp)).independent_add (ih (fun y hy => h y (by simp [hy])))

/-- Construct the bounded draws, rather than assuming a distributional witness. -/
theorem independentGraphSum_boundedLaw (ps : List (PMF (WeightedGraph V)))
    (f : WeightedGraph V → ℝ) (hzero : f 0 = 0)
    (hadd : ∀ X Y, f (X + Y) = f X + f Y)
    (hb : ∀ p ∈ ps, ∀ X ∈ p.support, 0 ≤ f X ∧ f X ≤ 1) :
    ∃ ds : List BoundedDraw, (independentGraphSum ps).map f = BoundedDraw.sumLaw ds := by
  induction ps with
  | nil => exact ⟨[], by simp [independentGraphSum, BoundedDraw.sumLaw, independentSum,
      PMF.pure_map, hzero]⟩
  | cons p ps ih =>
      obtain ⟨ds, hds⟩ := ih (fun q hq => hb q (by simp [hq]))
      let d := BoundedDraw.ofMap p f (hb p (by simp))
      refine ⟨d :: ds, ?_⟩
      rw [map_independentGraphSum _ f hzero hadd] at hds ⊢
      simp only [List.map_cons, independentSum, BoundedDraw.sumLaw,
        BoundedDraw.ofMap, d, hds]

end
end CutQueryComplexity.WeightedGraph
