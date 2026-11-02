import CutQueryComplexity.Graph.Operations
import CutQueryComplexity.Probability.Expectation

/-! # Expected weighted graphs

A random graph is a PMF on weighted graphs. `HasMean` specifies its edgewise
nonnegative expectations and therefore certifies finiteness. A real-valued
expected graph is constructed only with a proof of finite edge expectations.
Zero mean edges vanish at every supported outcome.
-/

namespace CutQueryComplexity
namespace WeightedGraph
noncomputable section
open scoped Classical ENNReal
open Probability
variable {V : Type}

def HasFiniteMean (p : PMF (WeightedGraph V)) : Prop :=
  ∀ u v, expect p (fun X => ENNReal.ofReal (X.w u v)) ≠ ∞

def HasMean (p : PMF (WeightedGraph V)) (G : WeightedGraph V) : Prop :=
  ∀ u v, expect p (fun X => ENNReal.ofReal (X.w u v)) = ENNReal.ofReal (G.w u v)

def expectedGraph (p : PMF (WeightedGraph V)) (_hf : HasFiniteMean p) : WeightedGraph V where
  w u v := (expect p (fun X => ENNReal.ofReal (X.w u v))).toReal
  symm u v := by simp only [WeightedGraph.symm]
  nonneg _ _ := ENNReal.toReal_nonneg
  diag v := by simp only [WeightedGraph.diag, ENNReal.ofReal_zero, expect_const, ENNReal.toReal_zero]

theorem HasMean.finite {p : PMF (WeightedGraph V)} {G : WeightedGraph V} (h : HasMean p G) :
    HasFiniteMean p := fun u v => by rw [h u v]; exact ENNReal.ofReal_ne_top

theorem hasMean_expectedGraph (p : PMF (WeightedGraph V)) (hf : HasFiniteMean p) :
    HasMean p (expectedGraph p hf) := by
  intro u v
  exact (ENNReal.ofReal_toReal (hf u v)).symm

theorem hasFiniteMean_iff (p : PMF (WeightedGraph V)) :
    HasFiniteMean p ↔ ∃ G, HasMean p G :=
  ⟨fun hf => ⟨expectedGraph p hf, hasMean_expectedGraph p hf⟩,
    fun ⟨_, h⟩ => h.finite⟩

theorem HasMean.unique {p : PMF (WeightedGraph V)} {G H : WeightedGraph V}
    (hG : HasMean p G) (hH : HasMean p H) : G = H := by
  ext u v
  have h := congrArg ENNReal.toReal ((hG u v).symm.trans (hH u v))
  simpa only [ENNReal.toReal_ofReal (G.nonneg u v), ENNReal.toReal_ofReal (H.nonneg u v)] using h

@[simp] theorem hasMean_pure (G : WeightedGraph V) : HasMean (PMF.pure G) G := by
  intro u v
  exact expect_pure G _

theorem hasFiniteMean_of_bounded (p : PMF (WeightedGraph V)) (M : V → V → ℝ)
    (h : ∀ X ∈ p.support, ∀ u v, X.w u v ≤ M u v) : HasFiniteMean p := by
  intro u v
  exact ne_of_lt ((expect_le_of_le_on_support p
    (fun X hX => ENNReal.ofReal_le_ofReal (h X hX u v))).trans_lt ENNReal.ofReal_lt_top)

/-- Original-edge support follows from the mean identity, without an extra assumption. -/
theorem HasMean.support {p : PMF (WeightedGraph V)} {G : WeightedGraph V}
    (h : HasMean p G) {X : WeightedGraph V} (hX : X ∈ p.support) : X.support ≤ G.support := by
  intro u v hx
  change G.w u v ≠ 0
  intro hz
  have he : expect p (fun Y => ENNReal.ofReal (Y.w u v)) = 0 := by
    rw [h u v, hz, ENNReal.ofReal_zero]
  have hzero := (expect_eq_zero_iff p _).mp he X hX
  exact hx (le_antisymm (ENNReal.ofReal_eq_zero.mp hzero) (X.nonneg u v))

theorem ofReal_cross (G : WeightedGraph V) (S T : Finset V) :
    ENNReal.ofReal (G.cross S T) = ∑ u ∈ S, ∑ v ∈ T, ENNReal.ofReal (G.w u v) := by
  rw [cross, ENNReal.ofReal_sum_of_nonneg (fun u _ =>
    Finset.sum_nonneg (fun v _ => G.nonneg u v))]
  apply Finset.sum_congr rfl
  intro u _
  exact ENNReal.ofReal_sum_of_nonneg (fun v _ => G.nonneg u v)

theorem HasMean.cross {p : PMF (WeightedGraph V)} {G : WeightedGraph V}
    (h : HasMean p G) (S T : Finset V) :
    expect p (fun X => ENNReal.ofReal (X.cross S T)) = ENNReal.ofReal (G.cross S T) := by
  simp only [ofReal_cross, expect_sum]
  exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => h u v

theorem HasMean.cut [Fintype V] [DecidableEq V] {p : PMF (WeightedGraph V)} {G : WeightedGraph V}
    (h : HasMean p G) (S : Finset V) :
    expect p (fun X => ENNReal.ofReal (X.cut S)) = ENNReal.ofReal (G.cut S) := h.cross S Sᶜ

theorem HasMean.scale {p : PMF (WeightedGraph V)} {G : WeightedGraph V}
    (h : HasMean p G) (c : ℝ) (hc : 0 ≤ c) :
    HasMean (p.map (fun X => X.scale c hc)) (G.scale c hc) := by
  intro u v
  simp only [expect_map, WeightedGraph.scale, ENNReal.ofReal_mul hc, expect_const_mul]
  rw [h u v]

theorem HasMean.induce [DecidableEq V] {p : PMF (WeightedGraph V)} {G : WeightedGraph V}
    (h : HasMean p G) (U : Finset V) :
    HasMean (p.map (fun X => X.induce U)) (G.induce U) := by
  intro u v
  rw [expect_map]
  by_cases hm : u ∈ U ∧ v ∈ U
  · simpa only [WeightedGraph.induce, ite_eq_left hm] using h u v
  · simp only [WeightedGraph.induce, ite_eq_right hm, ENNReal.ofReal_zero, expect_const]

end
end WeightedGraph
end CutQueryComplexity
