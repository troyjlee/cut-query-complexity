import CutQueryComplexity.Primitive.SubsetSample
import CutQueryComplexity.Primitive.CrossSearch
import CutQueryComplexity.Model.RandomizedReduction
import CutQueryComplexity.Probability.PairSample

/-! # Exact weight-proportional original-edge sampling in logarithmically many cut queries -/
namespace CutQueryComplexity
noncomputable section
open scoped Classical ENNReal
open Probability
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Sample a first endpoint according to the weight crossing to `T`. -/
def sampleFromCross (k : ℕ) (S T : Finset V) :
    RTree (Finset V) ℝ (Option V) ((2 * k + 1) * 3) :=
  (sampleSubset k Finset.univ).substitute (crossMassQuery S T)

theorem sampleFromCross_eval (G : WeightedGraph V) (k : ℕ) {S T : Finset V}
    (h : Disjoint S T) : (sampleFromCross k S T).eval G.cut =
      (sampleSubset k Finset.univ).eval (subsetSum (crossMass G S T)) := by
  simp only [sampleFromCross, RTree.eval_substitute, crossMassQuery_eval G h]

/-- Neighbors are sampled by edge weight, including on integral multigraph inputs. -/
def sampleNeighbor (k : ℕ) (u : V) (T : Finset V) :
    RTree (Finset V) ℝ (Option V) ((2 * k + 1) * 3) :=
  (sampleSubset k Finset.univ).substitute (neighborMassQuery u T)

theorem sampleNeighbor_eval (G : WeightedGraph V) (k : ℕ) (u : V) (T : Finset V) :
    (sampleNeighbor k u T).eval G.cut =
      (sampleSubset k Finset.univ).eval (subsetSum (restrictWeight (G.w u) T)) := by
  simp only [sampleNeighbor, RTree.eval_substitute, neighborMassQuery_eval G u T]

/-- The exact neighbor law divides the edge weight by the weight of the candidate neighborhood. -/
theorem sampleNeighbor_law (G : WeightedGraph V) (k : ℕ) (u v : V) (T : Finset V)
    (hn : Fintype.card V ≤ 2 ^ k) (hp : 0 < ∑ x ∈ T, G.w u x) :
    ((sampleNeighbor k u T).eval G.cut) (some v) =
      (if v ∈ T then ENNReal.ofReal (G.w u v) else 0) /
        ENNReal.ofReal (∑ x ∈ T, G.w u x) := by
  rw [sampleNeighbor_eval]
  have hs := sampleSubset_law _ (restrictWeight_nonneg _ (G.nonneg u) T) k Finset.univ
    (by simpa using hn) (by simpa [subsetSum_restrict] using hp) (some v)
  by_cases hv : v ∈ T <;>
    simpa [subsetSum_restrict, outputMass, restrictWeight, hv] using hs

/-- On simple graphs, every eligible neighbor has the same probability. -/
theorem sampleNeighbor_uniform (F : _root_.SimpleGraph V) (u v : V) (T : Finset V)
    (hv : v ∈ T) (hadj : F.Adj u v) :
    ((sampleNeighbor (searchDepth V) u T).eval (SimpleGraph.toWeighted F).cut) (some v) =
      1 / ((T.filter (F.Adj u)).card : ℝ≥0∞) := by
  have hsum : (∑ x ∈ T, (SimpleGraph.toWeighted F).w u x) =
      ((T.filter (F.Adj u)).card : ℝ) := by
    simp only [SimpleGraph.toWeighted_w]
    rw [Finset.card_filter]
    push_cast
    rfl
  have hc : 0 < (T.filter (F.Adj u)).card :=
    Finset.card_pos.mpr ⟨v, by simp [hv, hadj]⟩
  have hp : 0 < ∑ x ∈ T, (SimpleGraph.toWeighted F).w u x := by
    rw [hsum]; exact_mod_cast hc
  rw [sampleNeighbor_law (SimpleGraph.toWeighted F) (searchDepth V) u v T
    (Nat.le_pow_clog (by decide) _) hp]
  simp [hv, SimpleGraph.toWeighted_w, hadj, hsum]

/-- Return original endpoints, with budget `12*k+6`. -/
def sampleCross (k : ℕ) (S T : Finset V) :
    RTree (Finset V) ℝ (Option (V × V)) (6 * (2 * k + 1)) :=
  ((sampleFromCross k S T).bind fun ou => match ou with
    | none => RTree.pure (PMF.pure none)
    | some u => (sampleNeighbor k u T).map (Option.map (fun v => (u, v)))).cast (by omega)

theorem sampleCross_eval (G : WeightedGraph V) (k : ℕ) (S T : Finset V) :
    (sampleCross k S T).eval G.cut = pairSample ((sampleFromCross k S T).eval G.cut)
      (fun u => (sampleNeighbor k u T).eval G.cut) := by
  simp only [sampleCross, RTree.eval_cast, RTree.eval_bind, pairSample]
  congr 1
  funext ou
  cases ou <;> simp

theorem sampleFromCross_scaled (G : WeightedGraph V) (k : ℕ) {S T : Finset V}
    (h : Disjoint S T) (hn : Fintype.card V ≤ 2 ^ k) (o : Option V) :
    ENNReal.ofReal (G.cross S T) * ((sampleFromCross k S T).eval G.cut) o =
      outputMass (crossMass G S T) Finset.univ o := by
  rw [sampleFromCross_eval G k h]
  have hs := sampleSubset_scaled _ (crossMass_nonneg G S T) k Finset.univ
    (by simpa using hn) o
  simpa only [subsetSum_crossMass, Finset.univ_inter] using hs

theorem sampleNeighbor_scaled (G : WeightedGraph V) (k : ℕ) (u : V) (T : Finset V)
    (hn : Fintype.card V ≤ 2 ^ k) (o : Option V) :
    ENNReal.ofReal (∑ v ∈ T, G.w u v) * ((sampleNeighbor k u T).eval G.cut) o =
      outputMass (restrictWeight (G.w u) T) Finset.univ o := by
  rw [sampleNeighbor_eval]
  have hs := sampleSubset_scaled _ (restrictWeight_nonneg _ (G.nonneg u) T) k Finset.univ
    (by simpa using hn) o
  simpa only [subsetSum_restrict, Finset.univ_inter] using hs

/-- Exact edge-mass identity; no connectivity or positive-weight promise is necessary. -/
theorem sampleCross_scaled (G : WeightedGraph V) (k : ℕ) {S T : Finset V}
    (h : Disjoint S T) (hn : Fintype.card V ≤ 2 ^ k) (u v : V) :
    ENNReal.ofReal (G.cross S T) * ((sampleCross k S T).eval G.cut) (some (u, v)) =
      if u ∈ S ∧ v ∈ T then ENNReal.ofReal (G.w u v) else 0 := by
  rw [sampleCross_eval, pairSample_some, ← mul_assoc, sampleFromCross_scaled G k h hn]
  by_cases hu : u ∈ S
  · simp only [outputMass, Finset.mem_univ, ↓reduceIte, crossMass, restrictWeight, hu]
    rw [sampleNeighbor_scaled G k u T hn]
    by_cases hv : v ∈ T <;> simp [outputMass, restrictWeight, hu, hv]
  · simp [outputMass, crossMass, restrictWeight, hu]

/-- Positive crossing mass never returns absence. -/
theorem sampleCross_none_scaled (G : WeightedGraph V) (k : ℕ) {S T : Finset V}
    (h : Disjoint S T) (hn : Fintype.card V ≤ 2 ^ k) :
    ENNReal.ofReal (G.cross S T) * ((sampleCross k S T).eval G.cut) none = 0 := by
  rw [sampleCross_eval, pairSample_none, mul_add, Finset.mul_sum,
    sampleFromCross_scaled G k h hn]
  simp only [outputMass, zero_add, ← mul_assoc]
  apply Finset.sum_eq_zero
  intro u _
  rw [sampleFromCross_scaled G k h hn]
  by_cases hu : u ∈ S
  · simp only [outputMass, Finset.mem_univ, ↓reduceIte, crossMass, restrictWeight, hu]
    rw [sampleNeighbor_scaled G k u T hn]
    rfl
  · simp [outputMass, crossMass, restrictWeight, hu]

theorem sampleCross_none (G : WeightedGraph V) (k : ℕ) {S T : Finset V}
    (h : Disjoint S T) (hn : Fintype.card V ≤ 2 ^ k) (hp : 0 < G.cross S T) :
    ((sampleCross k S T).eval G.cut) none = 0 := by
  exact (mul_eq_zero.mp (sampleCross_none_scaled G k h hn)).resolve_left
    (ne_of_gt (ENNReal.ofReal_pos.mpr hp))

/-- A zero cross weight returns absence with probability one. -/
theorem sampleCross_zero (G : WeightedGraph V) (k : ℕ) {S T : Finset V}
    (h : Disjoint S T) (hz : G.cross S T = 0) :
    (sampleCross k S T).eval G.cut = PMF.pure none := by
  rw [sampleCross_eval, sampleFromCross_eval G k h,
    sampleSubset_zero _ k _ (by simpa [subsetSum_crossMass] using hz)]
  simp [pairSample]

/-- Every supported output is a positive original edge or a valid absence certificate. -/
theorem sampleCross_correct (G : WeightedGraph V) (k : ℕ) {S T : Finset V}
    (h : Disjoint S T) (hn : Fintype.card V ≤ 2 ^ k) (o : Option (V × V))
    (ho : o ∈ ((sampleCross k S T).eval G.cut).support) : CrossResult G S T o := by
  have hprob : ((sampleCross k S T).eval G.cut) o ≠ 0 := by
    simpa only [PMF.mem_support_iff] using ho
  by_cases hz : G.cross S T = 0
  · rw [sampleCross_zero G k h hz] at ho
    have he := (PMF.mem_support_pure_iff _ _).mp ho
    subst o
    exact hz
  · have hp : 0 < G.cross S T := lt_of_le_of_ne (G.cross_nonneg S T) (Ne.symm hz)
    cases o with
    | none => exact False.elim (hprob (sampleCross_none G k h hn hp))
    | some uv =>
        obtain ⟨u, v⟩ := uv
        have hm : (if u ∈ S ∧ v ∈ T then ENNReal.ofReal (G.w u v) else 0) ≠ 0 := by
          rw [← sampleCross_scaled G k h hn]
          exact mul_ne_zero (ne_of_gt (ENNReal.ofReal_pos.mpr hp)) hprob
        have huv : u ∈ S ∧ v ∈ T := by
          by_contra hh; simp [hh] at hm
        rw [ite_eq_left huv] at hm
        exact ⟨huv.1, huv.2, lt_of_not_ge (fun hw => hm (ENNReal.ofReal_eq_zero.mpr hw))⟩

/-- Exact weight-proportional law, with the original endpoints retained. -/
theorem sampleCross_law (G : WeightedGraph V) (k : ℕ) {S T : Finset V}
    (h : Disjoint S T) (hn : Fintype.card V ≤ 2 ^ k) (hp : 0 < G.cross S T) (u v : V) :
    ((sampleCross k S T).eval G.cut) (some (u, v)) =
      (if u ∈ S ∧ v ∈ T then ENNReal.ofReal (G.w u v) else 0) /
        ENNReal.ofReal (G.cross S T) := by
  have hnz : ENNReal.ofReal (G.cross S T) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hp)
  apply (ENNReal.mul_right_inj hnz ENNReal.ofReal_ne_top).mp
  rw [sampleCross_scaled G k h hn, div_eq_mul_inv, mul_left_comm,
    ENNReal.mul_inv_cancel hnz ENNReal.ofReal_ne_top, mul_one]

/-- The logarithmic specialization makes the budget independent of the input weights. -/
theorem sampleCross_logarithmic (G : WeightedGraph V) {S T : Finset V}
    (h : Disjoint S T) (hp : 0 < G.cross S T) (u v : V) :
    ((sampleCross (searchDepth V) S T).eval G.cut) (some (u, v)) =
      (if u ∈ S ∧ v ∈ T then ENNReal.ofReal (G.w u v) else 0) /
        ENNReal.ofReal (G.cross S T) :=
  sampleCross_law G _ h (Nat.le_pow_clog (by decide) _) hp u v

/-- Natural capacities give the endpoint distribution of a uniformly selected edge copy.
Different parallel copies share endpoints, so their multiplicities occur in the numerator. -/
theorem sampleCross_capacity {W : ℕ} (G : CapacityGraph V W) {S T : Finset V}
    (h : Disjoint S T) (hp : 0 < G.toWeighted.cross S T) (u v : V)
    (hu : u ∈ S) (hv : v ∈ T) :
    ((sampleCross (searchDepth V) S T).eval G.toWeighted.cut) (some (u, v)) =
      ((G.w u v : ℕ) : ℝ≥0∞) / (∑ a ∈ S, ∑ b ∈ T, ((G.w a b : ℕ) : ℝ≥0∞)) := by
  rw [sampleCross_logarithmic G.toWeighted h hp]
  simp only [hu, hv, and_self, ↓reduceIte, CapacityGraph.toWeighted,
    WeightedGraph.cross, ENNReal.ofReal_natCast]
  congr 1
  rw [ENNReal.ofReal_sum_of_nonneg (fun a _ =>
    Finset.sum_nonneg (fun b _ => Nat.cast_nonneg (G.w a b : ℕ)))]
  apply Finset.sum_congr rfl
  intro a _
  rw [ENNReal.ofReal_sum_of_nonneg (fun b _ => Nat.cast_nonneg (G.w a b : ℕ))]
  simp only [ENNReal.ofReal_natCast]

end
end CutQueryComplexity
