import CutQueryComplexity.Primitive.HeavySearch
import CutQueryComplexity.Primitive.CrossSearch

/-! # A crossing edge at least as heavy as the average possible pair -/

namespace CutQueryComplexity
noncomputable section
open scoped Classical
variable {V : Type} [Fintype V] [DecidableEq V]

def findHeavyFromCross (k : ℕ) (S T : Finset V) :
    DTree (Finset V) ℝ (Option V) ((k + 1) * 3) :=
  (findHeavySubset k S).substitute (crossMassQuery S T)

theorem findHeavyFromCross_eval (G : WeightedGraph V) (k : ℕ) {S T : Finset V}
    (h : Disjoint S T) : (findHeavyFromCross k S T).eval G.cut =
      (findHeavySubset k S).eval (subsetSum (crossMass G S T)) := by
  simp only [findHeavyFromCross, DTree.eval_substitute, crossMassQuery_eval G h]

def findHeavyNeighbor (k : ℕ) (u : V) (T : Finset V) :
    DTree (Finset V) ℝ (Option V) ((k + 1) * 3) :=
  (findHeavySubset k T).substitute (neighborMassQuery u T)

theorem findHeavyNeighbor_eval (G : WeightedGraph V) (k : ℕ) (u : V) (T : Finset V) :
    (findHeavyNeighbor k u T).eval G.cut =
      (findHeavySubset k T).eval (subsetSum (restrictWeight (G.w u) T)) := by
  simp only [findHeavyNeighbor, DTree.eval_substitute, neighborMassQuery_eval G u T]

/-- Two logarithmic average searches identify the original endpoints. -/
def findHeavyCross (k : ℕ) (S T : Finset V) :
    DTree (Finset V) ℝ (Option (V × V)) (6 * (k + 1)) :=
  ((findHeavyFromCross k S T).bind fun ou => match ou with
    | none => DTree.pure none
    | some u => (findHeavyNeighbor k u T).map (Option.map fun v => (u, v))).cast (by omega)

theorem findHeavyCross_positive (G : WeightedGraph V) (k : ℕ) {S T : Finset V}
    (h : Disjoint S T) (hn : Fintype.card V ≤ 2 ^ k) (hp : 0 < G.cross S T) :
    ∃ u v, (findHeavyCross k S T).eval G.cut = some (u, v) ∧
      u ∈ S ∧ v ∈ T ∧ 0 < G.w u v ∧
        G.cross S T ≤ (S.card : ℝ) * T.card * G.w u v := by
  have hS : S.card ≤ 2 ^ k := (Finset.card_le_univ S).trans hn
  have hT : T.card ≤ 2 ^ k := (Finset.card_le_univ T).trans hn
  obtain ⟨u, heu, hu, hrow, hav⟩ := findHeavySubset_positive (crossMass G S T) k S hS
    (by simpa [subsetSum_crossMass] using hp)
  have hefirst : (findHeavyFromCross k S T).eval G.cut = some u := by
    rw [findHeavyFromCross_eval G k h]; exact heu
  have hrow' : 0 < ∑ v ∈ T, G.w u v := by simpa [crossMass, restrictWeight, hu] using hrow
  have hav' : G.cross S T ≤ (S.card : ℝ) * ∑ v ∈ T, G.w u v := by
    rw [subsetSum_crossMass, Finset.inter_self] at hav
    simpa only [crossMass, restrictWeight, ite_eq_left hu] using hav
  obtain ⟨v, hev, hv, hw, havv⟩ := findHeavySubset_positive (restrictWeight (G.w u) T) k T hT
    (by simpa [subsetSum_restrict] using hrow')
  have hesecond : (findHeavyNeighbor k u T).eval G.cut = some v := by
    rw [findHeavyNeighbor_eval]; exact hev
  have hw' : 0 < G.w u v := by simpa [restrictWeight, hv] using hw
  have havv' : (∑ v ∈ T, G.w u v) ≤ (T.card : ℝ) * G.w u v := by
    simpa [subsetSum_restrict, restrictWeight, hv] using havv
  refine ⟨u, v, ?_, hu, hv, hw', ?_⟩
  · simp [findHeavyCross, DTree.eval_bind, hefirst, hesecond]
  · calc
      _ ≤ (S.card : ℝ) * ∑ v ∈ T, G.w u v := hav'
      _ ≤ (S.card : ℝ) * ((T.card : ℝ) * G.w u v) :=
        mul_le_mul_of_nonneg_left havv' (Nat.cast_nonneg _)
      _ = _ := by ring

theorem findHeavyCross_zero (G : WeightedGraph V) (k : ℕ) {S T : Finset V}
    (h : Disjoint S T) (hz : G.cross S T = 0) :
    (findHeavyCross k S T).eval G.cut = none := by
  have he : (findHeavyFromCross k S T).eval G.cut = none := by
    rw [findHeavyFromCross_eval G k h]
    exact findHeavySubset_zero _ _ _ (by simpa [subsetSum_crossMass] using hz)
  simp [findHeavyCross, DTree.eval_bind, he]

def HeavyCrossResult (G : WeightedGraph V) (S T : Finset V) : Option (V × V) → Prop
  | none => G.cross S T = 0
  | some (u, v) => u ∈ S ∧ v ∈ T ∧ 0 < G.w u v ∧
      G.cross S T ≤ (S.card : ℝ) * T.card * G.w u v

theorem findHeavyCross_correct (G : WeightedGraph V) (k : ℕ) {S T : Finset V}
    (h : Disjoint S T) (hn : Fintype.card V ≤ 2 ^ k) :
    HeavyCrossResult G S T ((findHeavyCross k S T).eval G.cut) := by
  by_cases hp : 0 < G.cross S T
  · obtain ⟨u, v, he, hu, hv, hw, hav⟩ := findHeavyCross_positive G k h hn hp
    rw [he]
    exact ⟨hu, hv, hw, hav⟩
  · have hz := le_antisymm (le_of_not_gt hp) (G.cross_nonneg S T)
    rw [findHeavyCross_zero G k h hz]
    exact hz

end
end CutQueryComplexity
