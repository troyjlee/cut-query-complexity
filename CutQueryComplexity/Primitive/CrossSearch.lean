import CutQueryComplexity.Primitive.BinarySearch

/-! # Logarithmic crossing-edge search with original-edge witnesses -/

namespace CutQueryComplexity

noncomputable section
open scoped Classical

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Restrict the support of a nonnegative weight vector to a public set. -/
def restrictWeight (w : V → ℝ) (S : Finset V) (u : V) : ℝ := if u ∈ S then w u else 0

theorem subsetSum_restrict (w : V → ℝ) (S A : Finset V) :
    subsetSum (restrictWeight w S) A = ∑ u ∈ A ∩ S, w u := by
  have he : A ∩ S = A.filter (fun u => u ∈ S) := by ext; simp
  simp [subsetSum, restrictWeight, he]

theorem restrictWeight_nonneg (w : V → ℝ) (hw : ∀ u, 0 ≤ w u) (S : Finset V) (u : V) :
    0 ≤ restrictWeight w S u := by
  unfold restrictWeight
  split
  · exact hw u
  · exact le_rfl

theorem restrictWeight_pos (w : V → ℝ) (S : Finset V) (u : V) :
    0 < restrictWeight w S u ↔ u ∈ S ∧ 0 < w u := by
  by_cases h : u ∈ S <;> simp [restrictWeight, h]

/-- The mass of each potential first endpoint of a crossing edge. -/
def crossMass (G : WeightedGraph V) (S T : Finset V) : V → ℝ :=
  restrictWeight (fun u => ∑ v ∈ T, G.w u v) S

theorem crossMass_nonneg (G : WeightedGraph V) (S T : Finset V) (u : V) :
    0 ≤ crossMass G S T u :=
  restrictWeight_nonneg _ (fun u => Finset.sum_nonneg (fun v _ => G.nonneg u v)) S u

theorem subsetSum_crossMass (G : WeightedGraph V) (S T A : Finset V) :
    subsetSum (crossMass G S T) A = G.cross (A ∩ S) T :=
  subsetSum_restrict _ S A

/-- Decode a first-endpoint subset sum by intersecting the public candidate set. -/
def crossMassQuery (S T A : Finset V) : DTree (Finset V) ℝ ℝ 3 := crossQuery (A ∩ S) T

theorem crossMassQuery_eval (G : WeightedGraph V) {S T : Finset V} (h : Disjoint S T)
    (A : Finset V) : (crossMassQuery S T A).eval G.cut = subsetSum (crossMass G S T) A := by
  rw [crossMassQuery, crossQuery_eval G (h.mono_left Finset.inter_subset_right),
    subsetSum_crossMass]

/-- Query a neighbor-weight subset sum, removing the zero diagonal explicitly. -/
def neighborMassQuery (u : V) (T A : Finset V) : DTree (Finset V) ℝ ℝ 3 :=
  crossQuery {u} ((A ∩ T) \ {u})

theorem neighborMassQuery_eval (G : WeightedGraph V) (u : V) (T A : Finset V) :
    (neighborMassQuery u T A).eval G.cut = subsetSum (restrictWeight (G.w u) T) A := by
  rw [neighborMassQuery, crossQuery_eval G Finset.disjoint_sdiff, subsetSum_restrict]
  simp only [WeightedGraph.cross, Finset.sum_singleton]
  apply Finset.sum_subset Finset.sdiff_subset
  intro v hv hn
  have h : v = u := by simpa [Finset.mem_sdiff, hv] using hn
  subst v
  exact G.diag u

def findFromCross (k : ℕ) (S T : Finset V) :
    DTree (Finset V) ℝ (Option V) ((k + 1) * 3) :=
  (findPositive k Finset.univ).substitute (crossMassQuery S T)

theorem findFromCross_correct (G : WeightedGraph V) (k : ℕ) {S T : Finset V}
    (h : Disjoint S T) (hn : Fintype.card V ≤ 2 ^ k) :
    PositiveResult (crossMass G S T) Finset.univ ((findFromCross k S T).eval G.cut) := by
  have he : (fun A => (crossMassQuery S T A).eval G.cut) = subsetSum (crossMass G S T) :=
    funext (crossMassQuery_eval G h)
  rw [findFromCross, DTree.eval_substitute, he]
  exact findPositive_correct _ (crossMass_nonneg G S T) k _ (by simpa using hn)

def findNeighbor (k : ℕ) (u : V) (T : Finset V) :
    DTree (Finset V) ℝ (Option V) ((k + 1) * 3) :=
  (findPositive k Finset.univ).substitute (neighborMassQuery u T)

theorem findNeighbor_correct (G : WeightedGraph V) (k : ℕ) (u : V) (T : Finset V)
    (hn : Fintype.card V ≤ 2 ^ k) :
    PositiveResult (restrictWeight (G.w u) T) Finset.univ ((findNeighbor k u T).eval G.cut) := by
  have he : (fun A => (neighborMassQuery u T A).eval G.cut) =
      subsetSum (restrictWeight (G.w u) T) := funext (neighborMassQuery_eval G u T)
  rw [findNeighbor, DTree.eval_substitute, he]
  exact findPositive_correct _ (restrictWeight_nonneg _ (G.nonneg u) T) k _ (by simpa using hn)

/-- None certifies zero cross weight; a returned pair names a positive original edge. -/
def CrossResult (G : WeightedGraph V) (S T : Finset V) : Option (V × V) → Prop
  | none => G.cross S T = 0
  | some (u, v) => u ∈ S ∧ v ∈ T ∧ 0 < G.w u v

/-- Search both endpoints. Absence is a successful output, not an exceptional case. -/
def findCross (k : ℕ) (S T : Finset V) :
    DTree (Finset V) ℝ (Option (V × V)) (6 * (k + 1)) :=
  ((findFromCross k S T).bind fun ou => match ou with
    | none => DTree.pure none
    | some u => (findNeighbor k u T).map (fun ov => ov.map (fun v => (u, v)))).cast (by omega)

theorem findCross_correct (G : WeightedGraph V) (k : ℕ) {S T : Finset V}
    (hST : Disjoint S T) (hn : Fintype.card V ≤ 2 ^ k) :
    CrossResult G S T ((findCross k S T).eval G.cut) := by
  have hfirst := findFromCross_correct G k hST hn
  unfold findCross
  simp only [DTree.eval, DTree.run_cast]
  change CrossResult G S T (DTree.eval _ G.cut)
  rw [DTree.eval_bind]
  cases he : (findFromCross k S T).eval G.cut with
  | none =>
      simp only [he, PositiveResult] at hfirst
      simp only [DTree.eval_pure, CrossResult]
      have hz : subsetSum (crossMass G S T) Finset.univ = 0 :=
        Finset.sum_eq_zero hfirst
      simpa [subsetSum_crossMass] using hz
  | some u =>
      simp only [he, PositiveResult] at hfirst
      have hu := (restrictWeight_pos _ S u).mp hfirst.2
      have hsecond := findNeighbor_correct G k u T hn
      rw [DTree.eval_map]
      cases hv : (findNeighbor k u T).eval G.cut with
      | none =>
          simp only [hv, PositiveResult] at hsecond
          have hz : subsetSum (restrictWeight (G.w u) T) Finset.univ = 0 :=
            Finset.sum_eq_zero hsecond
          have : (∑ v ∈ T, G.w u v) = 0 := by simpa [subsetSum_restrict] using hz
          exact False.elim (by linarith [hu.2])
      | some v =>
          simp only [hv, PositiveResult] at hsecond
          have hv' := (restrictWeight_pos _ T v).mp hsecond.2
          exact ⟨hu.1, hv'.1, hv'.2⟩

/-- Uniform logarithmic cut-query crossing-edge search on any finite vertex set. -/
theorem findCross_logarithmic (G : WeightedGraph V) {S T : Finset V}
    (h : Disjoint S T) :
    CrossResult G S T ((findCross (searchDepth V) S T).eval G.cut) :=
  findCross_correct G _ h (Nat.le_pow_clog (by decide) _)

end
end CutQueryComplexity
