import CutQueryComplexity.Sparsification.EstimationBudget

/-! # Output draws from a recorded merge event

A merge event records a labeling `π`, an exact cache, and a group `K` of labels.
Its bucket consists of the original edges inside `pull π K` whose blocks differ,
and its mass is the residual mass `M` of `K`. One call of the ordered residual
sampler returns such an edge with probability `w/(2M)` per orientation. Keeping the
original endpoints and weighting the edge by `M/r` gives exactly one counted draw
of `outBucket`, whose weights are half the original weights on ordered bucket pairs.

`sumDraws` repeats any draw program `r` times and adds the graphs; its output law is
the independent sum. With the residual sampler it realizes the counted sample of
one bucket.
-/

namespace CutQueryComplexity.WeightedGraph
noncomputable section
open scoped Classical ENNReal
open Probability
variable {V : Type} [Fintype V]

/-! ### The bucket of an event -/

/-- Half the original weight on each ordered pair of the bucket. -/
def bucketWeight (G : WeightedGraph V) (π : V → V) (T : Finset V) (e : EdgeIndex V) : ℝ :=
  if π e.val.1 ∈ T ∧ π e.val.2 ∈ T ∧ π e.val.1 ≠ π e.val.2 then G.w e.val.1 e.val.2 / 2 else 0

omit [Fintype V] in
theorem bucketWeight_nonneg (G : WeightedGraph V) (π : V → V) (T : Finset V) (e : EdgeIndex V) :
    0 ≤ bucketWeight G π T e := by
  unfold bucketWeight
  split <;> first | exact le_rfl | exact div_nonneg (G.nonneg _ _) (by norm_num)

theorem sum_bucketWeight (G : WeightedGraph V) (π : V → V) (T : Finset V)
    [inst : Fintype (EdgeIndex V)] :
    ∑ e, bucketWeight G π T e = (G.contract π).internalMass T := by
  obtain rfl : inst = Subtype.fintype _ := Subsingleton.elim _ _
  have := sum_edgeIndex (B := V)
    (f := fun p => if π p.1 ∈ T ∧ π p.2 ∈ T ∧ π p.1 ≠ π p.2 then G.w p.1 p.2 / 2 else 0)
    (fun a => by simp)
  simp only [bucketWeight] at this ⊢
  rw [this, Fintype.sum_prod_type, internalMass_eq_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro v _
  split_ifs <;> simp

/-- The original edges of the bucket, with their full weights. -/
def bucketGraph (G : WeightedGraph V) (π : V → V) (T : Finset V) : WeightedGraph V where
  w u v := if π u ∈ T ∧ π v ∈ T ∧ π u ≠ π v then G.w u v else 0
  symm u v := by
    by_cases h : π u ∈ T ∧ π v ∈ T ∧ π u ≠ π v
    · have h' : π v ∈ T ∧ π u ∈ T ∧ π v ≠ π u := ⟨h.2.1, h.1, Ne.symm h.2.2⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true h'),
        G.symm u v]
    · have h' : ¬(π v ∈ T ∧ π u ∈ T ∧ π v ≠ π u) := fun h' => h ⟨h'.2.1, h'.1, Ne.symm h'.2.2⟩
      rw [ite_eq_right_iff.mpr (fun hh => absurd hh h),
        ite_eq_right_iff.mpr (fun hh => absurd hh h')]
  nonneg u v := by split <;> simp [G.nonneg]
  diag v := by simp

theorem bucketWeight_graph (G : WeightedGraph V) (π : V → V) (T : Finset V) :
    finiteSum Finset.univ (fun e => edgeGraph e (bucketWeight G π T e)
      (bucketWeight_nonneg G π T e)) = bucketGraph G π T := by
  ext a b
  change ∑ e, (edgeGraph e _ _).w a b = _
  simp only [edgeGraph, Finset.sum_add_distrib]
  have hone (x y : V) (hxy : x ≠ y) : (∑ e : EdgeIndex V,
      if (x, y) = e.val then bucketWeight G π T e else 0) = bucketWeight G π T ⟨(x, y), hxy⟩ := by
    rw [Finset.sum_eq_single ⟨(x, y), hxy⟩]
    · simp
    · intro e _ he
      split_ifs with h
      · exact (he (Subtype.ext h.symm)).elim
      · rfl
    · simp
  have hzero (x : V) : (∑ e : EdgeIndex V,
      if (x, x) = e.val then bucketWeight G π T e else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    split_ifs with h
    · exact (e.property (by rw [← h])).elim
    · rfl
  by_cases hab : a = b
  · subst hab
    simp [hzero, bucketGraph]
  · rw [hone a b hab, hone b a (Ne.symm hab)]
    simp only [bucketWeight, bucketGraph]
    by_cases h : π a ∈ T ∧ π b ∈ T ∧ π a ≠ π b
    · have h' : π b ∈ T ∧ π a ∈ T ∧ π b ≠ π a := ⟨h.2.1, h.1, Ne.symm h.2.2⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true h'),
        ite_eq_left_of_eq_true _ _ (eq_true h), G.symm b a]
      ring
    · have h' : ¬(π b ∈ T ∧ π a ∈ T ∧ π b ≠ π a) := fun h' => h ⟨h'.2.1, h'.1, Ne.symm h'.2.2⟩
      rw [ite_eq_right_iff.mpr (fun hh => absurd hh h), ite_eq_right_iff.mpr (fun hh => absurd hh h'),
        ite_eq_right_iff.mpr (fun hh => absurd hh h)]
      ring

/-- The counted bucket of one event. -/
def outBucket (G : WeightedGraph V) (π : V → V) (T : Finset V) (r : ℕ) (hr : 0 < r)
    (hM : 0 < (G.contract π).internalMass T) : CountedBucket V where
  weight := bucketWeight G π T
  nonneg := bucketWeight_nonneg G π T
  positive := (sum_bucketWeight G π T).symm ▸ hM
  count := r
  count_pos := hr

namespace CountedBucket

@[simp] theorem outBucket_mass (G : WeightedGraph V) (π : V → V) (T : Finset V) (r : ℕ)
    (hr : 0 < r) (hM : 0 < (G.contract π).internalMass T) :
    (outBucket G π T r hr hM).mass = (G.contract π).internalMass T :=
  sum_bucketWeight G π T

@[simp] theorem outBucket_count (G : WeightedGraph V) (π : V → V) (T : Finset V) (r : ℕ)
    (hr : 0 < r) (hM : 0 < (G.contract π).internalMass T) :
    (outBucket G π T r hr hM).count = r := rfl

theorem outBucket_graph (G : WeightedGraph V) (π : V → V) (T : Finset V) (r : ℕ)
    (hr : 0 < r) (hM : 0 < (G.contract π).internalMass T) :
    (outBucket G π T r hr hM).graph = bucketGraph G π T :=
  bucketWeight_graph G π T

end CountedBucket

/-! ### The law of one output draw -/

/-- The original ordered edge, when its endpoints differ. -/
def origEdge (p : V × V) : Option (EdgeIndex V) :=
  if h : p.1 ≠ p.2 then some ⟨p, h⟩ else none

/-- A sampled original edge with weight `a`. -/
def outDraw (a : ℝ) (ha : 0 ≤ a) (o : Option (V × V)) : WeightedGraph V :=
  match o.bind origEdge with
  | none => 0
  | some e => edgeGraph e a ha

theorem sampleResidual_origLaw (G : WeightedGraph V) (kb kv : ℕ) (π : V → V)
    (cache : V → ℝ) (hc : ∀ b, cache b = G.cut (fiber π b)) (T : Finset V)
    (hB : Fintype.card V ≤ 2 ^ kb) (hV : Fintype.card V ≤ 2 ^ kv)
    (hM : 0 < (G.contract π).internalMass T) :
    ((sampleResidual kb kv π cache T).eval G.cut).map (fun o => o.bind origEdge) =
      (categorical (bucketWeight G π T) (bucketWeight_nonneg G π T)
        ((sum_bucketWeight G π T).symm ▸ hM)).map some := by
  set M := (G.contract π).internalMass T
  set P := (sampleResidual kb kv π cache T).eval G.cut
  have hnone : P none = 0 := sampleResidual_none G kb kv π cache hc T hB hV hM
  have hsome (u v : V) : P (some (u, v)) =
      (if π u ∈ T ∧ π v ∈ T ∧ π u ≠ π v then ENNReal.ofReal (G.w u v) else 0) /
        ENNReal.ofReal (2 * M) := sampleResidual_law G kb kv π cache hc T hB hV hM u v
  have h2M : 0 < 2 * M := by positivity
  ext x
  rw [PMF.map_apply, PMF.map_apply, tsum_fintype, tsum_fintype, Fintype.sum_option]
  simp only [Option.bind_none, hnone, ite_self, Option.bind_some, _root_.zero_add]
  rcases x with _ | ⟨⟨a, b⟩, hab⟩
  · -- Loops have probability zero.
    have hz (p : V × V) : (if none = origEdge p then P (some p) else 0) = 0 := by
      rcases p with ⟨u, v⟩
      rw [ite_eq_right_iff]
      intro h
      have huv : u = v := by
        by_contra hne
        simp [origEdge, hne] at h
      subst huv
      rw [hsome]
      simp
    rw [Finset.sum_eq_zero (fun p _ => by convert hz p)]
    simp
  · simp only [Option.some.injEq, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      categorical_apply, sum_bucketWeight]
    rw [Finset.sum_eq_single (a, b)]
    · have he : (some ⟨(a, b), hab⟩ : Option (EdgeIndex V)) = origEdge (a, b) := by
        simp [origEdge, hab]
      rw [ite_eq_left_of_eq_true _ _ (eq_true he), hsome]
      simp only [bucketWeight]
      split_ifs with h
      · rw [← ENNReal.ofReal_div_of_pos h2M]
        congr 1
        ring
      · simp
    · intro p _ hp
      split_ifs with he
      · exfalso
        apply hp
        rcases p with ⟨u, v⟩
        unfold origEdge at he
        split_ifs at he with huv
        · simp only [Option.some.injEq, Subtype.ext_iff] at he
          exact he.symm
      · rfl
    · simp

/-- One output draw of weight `M/r` has exactly the counted draw law of the bucket. -/
theorem outBucket_drawLaw (G : WeightedGraph V) (kb kv : ℕ) (π : V → V)
    (cache : V → ℝ) (hc : ∀ b, cache b = G.cut (fiber π b)) (T : Finset V)
    (hB : Fintype.card V ≤ 2 ^ kb) (hV : Fintype.card V ≤ 2 ^ kv) (r : ℕ) (hr : 0 < r)
    (hM : 0 < (G.contract π).internalMass T) :
    (outBucket G π T r hr hM).drawLaw =
      ((sampleResidual kb kv π cache T).eval G.cut).map
        (outDraw ((G.contract π).internalMass T / r) (by positivity)) := by
  have hf : outDraw ((G.contract π).internalMass T / r) (by positivity) =
      (fun o : Option (EdgeIndex V) => match o with
        | none => 0
        | some e => edgeGraph e ((G.contract π).internalMass T / r) (by positivity)) ∘
      (fun o => o.bind origEdge) := by
    funext o
    rfl
  rw [hf, ← PMF.map_comp, sampleResidual_origLaw G kb kv π cache hc T hB hV hM, PMF.map_comp]
  unfold CountedBucket.drawLaw
  congr 1
  funext e
  simp only [Function.comp_apply]
  congr 1
  rw [CountedBucket.outBucket_mass, CountedBucket.outBucket_count]

/-! ### Repeated draws -/

/-- `n` repetitions of a draw program, with the graphs added. -/
def sumDraws {I A O : Type} {c : ℕ} (P : RTree I A O c) (f : O → WeightedGraph V) :
    (n : ℕ) → RTree I A (WeightedGraph V) (n * c)
  | 0 => RTree.pure (PMF.pure 0)
  | n + 1 => ((P.bind fun o => (sumDraws P f n).map (fun Y => f o + Y)).cast (by ring))

omit [Fintype V] in
theorem sumDraws_eval {I A O : Type} {c : ℕ} (P : RTree I A O c) (f : O → WeightedGraph V)
    (read : I → A) (n : ℕ) :
    (sumDraws P f n).eval read = independentGraphSum (List.replicate n ((P.eval read).map f)) := by
  induction n with
  | zero => simp [sumDraws, independentGraphSum]
  | succ n ih =>
      rw [sumDraws, RTree.eval_cast, RTree.eval_bind, List.replicate_succ, independentGraphSum,
        PMF.bind_map]
      congr 1
      funext o
      rw [RTree.eval_map, ih]
      rfl

/-- `r` output draws of one event realize the counted sample of its bucket. -/
theorem outDraws_eval (G : WeightedGraph V) (kb kv : ℕ) (π : V → V)
    (cache : V → ℝ) (hc : ∀ b, cache b = G.cut (fiber π b)) (T : Finset V)
    (hB : Fintype.card V ≤ 2 ^ kb) (hV : Fintype.card V ≤ 2 ^ kv) (r : ℕ) (hr : 0 < r)
    (hM : 0 < (G.contract π).internalMass T) :
    (sumDraws (sampleResidual kb kv π cache T)
        (outDraw ((G.contract π).internalMass T / r) (by positivity)) r).eval G.cut =
      CountedBucket.sampleLaw [outBucket G π T r hr hM] := by
  rw [sumDraws_eval, CountedBucket.sampleLaw_singleton, CountedBucket.outBucket_count,
    outBucket_drawLaw G kb kv π cache hc T hB hV r hr hM]

end
end CutQueryComplexity.WeightedGraph
