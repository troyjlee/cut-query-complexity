import CutQueryComplexity.Sparsification.EstimateComplete
import CutQueryComplexity.Primitive.ResidualSample

/-! # Residual draws as counted draws on the block quotient

One call of the ordered residual sampler returns an original edge `(u,v)` with
probability `w(u,v)/(2M)`, where `M` is the residual mass of the region `T`.
Forgetting everything but the pair of blocks `(π u, π v)` gives exactly one draw of
a counted bucket on the block labels. Its weights are half the quotient weights on
ordered pairs, so its reference graph is the quotient induced on `T`, and its
mass is `M`. The estimation contracts therefore apply to the residual quotient.
-/

namespace CutQueryComplexity.WeightedGraph
noncomputable section
open scoped Classical ENNReal
open Probability
variable {V B : Type} [Fintype V] [DecidableEq V] [Fintype B]

/-- Half the quotient weight on each ordered pair of distinct blocks inside `T`. -/
def residualWeight (G : WeightedGraph V) (π : V → B) (T : Finset B) (e : EdgeIndex B) : ℝ :=
  if e.val.1 ∈ T ∧ e.val.2 ∈ T then (G.contract π).w e.val.1 e.val.2 / 2 else 0

omit [Fintype B] in
theorem residualWeight_nonneg (G : WeightedGraph V) (π : V → B) (T : Finset B)
    (e : EdgeIndex B) : 0 ≤ residualWeight G π T e := by
  unfold residualWeight
  split <;> first | exact le_rfl | exact div_nonneg ((G.contract π).nonneg _ _) (by norm_num)

/-- Sums over named edges are sums over ordered pairs, since loops have zero weight. -/
theorem sum_edgeIndex {f : B × B → ℝ} (hf : ∀ a, f (a, a) = 0) :
    ∑ e : EdgeIndex B, f e.val = ∑ p : B × B, f p := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun p : B × B => p.1 ≠ p.2))
    (by simp) f, Finset.sum_filter]
  apply Finset.sum_congr rfl
  rintro ⟨a, b⟩ _
  by_cases h : a = b
  · subst h; simp [hf]
  · simp [h]

theorem sum_residualWeight_aux (G : WeightedGraph V) (π : V → B) (T : Finset B) :
    ∑ e, residualWeight G π T e = (G.contract π).internalMass T := by
  have := sum_edgeIndex (B := B)
    (f := fun p => if p.1 ∈ T ∧ p.2 ∈ T then (G.contract π).w p.1 p.2 / 2 else 0)
    (fun a => by simp [(G.contract π).diag])
  simp only [residualWeight] at this ⊢
  rw [this, Fintype.sum_prod_type, internalMass, cross]
  simp only [ite_and, Finset.sum_div]
  rw [← Finset.sum_subset (Finset.subset_univ T) (fun x _ hx => by simp [hx])]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← Finset.sum_subset (Finset.subset_univ T) (fun y _ hy => by simp [hy])]
  apply Finset.sum_congr rfl
  intro y hy
  simp [hx, hy]

/-- The residual weights sum to the residual mass, for any enumeration of the names. -/
theorem sum_residualWeight (G : WeightedGraph V) (π : V → B) (T : Finset B)
    [inst : Fintype (EdgeIndex B)] :
    ∑ e, residualWeight G π T e = (G.contract π).internalMass T := by
  obtain rfl : inst = Subtype.fintype _ := Subsingleton.elim _ _
  exact sum_residualWeight_aux G π T

theorem residualWeight_graph (G : WeightedGraph V) (π : V → B) (T : Finset B) :
    finiteSum Finset.univ (fun e => edgeGraph e (residualWeight G π T e)
      (residualWeight_nonneg G π T e)) = (G.contract π).induce T := by
  ext a b
  change ∑ e, (edgeGraph e _ _).w a b = _
  simp only [edgeGraph, Finset.sum_add_distrib]
  have hone (x y : B) (hxy : x ≠ y) : (∑ e : EdgeIndex B,
      if (x, y) = e.val then residualWeight G π T e else 0) =
        residualWeight G π T ⟨(x, y), hxy⟩ := by
    rw [Finset.sum_eq_single ⟨(x, y), hxy⟩]
    · simp
    · intro e _ he
      split_ifs with h
      · exact (he (Subtype.ext h.symm)).elim
      · rfl
    · simp
  have hzero (x : B) : (∑ e : EdgeIndex B,
      if (x, x) = e.val then residualWeight G π T e else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    split_ifs with h
    · exact (e.property (by rw [← h])).elim
    · rfl
  by_cases hab : a = b
  · subst hab
    simp [hzero, induce, (G.contract π).diag]
  · rw [hone a b hab, hone b a (Ne.symm hab)]
    simp only [residualWeight, induce]
    rw [(G.contract π).symm b a]
    by_cases h : a ∈ T ∧ b ∈ T
    · simp only [h, and_self, ↓reduceIte]
      ring
    · have h' : ¬(b ∈ T ∧ a ∈ T) := fun h' => h ⟨h'.2, h'.1⟩
      simp only [h, h', ↓reduceIte]
      ring

/-- The counted bucket of one estimation call on the residual quotient of `T`. -/
def residualBucket (G : WeightedGraph V) (π : V → B) (T : Finset B) (r : ℕ) (hr : 0 < r)
    (hM : 0 < (G.contract π).internalMass T) : CountedBucket B where
  weight := residualWeight G π T
  nonneg := residualWeight_nonneg G π T
  positive := (sum_residualWeight G π T).symm ▸ hM
  count := r
  count_pos := hr

namespace CountedBucket

@[simp] theorem residualBucket_mass (G : WeightedGraph V) (π : V → B) (T : Finset B) (r : ℕ)
    (hr : 0 < r) (hM : 0 < (G.contract π).internalMass T) :
    (residualBucket G π T r hr hM).mass = (G.contract π).internalMass T :=
  sum_residualWeight G π T

@[simp] theorem residualBucket_count (G : WeightedGraph V) (π : V → B) (T : Finset B) (r : ℕ)
    (hr : 0 < r) (hM : 0 < (G.contract π).internalMass T) :
    (residualBucket G π T r hr hM).count = r := rfl

theorem residualBucket_graph (G : WeightedGraph V) (π : V → B) (T : Finset B) (r : ℕ)
    (hr : 0 < r) (hM : 0 < (G.contract π).internalMass T) :
    (residualBucket G π T r hr hM).graph = (G.contract π).induce T :=
  residualWeight_graph G π T

/-- The reference graph of `r` residual draws is the quotient induced on the region. -/
theorem residualBucket_reference (G : WeightedGraph V) (π : V → B) (T : Finset B) (r : ℕ)
    (hr : 0 < r) (hM : 0 < (G.contract π).internalMass T) :
    reference [residualBucket G π T r hr hM] = (G.contract π).induce T := by
  simp [reference, sumGraphs, residualBucket_graph]

end CountedBucket

/-- The pair of blocks of an original ordered edge, when they differ. -/
def blockEdge (π : V → B) (p : V × V) : Option (EdgeIndex B) :=
  if h : π p.1 ≠ π p.2 then some ⟨(π p.1, π p.2), h⟩ else none

/-- A sampled original edge becomes one block-level draw of weight `a`. -/
def blockDraw (π : V → B) (a : ℝ) (ha : 0 ≤ a) (o : Option (V × V)) : WeightedGraph B :=
  match o.bind (blockEdge π) with
  | none => 0
  | some e => edgeGraph e a ha

/-- Forgetting original endpoints turns the ordered residual sampler into the
categorical law of the residual bucket. -/
theorem sampleResidual_blockLaw (G : WeightedGraph V) (kb kv : ℕ) (π : V → B)
    (cache : B → ℝ) (hc : ∀ b, cache b = G.cut (fiber π b)) (T : Finset B)
    (hB : Fintype.card B ≤ 2 ^ kb) (hV : Fintype.card V ≤ 2 ^ kv)
    (hM : 0 < (G.contract π).internalMass T) :
    ((sampleResidual kb kv π cache T).eval G.cut).map (fun o => o.bind (blockEdge π)) =
      (categorical (residualWeight G π T) (residualWeight_nonneg G π T)
        ((sum_residualWeight G π T).symm ▸ hM)).map some := by
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
  · -- No positive mass lands on a loop.
    have hz (p : V × V) : (if none = blockEdge π p then P (some p) else 0) = 0 := by
      rcases p with ⟨u, v⟩
      rw [ite_eq_right_iff]
      intro h
      have hπ : π u = π v := by
        by_contra hne
        simp [blockEdge, hne] at h
      rw [hsome, hπ]
      simp
    rw [Finset.sum_eq_zero (fun p _ => by convert hz p)]
    simp
  · simp only [Option.some.injEq, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      categorical_apply, sum_residualWeight]
    -- Only original edges from block `a` to block `b` contribute.
    have hterm (p : V × V) : (if some ⟨(a, b), hab⟩ = blockEdge π p then P (some p) else 0) =
        if π p.1 = a ∧ π p.2 = b then
          (if a ∈ T ∧ b ∈ T then ENNReal.ofReal (G.w p.1 p.2) else 0) /
            ENNReal.ofReal (2 * M) else 0 := by
      rcases p with ⟨u, v⟩
      by_cases h : π u = a ∧ π v = b
      · obtain ⟨rfl, rfl⟩ := h
        simp [blockEdge, hab, hsome]
      · rw [ite_eq_right_iff.mpr (fun he => absurd he ?_), ite_eq_right_iff.mpr (fun he => absurd he h)]
        intro he
        apply h
        unfold blockEdge at he
        split_ifs at he with hne
        · simp only [Option.some.injEq, Subtype.ext_iff, Prod.ext_iff] at he
          exact ⟨he.1.symm, he.2.symm⟩
    rw [Finset.sum_congr rfl (fun p _ => by convert hterm p)]
    by_cases hT : a ∈ T ∧ b ∈ T
    · simp only [hT, and_self, ↓reduceIte, residualWeight]
      rw [← Finset.sum_filter]
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun p _ => G.nonneg _ _),
        ← ENNReal.ofReal_inv_of_pos h2M, ← ENNReal.ofReal_mul (Finset.sum_nonneg
          (fun p _ => G.nonneg _ _))]
      congr 1
      have hcross : ∑ p ∈ Finset.univ.filter (fun p : V × V => π p.1 = a ∧ π p.2 = b),
          G.w p.1 p.2 = G.cross (fiber π a) (fiber π b) := by
        rw [cross, ← Finset.sum_product']
        apply Finset.sum_congr
        · ext p; simp [mem_fiber]
        · intros; rfl
      rw [hcross]
      have hw : (G.contract π).w a b = G.cross (fiber π a) (fiber π b) := by
        simp [contract, hab]
      rw [hw]
      field_simp
      rfl
    · simp only [hT, ↓reduceIte, ENNReal.zero_div, ite_self, Finset.sum_const_zero, residualWeight,
        zero_div, ENNReal.ofReal_zero]

namespace CountedBucket

/-- One block-level residual draw has exactly the counted draw law of the bucket. -/
theorem residualBucket_drawLaw (G : WeightedGraph V) (kb kv : ℕ) (π : V → B)
    (cache : B → ℝ) (hc : ∀ b, cache b = G.cut (fiber π b)) (T : Finset B)
    (hB : Fintype.card B ≤ 2 ^ kb) (hV : Fintype.card V ≤ 2 ^ kv) (r : ℕ) (hr : 0 < r)
    (hM : 0 < (G.contract π).internalMass T) :
    (residualBucket G π T r hr hM).drawLaw =
      ((sampleResidual kb kv π cache T).eval G.cut).map
        (blockDraw π ((G.contract π).internalMass T / r) (by positivity)) := by
  have hf : blockDraw π ((G.contract π).internalMass T / r) (by positivity) =
      (fun o : Option (EdgeIndex B) => match o with
        | none => 0
        | some e => edgeGraph e ((G.contract π).internalMass T / r) (by positivity)) ∘
      (fun o => o.bind (blockEdge π)) := by
    funext o
    rfl
  rw [hf, ← PMF.map_comp, sampleResidual_blockLaw G kb kv π cache hc T hB hV hM, PMF.map_comp]
  unfold drawLaw
  congr 1
  funext e
  simp only [Function.comp_apply]
  congr 1
  rw [residualBucket_mass, residualBucket_count]

end CountedBucket
end
end CutQueryComplexity.WeightedGraph
