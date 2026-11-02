import CutQueryComplexity.AllPairsAudit.Star
import CutQueryComplexity.Primitive.Residual
import CutQueryComplexity.Problem.Basic

/-!
# Public shaving and preservation of small friendly cuts

Only the global cut approximation of the explicit graph is used. No statement
that induced subgraphs approximate one another enters this argument.
The threshold constants specialize the repaired proof to friendliness 1/6.
-/

set_option autoImplicit false

namespace CutQueryComplexity.AllPairs

open Finset WeightedGraph AllPairsAudit
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem incident_le_card {G : WeightedGraph V} (hG : Unweighted G) (v : V) (S : Finset V) :
    incident G v S ≤ S.card := by
  calc
    incident G v S ≤ ∑ _u ∈ S, (1 : ℝ) :=
      sum_le_sum fun u _ => unweighted_edge_le_one hG v u
    _ = _ := by simp

theorem incident_inter_bound (G : WeightedGraph V) (v : V) (S W : Finset V) :
    incident G v S ≤ incident G v (S ∩ W) + incident G v Wᶜ := by
  have hsub : S ⊆ (S ∩ W) ∪ Wᶜ := by
    intro u hu
    by_cases hw : u ∈ W
    · exact mem_union_left _ (mem_inter.mpr ⟨hu, hw⟩)
    · exact mem_union_right _ (mem_compl.mpr hw)
  have hd : Disjoint (S ∩ W) Wᶜ :=
    disjoint_left.mpr fun u hu hc => (mem_compl.mp hc) (mem_inter.mp hu).2
  have hm := incident_mono G v hsub
  simpa only [incident, sum_union hd] using hm

/-- Each retained vertex has many original neighbors on its own friendly
shore, inside the original cluster. Simplicity turns this into cardinality. -/
theorem retained_side_card {G : WeightedGraph V} (hG : Unweighted G)
    {τ : ℝ} (_hτ : 0 ≤ τ) {W S : Finset V} {v : V}
    (hf : Friendly G S) (hv : v ∈ S)
    (hdegree : 60 * τ ≤ G.degree v)
    (hboundary : 24 * incident G v Wᶜ ≤ G.degree v) :
    6 * τ ≤ ((W ∩ S).card : ℝ) := by
  have hfriend := hf v
  simp only [crossing, hv, ↓reduceIte] at hfriend
  have htotal := incident_add_compl G v S
  have hsplit := incident_inter_bound G v S W
  have hcard := incident_le_card hG v (S ∩ W)
  rw [inter_comm W S]
  linarith

/-- An expanding explicit cluster cannot have retained vertices on both sides
of a small friendly cut. The approximation premise concerns global cuts only. -/
theorem retained_no_split {G K : WeightedGraph V} (hG : Unweighted G)
    (hK : IsCutSparsifier (1 / 2) G K) {τ w : ℝ} (hτ : 0 < τ) (hw : w ≤ τ ^ 2)
    {W S : Finset V}
    (hexpand : ∀ A : Finset V, A ⊆ W →
      τ * min (A.card : ℝ) ((W \ A).card : ℝ) ≤ K.cross A (W \ A))
    (hf : Friendly G S) (hcut : G.cut S ≤ w) {x y : V}
    (hxW : x ∈ W) (hyW : y ∈ W) (hxS : x ∈ S) (hyS : y ∉ S)
    (hxd : 60 * τ ≤ G.degree x) (hyd : 60 * τ ≤ G.degree y)
    (hxb : 24 * incident G x Wᶜ ≤ G.degree x)
    (hyb : 24 * incident G y Wᶜ ≤ G.degree y) : False := by
  have hl := retained_side_card hG hτ.le hf hxS hxd hxb
  have hr := retained_side_card hG hτ.le ((friendly_compl G S).mpr hf)
    (mem_compl.mpr hyS) hyd hyb
  have hright : W \ (W ∩ S) = W ∩ Sᶜ := by ext; simp
  have hmin : 6 * τ ≤ min ((W ∩ S).card : ℝ) ((W \ (W ∩ S)).card : ℝ) := by
    rw [hright]
    exact le_min hl hr
  have he := hexpand (W ∩ S) inter_subset_left
  have hcross : K.cross (W ∩ S) (W \ (W ∩ S)) ≤ K.cut S := by
    apply K.cross_mono inter_subset_right
    intro v hv
    have h := mem_sdiff.mp hv
    apply mem_compl.mpr
    intro hs
    exact h.2 (mem_inter.mpr ⟨h.1, hs⟩)
  have hlow := mul_le_mul_of_nonneg_left hmin hτ.le
  have hupper := (hK.2 S).2
  have hpos : 0 < τ ^ 2 := sq_pos_of_pos hτ
  nlinarith

/-- The decision uses only public degree and boundary-degree tables. -/
def Keep (d boundary : V → ℝ) (τ : ℝ) (v : V) : Prop :=
  60 * τ ≤ d v ∧ 24 * boundary v ≤ d v

def keptFiber (p : V → V) (d boundary : V → ℝ) (τ : ℝ) (b : V) : Finset V :=
  (fiber p b).filter (Keep d boundary τ)

def shaveRepresentative (p : V → V) (d boundary : V → ℝ) (τ : ℝ) (b : V) : V :=
  if h : (keptFiber p d boundary τ b).Nonempty then Classical.choose h else b

def shaveMap (p : V → V) (d boundary : V → ℝ) (τ : ℝ) (v : V) : V :=
  if Keep d boundary τ v then shaveRepresentative p d boundary τ (p v) else v

theorem shaveRepresentative_spec (p : V → V) (d boundary : V → ℝ) (τ : ℝ)
    {v : V} (hv : Keep d boundary τ v) :
    p (shaveRepresentative p d boundary τ (p v)) = p v ∧
      Keep d boundary τ (shaveRepresentative p d boundary τ (p v)) := by
  have hm : v ∈ keptFiber p d boundary τ (p v) := by
    simp [keptFiber, WeightedGraph.fiber, hv]
  have hn : (keptFiber p d boundary τ (p v)).Nonempty := ⟨v, hm⟩
  have hc := Classical.choose_spec hn
  rw [shaveRepresentative, dite_eq_left hn]
  simpa only [keptFiber, mem_filter, mem_fiber] using hc

/-- Distinct merged vertices are both retained in the same original block.
Shaved singleton labels cannot collide with a retained representative. -/
theorem shaveMap_eq_cases (p : V → V) (d boundary : V → ℝ) (τ : ℝ) {u v : V}
    (hne : u ≠ v) (he : shaveMap p d boundary τ u = shaveMap p d boundary τ v) :
    Keep d boundary τ u ∧ Keep d boundary τ v ∧ p u = p v := by
  by_cases hu : Keep d boundary τ u
  · have hru := shaveRepresentative_spec p d boundary τ hu
    by_cases hv : Keep d boundary τ v
    · have hrv := shaveRepresentative_spec p d boundary τ hv
      simp only [shaveMap, hu, hv, ↓reduceIte] at he
      exact ⟨hu, hv, hru.1.symm.trans ((congrArg p he).trans hrv.1)⟩
    · simp only [shaveMap, hu, hv, ↓reduceIte] at he
      exact False.elim (hv (he ▸ hru.2))
  · by_cases hv : Keep d boundary τ v
    · have hrv := shaveRepresentative_spec p d boundary τ hv
      simp only [shaveMap, hu, hv, ↓reduceIte] at he
      exact False.elim (hu (he.symm ▸ hrv.2))
    · simp only [shaveMap, hu, hv, ↓reduceIte] at he
      exact False.elim (hne he)

theorem shaveMap_same_kept_block (p : V → V) (d boundary : V → ℝ) (τ : ℝ)
    {u v : V} (hu : Keep d boundary τ u) (hv : Keep d boundary τ v) (hp : p u = p v) :
    shaveMap p d boundary τ u = shaveMap p d boundary τ v := by
  simp [shaveMap, hu, hv, hp]

theorem shaveMap_idempotent (p : V → V) (d boundary : V → ℝ) (τ : ℝ) (v : V) :
    shaveMap p d boundary τ (shaveMap p d boundary τ v) = shaveMap p d boundary τ v := by
  by_cases hv : Keep d boundary τ v
  · have hr := shaveRepresentative_spec p d boundary τ hv
    simp only [shaveMap, hv, hr.2, hr.1, ↓reduceIte]
  · simp [shaveMap, hv]

/-- Correctly measured shaving preserves every friendly cut up to the chosen
scale, simultaneously. Its only graph approximation is the global one. -/
theorem shaveMap_respects {G K : WeightedGraph V} (hG : Unweighted G)
    (hK : IsCutSparsifier (1 / 2) G K) (p : V → V) (d boundary : V → ℝ)
    (hd : ∀ v, d v = G.degree v)
    (hb : ∀ v, boundary v = incident G v (fiber p (p v))ᶜ)
    {τ w : ℝ} (hτ : 0 < τ) (hw : w ≤ τ ^ 2)
    (hexpand : ∀ b A, A ⊆ fiber p b →
      τ * min (A.card : ℝ) (((fiber p b) \ A).card : ℝ) ≤ K.cross A ((fiber p b) \ A))
    {S : Finset V} (hf : Friendly G S) (hcut : G.cut S ≤ w) :
    Respects (shaveMap p d boundary τ) S := by
  intro u v he
  by_cases huv : u = v
  · subst v; rfl
  obtain ⟨hu, hv, hp⟩ := shaveMap_eq_cases p d boundary τ huv he
  simp only [Keep, hd, hb] at hu hv
  have hsplit (x y : V) (hx : x ∈ S) (hy : y ∉ S)
      (hxW : x ∈ fiber p (p u)) (hyW : y ∈ fiber p (p u))
      (hxd : 60 * τ ≤ G.degree x) (hyd : 60 * τ ≤ G.degree y)
      (hxb : 24 * incident G x (fiber p (p u))ᶜ ≤ G.degree x)
      (hyb : 24 * incident G y (fiber p (p u))ᶜ ≤ G.degree y) : False :=
    retained_no_split hG hK hτ hw (hexpand (p u)) hf hcut hxW hyW hx hy hxd hyd hxb hyb
  have huW : u ∈ fiber p (p u) := by simp [fiber]
  have hvW : v ∈ fiber p (p u) := by simp [fiber, hp]
  have hvb : 24 * incident G v (fiber p (p u))ᶜ ≤ G.degree v := by simpa [hp] using hv.2
  constructor
  · intro hus
    by_contra hvs
    exact hsplit u v hus hvs huW hvW hu.1 hv.1 hu.2 hvb
  · intro hvs
    by_contra hus
    exact hsplit v u hvs hus hvW huW hv.1 hu.1 hvb hu.2

/-- Three public families of original cuts provide all shaving statistics. -/
def shaveStats (p : V → V) :
    DTree (Finset V) ℝ ((V → ℝ) × (V → ℝ)) (3 * Fintype.card V) :=
  ((DTree.queryAll (fun v : V => ({v} : Finset V)) (fun _ => (0 : ℝ))).bind fun degree =>
    (cacheBlockCuts p).bind fun blockCut =>
      (DTree.queryAll (fun v => (fiber p (p v)).erase v) (fun _ => (0 : ℝ))).map
        (fun deleted => (degree, fun v => (degree v + blockCut (p v) - deleted v) / 2))).cast
        (by omega)

theorem shaveStats_eval (G : WeightedGraph V) (p : V → V) :
    (shaveStats p).eval G.cut =
      (G.degree, fun v => incident G v (fiber p (p v))ᶜ) := by
  have hdeg : (DTree.queryAll (fun v : V => ({v} : Finset V)) (fun _ => (0 : ℝ))).eval G.cut =
      G.degree := by simp [DTree.eval, DTree.queryAll_run]
  have hblock : (cacheBlockCuts p).eval G.cut = fun b => G.cut (fiber p b) := by
    rw [DTree.eval, cacheBlockCuts_run]
  have hdeleted : (DTree.queryAll (fun v => (fiber p (p v)).erase v) (fun _ => (0 : ℝ))).eval
      G.cut = fun v => G.cut ((fiber p (p v)).erase v) := by
    rw [DTree.eval, DTree.queryAll_run]
  simp only [shaveStats, DTree.eval_cast, DTree.eval_bind, hdeg, hblock, DTree.eval_map, hdeleted]
  apply congrArg (fun b : V → ℝ => (G.degree, b))
  funext v
  have hv : v ∈ fiber p (p v) := by simp [fiber]
  have he := cut_erase G hv
  simp only [crossing, hv, ↓reduceIte] at he
  linarith

/-- The block map itself is selected from public tables and cut answers. -/
def shaveProgram (p : V → V) (τ : ℝ) :
    DTree (Finset V) ℝ (V → V) (3 * Fintype.card V) :=
  (shaveStats p).map fun data => shaveMap p data.1 data.2 τ

theorem shaveProgram_eval (G : WeightedGraph V) (p : V → V) (τ : ℝ) :
    (shaveProgram p τ).eval G.cut =
      shaveMap p G.degree (fun v => incident G v (fiber p (p v))ᶜ) τ := by
  simp [shaveProgram, shaveStats_eval]

theorem shaveProgram_cost (p : V → V) (τ : ℝ) (oracle : Finset V → ℝ) :
    (shaveProgram p τ).cost oracle ≤ 3 * Fintype.card V := DTree.cost_le _ _

theorem shaveProgram_respects {G K : WeightedGraph V} (hG : Unweighted G)
    (hK : IsCutSparsifier (1 / 2) G K) (p : V → V)
    {τ w : ℝ} (hτ : 0 < τ) (hw : w ≤ τ ^ 2)
    (hexpand : ∀ b A, A ⊆ fiber p b →
      τ * min (A.card : ℝ) (((fiber p b) \ A).card : ℝ) ≤ K.cross A ((fiber p b) \ A))
    {S : Finset V} (hf : Friendly G S) (hcut : G.cut S ≤ w) :
    Respects ((shaveProgram p τ).eval G.cut) S := by
  rw [shaveProgram_eval]
  exact shaveMap_respects hG hK p _ _ (fun _ => rfl) (fun _ => rfl)
    hτ hw hexpand hf hcut

/-- Ordered residual mass equals the sum of all original block cuts. -/
theorem residual_sum_eq_boundary (G : WeightedGraph V) (p : V → V) :
    (∑ u, ∑ v, (G.residual p).w u v) = ∑ b, G.cut (fiber p b) := by
  have hm := G.residual_internalMass p (univ : Finset V)
  have hf := G.residual_mass_formula p (univ : Finset V)
  have hp : WeightedGraph.pull p (univ : Finset V) = univ := by
    ext; simp [WeightedGraph.pull]
  rw [hp] at hm hf
  rw [G.cut_univ, sub_zero, ← hm] at hf
  change (∑ u, ∑ v, (G.residual p).w u v) / 2 = _ at hf
  linarith

theorem boundary_degree_sum (G : WeightedGraph V) (p : V → V) :
    (∑ v, incident G v (fiber p (p v))ᶜ) = ∑ b, G.cut (fiber p b) := by
  rw [← residual_sum_eq_boundary]
  apply sum_congr rfl
  intro v _
  have he : (fiber p (p v))ᶜ = univ.filter (fun u => p u ≠ p v) := by
    ext u; simp [fiber]
  rw [incident, he, sum_filter]
  apply sum_congr rfl
  intro u _
  by_cases hp : p v = p u <;> simp [residual, hp, eq_comm]

/-- Only edges touching a shaved vertex can be added to the old residual. -/
theorem shaved_residual_pointwise (G : WeightedGraph V) (p : V → V)
    (d boundary : V → ℝ) (τ : ℝ) (u v : V) :
    (G.residual (shaveMap p d boundary τ)).w u v ≤
      (G.residual p).w u v +
        (if Keep d boundary τ u then 0 else G.w u v) +
        (if Keep d boundary τ v then 0 else G.w u v) := by
  have hsub := G.residual_subgraph (shaveMap p d boundary τ) u v
  have hn := G.nonneg u v
  by_cases hp : p u = p v
  · by_cases hu : Keep d boundary τ u
    · by_cases hv : Keep d boundary τ v
      · have he := shaveMap_same_kept_block p d boundary τ hu hv hp
        simp [residual, hp, he, hu, hv]
      · simpa [residual, hp, hu, hv] using hsub
    · by_cases hv : Keep d boundary τ v
      · simpa [residual, hp, hu, hv] using hsub
      · simp only [residual, hp, hu, hv, ↓reduceIte, zero_add]
        exact hsub.trans (by linarith)
  · have ha : 0 ≤ if Keep d boundary τ u then 0 else G.w u v := by
      split <;> positivity
    have hb : 0 ≤ if Keep d boundary τ v then 0 else G.w u v := by
      split <;> positivity
    simpa only [residual, hp, ↓reduceIte] using
      hsub.trans (show G.w u v ≤ G.w u v +
        (if Keep d boundary τ u then 0 else G.w u v) +
        (if Keep d boundary τ v then 0 else G.w u v) by linarith)

/-- Surviving ordered edge mass is charged to old boundary mass and twice the
degrees of shaved vertices. This holds for arbitrary nonnegative weights. -/
theorem shaved_boundary_charge (G : WeightedGraph V) (p : V → V)
    (d boundary : V → ℝ) (τ : ℝ) :
    (∑ b, G.cut (fiber (shaveMap p d boundary τ) b)) ≤
      (∑ b, G.cut (fiber p b)) +
        2 * ∑ v, if Keep d boundary τ v then 0 else G.degree v := by
  have h := sum_le_sum (s := (univ : Finset V)) fun u _ =>
    sum_le_sum (s := (univ : Finset V)) fun v _ =>
      shaved_residual_pointwise G p d boundary τ u v
  have hf : (∑ u, ∑ v, if Keep d boundary τ u then 0 else G.w u v) =
      ∑ u, if Keep d boundary τ u then 0 else G.degree u := by
    simp only [sum_ite_irrel, sum_const_zero, degree]
  have hs : (∑ u, ∑ v, if Keep d boundary τ v then 0 else G.w u v) =
      ∑ u, if Keep d boundary τ u then 0 else G.degree u := by
    rw [sum_comm]
    simp_rw [G.symm]
    exact hf
  simp only [sum_add_distrib] at h
  rw [residual_sum_eq_boundary, residual_sum_eq_boundary, hf, hs] at h
  linarith

/-- The explicit constants of the repaired shaving argument. A failure of
either retention test pays the vertex degree from its threshold or boundary. -/
theorem shaveProgram_boundary_le (G : WeightedGraph V) (p : V → V)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    (∑ b, G.cut (fiber ((shaveProgram p τ).eval G.cut) b)) ≤
      49 * (∑ b, G.cut (fiber p b)) + 120 * Fintype.card V * τ := by
  rw [shaveProgram_eval]
  have hc := shaved_boundary_charge G p G.degree
    (fun v => incident G v (fiber p (p v))ᶜ) τ
  have hb : (∑ v, if Keep G.degree (fun v => incident G v (fiber p (p v))ᶜ) τ v
      then 0 else G.degree v) ≤
      60 * Fintype.card V * τ + 24 * (∑ b, G.cut (fiber p b)) := by
    calc
      _ ≤ ∑ v, (60 * τ + 24 * incident G v (fiber p (p v))ᶜ) := by
        apply sum_le_sum
        intro v _
        have hn : 0 ≤ incident G v (fiber p (p v))ᶜ :=
          sum_nonneg fun u _ => G.nonneg v u
        split_ifs with hk
        · positivity
        · simp only [Keep, not_and_or, not_le] at hk
          rcases hk with hl | hr <;> linarith
      _ = _ := by
        rw [sum_add_distrib]
        simp_rw [← mul_sum]
        rw [boundary_degree_sum]
        simp only [sum_const, card_univ, nsmul_eq_mul]
        ring
  linarith

/-- Global approximation transfers the explicit decomposition's boundary cap
to the original graph before the shaving charge. -/
theorem shaveProgram_sparse_bound {G K : WeightedGraph V}
    (hK : IsCutSparsifier (1 / 2) G K) (p : V → V) {τ : ℝ} (hτ : 0 ≤ τ)
    (hpartition : (∑ b, K.cut (fiber p b)) ≤
      2 * τ * Fintype.card V * Nat.clog 2 (Fintype.card V)) :
    (∑ b, G.cut (fiber ((shaveProgram p τ).eval G.cut) b)) ≤
      196 * τ * Fintype.card V * Nat.clog 2 (Fintype.card V) +
        120 * Fintype.card V * τ := by
  have hb : (∑ b, G.cut (fiber p b)) ≤
      4 * τ * Fintype.card V * Nat.clog 2 (Fintype.card V) := by
    have hsum := sum_le_sum (s := (univ : Finset V)) fun b _ => (hK.2 (fiber p b)).1
    simp only [← mul_sum] at hsum
    linarith
  have hs := shaveProgram_boundary_le G p hτ
  linarith

end
end CutQueryComplexity.AllPairs

#print axioms CutQueryComplexity.AllPairs.shaveProgram_respects
#print axioms CutQueryComplexity.AllPairs.shaveProgram_cost
#print axioms CutQueryComplexity.AllPairs.shaveProgram_sparse_bound
