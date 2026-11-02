import CutQueryComplexity.Hierarchy.GuardTransfer
import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # From an aggregate tree inequality to a retraction distribution (log-five plan, B1–B2)

**B1.** The terminal distance of a hierarchy with edge lengths `ℓ` is the cluster sum
`d_ℓ(u, v) = Σ_x ℓ x · [u, v separated by cluster x]` (`terminalDist`). Exchanging finite sums,
`Σ_x ℓ x · load_f(x) = Σ_y cap y · d_ℓ(f y, f (parent y))` (`sum_mul_load_eq`), where
`load_f(x) = c_{J_f}(cluster x)`.

`TreeZeroExt α` is the remaining mathematical input: for every hierarchy with childless leaves
and nonempty terminal set, and all `cap, ℓ ≥ 0`, some retraction `f` has
`Σ_y cap y · d_ℓ(f y, f (parent y)) ≤ α Σ_y cap y · ℓ y`.

**B2.** For a fixed hierarchy and capacity, play the matrix game with rows the retractions,
columns the tree edges, and payoff `load_f(x) − α cap x` (no division by capacities). For a
column distribution `b`, `TreeZeroExt α` with `ℓ = b` gives a row of nonpositive expected
payoff. The finite minimax theorem (`finite_minimax`, via Sion) gives a row distribution with
`E[load(x)] ≤ α cap x` on every edge, including zero-capacity edges. Hence
`retractionBound_of_treeZeroExt : TreeZeroExt α → RetractionBound α`.
-/

namespace CutQueryComplexity
namespace Hierarchy

open WeightedGraph Finset

/-! ## Finite minimax -/

set_option linter.deprecated false in
/-- **Finite minimax.** If every mixed column strategy has a row of nonpositive expected
payoff, some mixed row strategy has nonpositive expected payoff against every column. -/
theorem finite_minimax {R C : Type} [Fintype R] [Fintype C] [Nonempty R] [Nonempty C]
    (A : R → C → ℝ) (h : ∀ b ∈ stdSimplex ℝ C, ∃ r, ∑ c, b c * A r c ≤ 0) :
    ∃ p ∈ stdSimplex ℝ R, ∀ c, ∑ r, p r * A r c ≤ 0 := by
  classical
  let payoff : (R → ℝ) → (C → ℝ) → ℝ := fun x y => ∑ r, ∑ c, x r * y c * A r c
  let linX : (C → ℝ) → (R → ℝ) →ₗ[ℝ] ℝ := fun y =>
    { toFun := fun x => payoff x y
      map_add' := fun x x' => by
        simp only [payoff, Pi.add_apply, add_mul, sum_add_distrib]
      map_smul' := fun t x => by
        simp only [payoff, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
        exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring }
  let linY : (R → ℝ) → (C → ℝ) →ₗ[ℝ] ℝ := fun x =>
    { toFun := fun y => payoff x y
      map_add' := fun y y' => by
        simp only [payoff, Pi.add_apply, mul_add, add_mul, sum_add_distrib]
      map_smul' := fun t y => by
        simp only [payoff, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
        exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring }
  obtain ⟨a, ha, b, hb, hsad⟩ := Sion.exists_isSaddlePointOn
    (X := stdSimplex ℝ R) (Y := stdSimplex ℝ C) (f := payoff)
    (ne_X := ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary _)⟩)
    (cX := convex_stdSimplex ℝ _) (kX := isCompact_stdSimplex ℝ _)
    (hfy := fun y _ => (linX y).continuous_of_finiteDimensional.continuousOn.lowerSemicontinuousOn)
    (hfy' := fun y _ => ((linX y).convexOn (convex_stdSimplex ℝ _)).quasiconvexOn)
    (cY := convex_stdSimplex ℝ _) (ne_Y := ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary _)⟩)
    (kY := isCompact_stdSimplex ℝ _)
    (hfx := fun x _ => (linY x).continuous_of_finiteDimensional.continuousOn.upperSemicontinuousOn)
    (hfx' := fun x _ => ((linY x).concaveOn (convex_stdSimplex ℝ _)).quasiconcaveOn)
  refine ⟨a, ha, fun c => ?_⟩
  obtain ⟨r, hr⟩ := h b hb
  have hs := hsad _ (single_mem_stdSimplex ℝ r) _ (single_mem_stdSimplex ℝ c)
  have hl : payoff a (Pi.single c 1) = ∑ r', a r' * A r' c := by
    simp only [payoff, Pi.single_apply]
    refine sum_congr rfl fun r' _ => ?_
    rw [sum_eq_single c (fun c' _ hc' => by simp [hc']) (by simp)]
    simp
  have hrr : payoff (Pi.single r 1) b = ∑ c', b c' * A r c' := by
    simp only [payoff, Pi.single_apply]
    rw [sum_eq_single r (fun r' _ hr' => by simp [hr']) (by simp)]
    simp
  rw [hl, hrr] at hs
  exact hs.trans hr

variable {V : Type} [Fintype V] [DecidableEq V]

namespace Hier

variable {N : Type} [Fintype N] [DecidableEq N]

/-! ## B1: terminal distance and the path identity -/

/-- The terminal distance: the total length of the tree edges separating `u` and `v`. -/
noncomputable def terminalDist (H : Hier V N) (ℓ : N → ℝ) (u v : V) : ℝ :=
  ∑ x ∈ H.edges, if (u ∈ H.cluster x) = (v ∈ H.cluster x) then 0 else ℓ x

/-- **The path identity.** -/
theorem sum_mul_load_eq (H : Hier V N) (cap : N → ℝ) (hcap : ∀ x, 0 ≤ cap x) (ℓ : N → ℝ)
    (f : N → V) :
    ∑ x ∈ H.edges, ℓ x * (H.pushGraph cap hcap f).cut (H.cluster x) =
      ∑ y ∈ H.edges, cap y * H.terminalDist ℓ (f y) (f (H.T.parent y)) := by
  simp only [cut_pushGraph, terminalDist, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun y _ => sum_congr rfl fun x _ => ?_
  split_ifs <;> ring

end Hier

/-- **The remaining input**: an aggregate 0-extension bound on trees. -/
def TreeZeroExt (α : ℝ) : Prop :=
  ∀ (V M : Type) [Fintype V] [DecidableEq V] [Nonempty V] [Fintype M] [DecidableEq M]
    (H : Hier V M), H.LeafChildless →
    ∀ (cap ℓ : M → ℝ), (∀ x, 0 ≤ cap x) → (∀ x, 0 ≤ ℓ x) →
      ∃ f : M → V, H.Fixing f ∧
        ∑ y ∈ H.edges, cap y * H.terminalDist ℓ (f y) (f (H.T.parent y)) ≤
          α * ∑ y ∈ H.edges, cap y * ℓ y

namespace Hier

variable {N : Type} [Fintype N] [DecidableEq N]

omit [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N] in
/-- A retraction exists when there are terminals. -/
theorem exists_fixing [Nonempty V] (H : Hier V N) : ∃ f : N → V, H.Fixing f :=
  ⟨Function.invFun H.leaf, fun v => Function.leftInverse_invFun H.leaf_inj v⟩

end Hier

set_option linter.deprecated false in
/-- **B2.** The aggregate tree inequality gives a load-bounded retraction distribution. -/
theorem retractionBound_of_treeZeroExt {α : ℝ} (h : TreeZeroExt α) : RetractionBound α := by
  classical
  intro V M _ _ _ _ _ H hlc cap hcap
  obtain ⟨f0, hf0⟩ := H.exists_fixing
  -- an empty edge set: a point mass
  rcases (H.edges).eq_empty_or_nonempty with he | he
  · refine ⟨{f0}, fun _ => 1, fun _ _ => zero_le_one, fun f hf => ?_, by simp, ?_⟩
    · rw [mem_singleton.mp hf]; exact hf0
    · intro x hx; rw [he] at hx; exact absurd hx (Finset.notMem_empty x)
  -- the matrix game
  let R := {f : M → V // H.Fixing f}
  let C := {x : M // x ∈ H.edges}
  have : Nonempty R := ⟨⟨f0, hf0⟩⟩
  have : Nonempty C := ⟨⟨he.choose, he.choose_spec⟩⟩
  let load : (M → V) → M → ℝ := fun f x => (H.pushGraph cap hcap f).cut (H.cluster x)
  let A : R → C → ℝ := fun f x => load f.1 x.1 - α * cap x.1
  have hbest : ∀ b ∈ stdSimplex ℝ C, ∃ r, ∑ c, b c * A r c ≤ 0 := by
    intro b hb
    let ℓ : M → ℝ := fun x => if hx : x ∈ H.edges then b ⟨x, hx⟩ else 0
    have hℓ0 : ∀ x, 0 ≤ ℓ x := fun x => by
      simp only [ℓ]; split_ifs
      · exact hb.1 _
      · exact le_rfl
    obtain ⟨f, hf, hineq⟩ := h V M H hlc cap ℓ hcap hℓ0
    refine ⟨⟨f, hf⟩, ?_⟩
    have hsum : ∀ g : M → ℝ, ∑ c : C, b c * g c.1 = ∑ x ∈ H.edges, ℓ x * g x := by
      intro g
      rw [← sum_coe_sort H.edges]
      refine sum_congr rfl fun c _ => ?_
      show b c * g c.1 = (if hx : c.1 ∈ H.edges then b ⟨c.1, hx⟩ else 0) * g c.1
      rw [dite_eq_left c.2]
    have e1 : ∑ c : C, b c * A ⟨f, hf⟩ c =
        ∑ c : C, b c * load f c.1 - α * ∑ c : C, b c * cap c.1 := by
      simp only [A, mul_sub, sum_sub_distrib, mul_sum]
      congr 1
      exact sum_congr rfl fun c _ => by ring
    rw [e1, hsum, hsum, Hier.sum_mul_load_eq H cap hcap ℓ f]
    have e2 : ∑ x ∈ H.edges, ℓ x * cap x = ∑ y ∈ H.edges, cap y * ℓ y :=
      sum_congr rfl fun _ _ => mul_comm _ _
    rw [e2]
    linarith
  obtain ⟨p, hp, hpc⟩ := finite_minimax A hbest
  -- transfer the distribution on `R` to a finset of maps
  refine ⟨(univ : Finset R).image Subtype.val, fun g => if hg : H.Fixing g then p ⟨g, hg⟩ else 0,
    fun g _ => by dsimp only; split_ifs; exacts [hp.1 _, le_rfl], fun g hg => ?_, ?_,
    fun x hx => ?_⟩
  · obtain ⟨r, -, rfl⟩ := mem_image.mp hg; exact r.2
  · rw [sum_image fun r _ s _ h => Subtype.ext h]
    calc ∑ r : R, (if hg : H.Fixing r.1 then p ⟨r.1, hg⟩ else 0) = ∑ r : R, p r :=
          sum_congr rfl fun r _ => by rw [dite_eq_left r.2]
      _ = 1 := hp.2
  · rw [sum_image fun r _ s _ h => Subtype.ext h]
    have e : ∑ r : R, (if hg : H.Fixing r.1 then p ⟨r.1, hg⟩ else 0) *
        (H.pushGraph cap hcap r.1).cut (H.cluster x) =
        ∑ r : R, p r * load r.1 x :=
      sum_congr rfl fun r _ => by rw [dite_eq_left r.2]
    rw [e]
    have := hpc ⟨x, hx⟩
    simp only [A, mul_sub, sum_sub_distrib] at this
    have hmass : ∑ r : R, p r * (α * cap x) = α * cap x := by
      rw [← sum_mul, hp.2, one_mul]
    rw [hmass] at this
    linarith

end Hierarchy
end CutQueryComplexity
