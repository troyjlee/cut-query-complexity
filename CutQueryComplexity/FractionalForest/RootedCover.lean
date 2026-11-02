import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Rooted forests and the rooted-cover inequality (W2)

Source: Lemma 17 and Corollary 18 of paper P3
(`papers/P3/directed-cut-certificates.pdf`).

A rooted forest on a vertex type `V` is a parent map `V → Option V`
(`none` = root) in which every ancestor chain terminates.  Every component is
oriented toward its root: the arc of a nonroot vertex `v` is `v → parent v`.
An arc `v → w` enters `T` when `v ∉ T` and `w ∈ T`.
-/

namespace CutQueryComplexity
namespace FractionalForest

open Finset

/-- A rooted forest given by a parent map; `none` marks a root. The no-cycle
condition says that iterating the parent map from any vertex reaches `none`. -/
structure RootedForest (V : Type*) where
  parent : V → Option V
  acyclic : ∀ v : V, ∃ n : ℕ, (fun o : Option V => o.bind parent)^[n] (some v) = none

namespace RootedForest

variable {V : Type*} (F : RootedForest V)

/-- One step up the ancestor chain. -/
def up : Option V → Option V := fun o => o.bind F.parent

/-- Number of vertices on the ancestor chain of `v` (including `v`):
the least `n` with `up^[n] (some v) = none`. -/
noncomputable def height (v : V) : ℕ := by
  classical exact Nat.find (F.acyclic v)

theorem height_spec (v : V) : F.up^[F.height v] (some v) = none := by
  classical
  unfold height
  exact Nat.find_spec (F.acyclic v)

theorem height_min (v : V) {n : ℕ} (h : F.up^[n] (some v) = none) :
    F.height v ≤ n := by
  classical
  unfold height
  exact Nat.find_min' (F.acyclic v) h

theorem height_pos (v : V) : 0 < F.height v := by
  rcases Nat.eq_zero_or_pos (F.height v) with h | h
  · have := F.height_spec v
    rw [h] at this
    simp at this
  · exact h

/-- The defining depth relation: a child is one deeper than its parent. -/
theorem height_of_parent {v w : V} (h : F.parent v = some w) :
    F.height v = F.height w + 1 := by
  have key : ∀ n, F.up^[n + 1] (some v) = F.up^[n] (some w) := by
    intro n
    rw [Function.iterate_succ_apply]
    simp [up, h]
  apply le_antisymm
  · apply F.height_min
    rw [key]
    exact F.height_spec w
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (F.height_pos v).ne'
    have hv := F.height_spec v
    rw [hk, key] at hv
    have := F.height_min w hv
    omega

theorem height_lt_of_parent {v w : V} (h : F.parent v = some w) :
    F.height w < F.height v := by
  rw [F.height_of_parent h]; omega

/-- Well-founded induction from parents to children. -/
theorem induction {P : V → Prop}
    (hroot : ∀ v, F.parent v = none → P v)
    (hstep : ∀ v w, F.parent v = some w → P w → P v) : ∀ v, P v := by
  intro v
  induction h : F.height v using Nat.strong_induction_on generalizing v with
  | _ n ih =>
    cases hp : F.parent v with
    | none => exact hroot v hp
    | some w =>
      exact hstep v w hp (ih _ (h ▸ F.height_lt_of_parent hp) w rfl)

/-- Roots of the forest. -/
def IsRoot (v : V) : Prop := F.parent v = none

instance [DecidableEq V] (v : V) : Decidable (F.IsRoot v) :=
  inferInstanceAs (Decidable (F.parent v = none))

/-- The arc `v → parent v` enters `T`. -/
def Enters (T : Finset V) (v : V) : Prop :=
  v ∉ T ∧ ∃ w, F.parent v = some w ∧ w ∈ T

instance [DecidableEq V] (T : Finset V) (v : V) : Decidable (F.Enters T v) := by
  unfold Enters
  cases F.parent v with
  | none => exact isFalse (by simp)
  | some w => exact decidable_of_iff (v ∉ T ∧ w ∈ T) (by simp)

variable [Fintype V] [DecidableEq V] in
/-- `|T ∩ R_F|`. -/
def rootCount (T : Finset V) : ℕ := (T.filter F.IsRoot).card

variable [Fintype V] [DecidableEq V] in
/-- `|δ⁻_F(T)|`: forest arcs `v → parent v` with `v ∉ T`, `parent v ∈ T`.
Arcs are indexed by their tail `v`. -/
def inArcs (T : Finset V) : ℕ := (univ.filter (F.Enters T)).card

/-! ## The coloring -/

section Coloring

variable {ι : Type*} (T : ι → Finset V) (hcov : ∀ v, ∃ i, v ∈ T i)

/-- Choose a covering label for every vertex, processing parents before
children: a nonroot vertex keeps its parent's color whenever it may. -/
noncomputable def color (v : V) : ι :=
  match _h : F.parent v with
  | none => Classical.choose (hcov v)
  | some w =>
      haveI := Classical.propDecidable
      if v ∈ T (color w) then color w else Classical.choose (hcov v)
termination_by F.height v
decreasing_by exact F.height_lt_of_parent _h

theorem color_root {v : V} (h : F.parent v = none) :
    F.color T hcov v = Classical.choose (hcov v) := by
  rw [color]; split <;> simp_all

theorem color_child {v w : V} (h : F.parent v = some w) :
    F.color T hcov v =
      (haveI := Classical.propDecidable
       if v ∈ T (F.color T hcov w) then F.color T hcov w
       else Classical.choose (hcov v)) := by
  rw [color]
  split
  · simp_all
  · rename_i w' h'
    rw [h] at h'
    cases h'
    rfl

theorem color_mem (v : V) : v ∈ T (F.color T hcov v) := by
  cases h : F.parent v with
  | none => rw [F.color_root T hcov h]; exact Classical.choose_spec (hcov v)
  | some w =>
    rw [F.color_child T hcov h]
    split
    · assumption
    · exact Classical.choose_spec (hcov v)

/-- If a child's color differs from its parent's, the parent's color is not
a label of the child. -/
theorem color_parent_not_mem {v w : V} (h : F.parent v = some w)
    (hne : F.color T hcov v ≠ F.color T hcov w) :
    v ∉ T (F.color T hcov w) := by
  intro hv
  apply hne
  rw [F.color_child T hcov h]
  simp [hv]

end Coloring

/-! ## The rooted-cover inequality -/

variable [Fintype V] [DecidableEq V]

/-- **Rooted-cover inequality** (`lem:rooted-cover`, eq. `rooted-cover`).
For a cover `T : ι → Finset V` of the vertex set in which every member has a
private vertex, `∑ᵢ (|δ⁻_F(Tᵢ)| + |Tᵢ ∩ R_F|) ≥ m`. -/
theorem rooted_cover {ι : Type*} [Fintype ι] [DecidableEq ι] (T : ι → Finset V)
    (hcov : ∀ v, ∃ i, v ∈ T i)
    (hpriv : ∀ i, ∃ v, v ∈ T i ∧ ∀ j, j ≠ i → v ∉ T j) :
    Fintype.card ι ≤ ∑ i, (F.inArcs (T i) + F.rootCount (T i)) := by
  classical
  set c := F.color T hcov with hc
  -- The counted incidences.
  let pred : ι × V → Prop := fun p =>
    (F.IsRoot p.2 ∧ p.2 ∈ T p.1) ∨ F.Enters (T p.1) p.2
  let P : Finset (ι × V) := univ.filter pred
  have hsum : ∑ i, (F.inArcs (T i) + F.rootCount (T i)) = P.card := by
    have h1 : P.card = ∑ i, (univ.filter fun v => pred (i, v)).card := by
      rw [show P = (univ ×ˢ univ).filter pred by simp [P, Finset.univ_product_univ]]
      rw [Finset.card_filter, Finset.sum_product]
      exact Finset.sum_congr rfl fun i _ => (Finset.card_filter _ _).symm
    rw [h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (univ.filter fun v => pred (i, v)) =
        (univ.filter (F.Enters (T i))) ∪ (T i).filter F.IsRoot by
          ext v; simp [pred]; tauto]
    rw [Finset.card_union_of_disjoint]
    · rfl
    · rw [Finset.disjoint_left]
      intro v hv hv'
      simp only [mem_filter, mem_univ, true_and] at hv hv'
      obtain ⟨_, w, hw, _⟩ := hv
      have : F.parent v = none := hv'.2
      rw [hw] at this; cases this
  rw [hsum]
  -- Each color class is nonempty (private witnesses).
  have hcolor : ∀ i, ∃ v, c v = i := by
    intro i
    obtain ⟨v, hv, hpv⟩ := hpriv i
    refine ⟨v, ?_⟩
    by_contra hne
    exact hpv _ hne (F.color_mem T hcov v)
  -- A minimum-height vertex of each color.
  have hsel : ∀ i, ∃ s, c s = i ∧ ∀ u, c u = i → F.height s ≤ F.height u := by
    intro i
    have hne : (univ.filter fun v => c v = i).Nonempty := by
      obtain ⟨v, hv⟩ := hcolor i; exact ⟨v, by simp [hv]⟩
    obtain ⟨s, hs, hmin⟩ := Finset.exists_min_image _ F.height hne
    exact ⟨s, (mem_filter.1 hs).2, fun u hu => hmin u (by simp [hu])⟩
  choose s hs hsmin using hsel
  -- The partner index for the selected vertex.
  let j : ι → ι := fun i =>
    match F.parent (s i) with
    | none => i
    | some w => c w
  have hmem : ∀ i, (j i, s i) ∈ P := by
    intro i
    simp only [P, mem_filter, mem_univ, true_and, pred]
    cases hp : F.parent (s i) with
    | none =>
      left
      refine ⟨hp, ?_⟩
      simp only [j, hp]
      have := F.color_mem T hcov (s i)
      rw [← hc, hs i] at this
      exact this
    | some w =>
      right
      simp only [j, hp]
      have hne : c (s i) ≠ c w := by
        intro heq
        have := hsmin i w (by rw [← heq, hs i])
        have := F.height_lt_of_parent hp
        omega
      refine ⟨F.color_parent_not_mem T hcov hp hne, w, hp, F.color_mem T hcov w⟩
  have hinj : Function.Injective fun i => (j i, s i) := by
    intro a b hab
    have : s a = s b := (Prod.ext_iff.1 hab).2
    rw [← hs a, ← hs b, this]
  calc Fintype.card ι = (univ.image fun i => (j i, s i)).card := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
    _ ≤ P.card := by
        apply Finset.card_le_card
        intro p hp
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
        exact hmem i

/-! ## The weighted form -/

/-- **Weighted rooted-cover inequality** (second display of `lem:rooted-cover`). -/
theorem rooted_cover_weighted {ι : Type*} [Fintype ι] [DecidableEq ι] (T : ι → Finset V)
    (hcov : ∀ v, ∃ i, v ∈ T i)
    (hpriv : ∀ i, ∃ v, v ∈ T i ∧ ∀ j, j ≠ i → v ∉ T j)
    {γ : ℝ} (hγ : 0 < γ) :
    (Fintype.card ι : ℝ) * min 1 γ ≤
      ∑ i, ((F.inArcs (T i) : ℝ) + γ * (F.rootCount (T i) : ℝ)) := by
  have hcard : (Fintype.card ι : ℝ) ≤ ∑ i, ((F.inArcs (T i) : ℝ) + (F.rootCount (T i) : ℝ)) := by
    exact_mod_cast F.rooted_cover T hcov hpriv
  have hmin0 : 0 ≤ min 1 γ := le_min zero_le_one hγ.le
  calc (Fintype.card ι : ℝ) * min 1 γ
      ≤ (∑ i, ((F.inArcs (T i) : ℝ) + (F.rootCount (T i) : ℝ))) * min 1 γ :=
        mul_le_mul_of_nonneg_right hcard hmin0
    _ = ∑ i, (min 1 γ * (F.inArcs (T i) : ℝ) + min 1 γ * (F.rootCount (T i) : ℝ)) := by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i _ => by ring
    _ ≤ ∑ i, ((F.inArcs (T i) : ℝ) + γ * (F.rootCount (T i) : ℝ)) := by
        refine Finset.sum_le_sum fun i _ => add_le_add ?_ ?_
        · calc min 1 γ * (F.inArcs (T i) : ℝ) ≤ 1 * (F.inArcs (T i) : ℝ) :=
                mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _)
            _ = _ := one_mul _
        · exact mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg _)

end RootedForest

/-! ## Acyclicity from the absence of directed cycles -/

/-- On a finite vertex type, a parent map with no directed cycle has
terminating ancestor chains, so it defines a `RootedForest`. -/
theorem acyclic_of_noCycle {V : Type*} [Finite V] (parent : V → Option V)
    (h : ∀ v n, 0 < n → (fun o : Option V => o.bind parent)^[n] (some v) ≠ some v) :
    ∀ v : V, ∃ n : ℕ, (fun o : Option V => o.bind parent)^[n] (some v) = none := by
  intro v
  by_contra hne
  have hs : ∀ n, ∃ x, (fun o : Option V => o.bind parent)^[n] (some v) = some x :=
    fun n => Option.ne_none_iff_exists'.1 (fun h0 => hne ⟨n, h0⟩)
  choose f hf using hs
  obtain ⟨a, b, hab, heq⟩ := Finite.exists_ne_map_eq_of_infinite f
  have key : ∀ a b, a < b → f a = f b → False := by
    intro a b hab heq
    apply h (f a) (b - a) (by omega)
    calc (fun o : Option V => o.bind parent)^[b - a] (some (f a))
        = (fun o : Option V => o.bind parent)^[b - a]
            ((fun o : Option V => o.bind parent)^[a] (some v)) := by rw [hf a]
      _ = (fun o : Option V => o.bind parent)^[b] (some v) := by
          rw [← Function.iterate_add_apply, Nat.sub_add_cancel hab.le]
      _ = some (f a) := by rw [hf b, heq]
  rcases lt_or_gt_of_ne hab with h' | h'
  · exact key a b h' heq
  · exact key b a h' heq.symm

/-- The rooted forest determined by a cycle-free parent map. -/
def RootedForest.ofNoCycle {V : Type*} [Finite V] (parent : V → Option V)
    (h : ∀ v n, 0 < n → (fun o : Option V => o.bind parent)^[n] (some v) ≠ some v) :
    RootedForest V :=
  ⟨parent, acyclic_of_noCycle parent h⟩

/-! ## Mixtures of rooted forests and root concentration -/

section Mixture

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {J : Type*} [Fintype J] (p : J → ℝ) (F : J → RootedForest V)

/-- Expected arc vector `y_{uw} = Pr[parent u = w]` (arc `u → w`). -/
noncomputable def arcVec (u w : V) : ℝ :=
  ∑ j, p j * (if (F j).parent u = some w then 1 else 0)

/-- Root marginals `r_v = Pr[v is a root]`. -/
noncomputable def rootVec (v : V) : ℝ :=
  ∑ j, p j * (if (F j).parent v = none then 1 else 0)

/-- `y(δ⁻(T))`: total `y`-weight of arcs `u → w` with `u ∉ T`, `w ∈ T`. -/
noncomputable def inWeight (y : V → V → ℝ) (T : Finset V) : ℝ :=
  ∑ u ∈ Tᶜ, ∑ w ∈ T, y u w

/-- `r(T)`. -/
noncomputable def setWeight (r : V → ℝ) (T : Finset V) : ℝ := ∑ v ∈ T, r v

theorem inArcs_eq_sum (G : RootedForest V) (T : Finset V) :
    (G.inArcs T : ℝ) = ∑ u ∈ Tᶜ, ∑ w ∈ T, (if G.parent u = some w then (1 : ℝ) else 0) := by
  unfold RootedForest.inArcs
  rw [Finset.card_filter]
  push_cast
  rw [← Finset.sum_compl_add_sum T]
  have h2 : ∑ u ∈ T, (if G.Enters T u then (1 : ℝ) else 0) = 0 :=
    Finset.sum_eq_zero fun u hu => by simp [show ¬ G.Enters T u from fun he => he.1 hu]
  rw [h2, add_zero]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [Finset.mem_compl] at hu
  cases hp : G.parent u with
  | none => simp [RootedForest.Enters, hp]
  | some w0 =>
    simp only [Option.some.injEq]
    rw [Finset.sum_ite_eq]
    by_cases hw : w0 ∈ T
    · have he : G.Enters T u := ⟨hu, w0, hp, hw⟩
      simp [hw, he]
    · have he : ¬ G.Enters T u := by
        rintro ⟨-, w, hw', hwT⟩
        rw [hp] at hw'; cases hw'; exact hw hwT
      simp [hw, he]

omit [Fintype V] in
theorem rootCount_eq_sum (G : RootedForest V) (T : Finset V) :
    (G.rootCount T : ℝ) = ∑ v ∈ T, (if G.parent v = none then (1 : ℝ) else 0) := by
  unfold RootedForest.rootCount
  rw [Finset.card_filter]
  push_cast
  rfl

theorem inWeight_arcVec (T : Finset V) :
    inWeight (arcVec p F) T = ∑ j, p j * ((F j).inArcs T : ℝ) := by
  unfold inWeight arcVec
  calc ∑ u ∈ Tᶜ, ∑ w ∈ T, ∑ j, p j * (if (F j).parent u = some w then (1 : ℝ) else 0)
      = ∑ u ∈ Tᶜ, ∑ j, ∑ w ∈ T, p j * (if (F j).parent u = some w then (1 : ℝ) else 0) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ j, ∑ u ∈ Tᶜ, ∑ w ∈ T, p j * (if (F j).parent u = some w then (1 : ℝ) else 0) :=
        Finset.sum_comm
    _ = ∑ j, p j * ((F j).inArcs T : ℝ) := by
        simp_rw [inArcs_eq_sum, Finset.mul_sum]

omit [Fintype V] in
theorem setWeight_rootVec (T : Finset V) :
    setWeight (rootVec p F) T = ∑ j, p j * ((F j).rootCount T : ℝ) := by
  unfold setWeight rootVec
  rw [Finset.sum_comm]
  simp_rw [rootCount_eq_sum, Finset.mul_sum]

/-- **Concentration of fractional roots** (`cor:root-concentration`).
Let `y` and `r` be the expected arc vector and root marginals of a finite
mixture of rooted forests on a nonempty finite vertex type. For every `γ > 0`
some vertex `v` satisfies `y(δ⁻(T)) + γ r(T) ≥ min{1, γ}` for every `T ∋ v`. -/
theorem root_concentration [Nonempty V] (hp : ∀ j, 0 ≤ p j) (hsum : ∑ j, p j = 1)
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ v : V, ∀ T : Finset V, v ∈ T →
      min 1 γ ≤ inWeight (arcVec p F) T + γ * setWeight (rootVec p F) T := by
  classical
  set μ := min 1 γ with hμ
  set cost : Finset V → ℝ := fun T => inWeight (arcVec p F) T + γ * setWeight (rootVec p F) T
    with hcost
  by_contra hcon
  simp only [not_exists, not_forall, not_le] at hcon
  -- For each vertex a cheap set containing it.
  choose C hvC hC using hcon
  -- A subfamily of minimum size that still covers.
  let Covers : Finset V → Prop := fun S => ∀ u, ∃ s ∈ S, u ∈ C s
  have hne : (univ.powerset.filter Covers).Nonempty :=
    ⟨univ, by simp only [mem_filter, mem_powerset, subset_refl, true_and]
              exact fun u => ⟨u, mem_univ u, hvC u⟩⟩
  obtain ⟨S, hS, hSmin⟩ := Finset.exists_min_image _ Finset.card hne
  have hScov : Covers S := (mem_filter.1 hS).2
  have hSmin' : ∀ S', Covers S' → S.card ≤ S'.card := fun S' h' =>
    hSmin S' (mem_filter.2 ⟨mem_powerset.2 (subset_univ _), h'⟩)
  -- The cover indexed by `S`.
  let T : S → Finset V := fun s => C s
  have hcov : ∀ v, ∃ i, v ∈ T i := by
    intro v
    obtain ⟨s, hs, hv⟩ := hScov v
    exact ⟨⟨s, hs⟩, hv⟩
  have hpriv : ∀ i, ∃ v, v ∈ T i ∧ ∀ j, j ≠ i → v ∉ T j := by
    rintro ⟨s, hs⟩
    have hnot : ¬ Covers (S.erase s) := by
      intro h'
      have := hSmin' _ h'
      rw [Finset.card_erase_of_mem hs] at this
      have : 0 < S.card := Finset.card_pos.2 ⟨s, hs⟩
      omega
    simp only [Covers, not_forall, not_exists, not_and] at hnot
    obtain ⟨u, hu⟩ := hnot
    refine ⟨u, ?_, ?_⟩
    · obtain ⟨t, ht, hut⟩ := hScov u
      by_cases hts : t = s
      · subst hts; exact hut
      · exact absurd hut (hu t (Finset.mem_erase.2 ⟨hts, ht⟩))
    · rintro ⟨t, ht⟩ hts
      have hts' : t ≠ s := fun h => hts (Subtype.ext h)
      exact hu t (Finset.mem_erase.2 ⟨hts', ht⟩)
  -- Lower bound from the rooted-cover inequality, averaged.
  have hlow : (Fintype.card S : ℝ) * μ ≤ ∑ i, cost (T i) := by
    have hterm : ∀ i, cost (T i) =
        ∑ j, p j * (((F j).inArcs (T i) : ℝ) + γ * ((F j).rootCount (T i) : ℝ)) := by
      intro i
      show inWeight (arcVec p F) (T i) + γ * setWeight (rootVec p F) (T i) = _
      rw [inWeight_arcVec, setWeight_rootVec, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hexp : ∑ i, cost (T i) =
        ∑ j, p j * ∑ i, (((F j).inArcs (T i) : ℝ) + γ * ((F j).rootCount (T i) : ℝ)) := by
      rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm
    rw [hexp]
    calc (Fintype.card S : ℝ) * μ = ∑ j, p j * ((Fintype.card S : ℝ) * μ) := by
          rw [← Finset.sum_mul, hsum, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left
            ((F j).rooted_cover_weighted T hcov hpriv hγ) (hp j)
  have hup : ∑ i, cost (T i) < (Fintype.card S : ℝ) * μ := by
    have : (univ : Finset S).Nonempty := by
      obtain ⟨v⟩ := ‹Nonempty V›
      obtain ⟨i, -⟩ := hcov v
      exact ⟨i, mem_univ _⟩
    calc ∑ i, cost (T i) < ∑ _i : S, μ := Finset.sum_lt_sum_of_nonempty this fun i _ => hC i
      _ = (Fintype.card S : ℝ) * μ := by simp
  linarith

end Mixture

end FractionalForest
end CutQueryComplexity
