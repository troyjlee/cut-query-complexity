import CutQueryComplexity.AllPairsAudit.CutAlgebra
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.BigOperators

/-!
# Explicit star replacement

For a block map `p : V → B`, keep exactly the original interblock edges and
replace each block's internal edges by a star with a fresh proxy. Its spoke at
`u` has weight equal to the original degree of `u` inside its own block.
No contraction capacities, infinities, or all-pairs preservation hypotheses
enter the graph definition or the cut-domination theorem.
-/

set_option autoImplicit false

namespace CutQueryComplexity.AllPairsAudit

open WeightedGraph
noncomputable section
open scoped Classical

variable {V B : Type*} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]

def separated {A : Type*} [DecidableEq A] (S : Finset A) (u v : A) : ℝ :=
  if u ∈ S then (if v ∈ S then 0 else 1) else (if v ∈ S then 1 else 0)

omit [Fintype V] [Fintype B] [DecidableEq B] in
theorem separated_symm (S : Finset V) (u v : V) : separated S u v = separated S v u := by
  by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp [separated, hu, hv]

omit [Fintype B] [DecidableEq B] in
theorem two_cut_eq_energy (G : WeightedGraph V) (S : Finset V) :
    2 * G.cut S = ∑ u, ∑ v, G.w u v * separated S u v := by
  have hp (u v : V) : G.w u v * separated S u v =
      (if u ∈ S ∧ v ∉ S then G.w u v else 0) +
      (if v ∈ S ∧ u ∉ S then G.w u v else 0) := by
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp [separated, hu, hv]
  simp_rw [hp]
  simp_rw [Finset.sum_add_distrib]
  have hr : (∑ u : V, ∑ v : V, if v ∈ S ∧ u ∉ S then G.w u v else 0) = G.cut S := by
    rw [Finset.sum_comm, G.cut_eq_sum_ite]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by rw [G.symm]
  rw [hr, ← G.cut_eq_sum_ite]
  ring

def internalDegree (G : WeightedGraph V) (p : V → B) (u : V) : ℝ :=
  ∑ v, if p v = p u then G.w u v else 0

def star (G : WeightedGraph V) (p : V → B) : WeightedGraph (V ⊕ B) where
  w
    | .inl u, .inl v => if p u = p v then 0 else G.w u v
    | .inl u, .inr b => if p u = b then internalDegree G p u else 0
    | .inr b, .inl v => if p v = b then internalDegree G p v else 0
    | .inr _, .inr _ => 0
  symm u v := by
    cases u <;> cases v <;> simp [eq_comm, G.symm]
  nonneg u v := by
    have hd (x : V) : 0 ≤ internalDegree G p x :=
      Finset.sum_nonneg fun y _ => by split <;> simp_all [G.nonneg]
    cases u <;> cases v <;> dsimp <;> (try split) <;> simp_all [G.nonneg]
  diag u := by cases u <;> simp

/-- Restrict an augmented shore to the original labeled vertices. -/
def originalShore (A : Finset (V ⊕ B)) : Finset V :=
  Finset.univ.filter fun u => Sum.inl u ∈ A

omit [Fintype B] in
@[simp] theorem mem_originalShore (A : Finset (V ⊕ B)) (u : V) :
    u ∈ originalShore A ↔ Sum.inl u ∈ A := by simp [originalShore]

/-- A shore is a union of complete contraction blocks. -/
def Respects (p : V → B) (S : Finset V) : Prop :=
  ∀ u v, p u = p v → (u ∈ S ↔ v ∈ S)

/-- Put a proxy inside exactly when its block meets the original shore. -/
def lift (p : V → B) (S : Finset V) : Finset (V ⊕ B) :=
  S.disjSum (S.image p)

omit [Fintype V] [Fintype B] [DecidableEq V] in
@[simp] theorem mem_lift_left (p : V → B) (S : Finset V) (u : V) :
    Sum.inl u ∈ lift p S ↔ u ∈ S := by simp [lift]

omit [Fintype V] [Fintype B] [DecidableEq V] in
theorem mem_lift_proxy (p : V → B) {S : Finset V} (hS : Respects p S) (u : V) :
    Sum.inr (p u) ∈ lift p S ↔ u ∈ S := by
  simp only [lift, Finset.inr_mem_disjSum, Finset.mem_image]
  constructor
  · rintro ⟨v, hv, hp⟩
    exact (hS v u hp).mp hv
  · intro hu
    exact ⟨u, hu, rfl⟩

omit [Fintype B] in
@[simp] theorem originalShore_lift (p : V → B) (S : Finset V) :
    originalShore (lift p S) = S := by ext; simp

/-- A directly expanded cut formula, counting each spoke once. -/
theorem star_cut_expand (G : WeightedGraph V) (p : V → B) (A : Finset (V ⊕ B)) :
    2 * (star G p).cut A =
      (∑ u, ∑ v, (if p u = p v then 0 else G.w u v) * separated A (.inl u) (.inl v)) +
      2 * ∑ u, internalDegree G p u * separated A (.inl u) (.inr (p u)) := by
  rw [two_cut_eq_energy]
  simp only [Fintype.sum_sum_type, star]
  simp_rw [Finset.sum_add_distrib]
  have h1 (u : V) :
      (∑ b : B, (if p u = b then internalDegree G p u else 0) * separated A (.inl u) (.inr b)) =
      internalDegree G p u * separated A (.inl u) (.inr (p u)) := by
    simp only [ite_mul, zero_mul]
    simp
  have h2 :
      (∑ b : B, ∑ v : V, (if p v = b then internalDegree G p v else 0) *
        separated A (.inr b) (.inl v)) =
      ∑ v, internalDegree G p v * separated A (.inl v) (.inr (p v)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    simp_rw [separated_symm A (.inr _) (.inl v)]
    exact h1 v
  simp only [h1, h2, zero_mul, Finset.sum_const_zero, add_zero]
  ring

/-- Per original edge, the replacement cost is its path through the block proxy. -/
theorem star_cut_energy (G : WeightedGraph V) (p : V → B) (A : Finset (V ⊕ B)) :
    2 * (star G p).cut A = ∑ u, ∑ v, G.w u v *
      (if p u = p v then
        separated A (.inl u) (.inr (p u)) + separated A (.inl v) (.inr (p u))
       else separated A (.inl u) (.inl v)) := by
  rw [star_cut_expand]
  have hi : (∑ u, internalDegree G p u * separated A (.inl u) (.inr (p u))) =
      ∑ u, ∑ v, if p u = p v then G.w u v * separated A (.inl u) (.inr (p u)) else 0 := by
    apply Finset.sum_congr rfl
    intro u _
    simp only [internalDegree, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro v _
    by_cases h : p u = p v
    · simp [h]
    · simp [h, Ne.symm h]
  have hs : (∑ u, ∑ v, if p u = p v then
      G.w u v * separated A (.inl v) (.inr (p u)) else 0) =
      ∑ u, ∑ v, if p u = p v then G.w u v * separated A (.inl u) (.inr (p u)) else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    by_cases h : p u = p v
    · simp [h, G.symm v u]
    · simp [h, Ne.symm h]
  have hp (u v : V) : G.w u v *
      (if p u = p v then separated A (.inl u) (.inr (p u)) +
        separated A (.inl v) (.inr (p u)) else separated A (.inl u) (.inl v)) =
      (if p u = p v then 0 else G.w u v) * separated A (.inl u) (.inl v) +
      (if p u = p v then G.w u v * separated A (.inl u) (.inr (p u)) else 0) +
      (if p u = p v then G.w u v * separated A (.inl v) (.inr (p u)) else 0) := by
    by_cases h : p u = p v <;> simp [h, mul_add]
  simp_rw [hp, Finset.sum_add_distrib]
  rw [hs, hi]
  ring

/-- Every augmented cut dominates the original cut obtained by restriction. -/
theorem star_cut_dominates (G : WeightedGraph V) (p : V → B) (A : Finset (V ⊕ B)) :
    G.cut (originalShore A) ≤ (star G p).cut A := by
  have henergy : (∑ u, ∑ v, G.w u v * separated (originalShore A) u v) ≤
      ∑ u, ∑ v, G.w u v *
        (if p u = p v then separated A (.inl u) (.inr (p u)) +
          separated A (.inl v) (.inr (p u)) else separated A (.inl u) (.inl v)) := by
    apply Finset.sum_le_sum
    intro u _
    apply Finset.sum_le_sum
    intro v _
    apply mul_le_mul_of_nonneg_left _ (G.nonneg u v)
    by_cases hp : p u = p v
    · by_cases hu : Sum.inl u ∈ A <;> by_cases hv : Sum.inl v ∈ A <;>
        by_cases hb : Sum.inr (p v) ∈ A <;> simp [hp, separated, hu, hv, hb]
    · simp [hp, separated]
  rw [← two_cut_eq_energy, ← star_cut_energy] at henergy
  linarith

/-- A block-respecting shore lifts with exactly the original cut value. -/
theorem star_cut_lift (G : WeightedGraph V) (p : V → B) {S : Finset V}
    (hS : Respects p S) : (star G p).cut (lift p S) = G.cut S := by
  have he : 2 * (star G p).cut (lift p S) = 2 * G.cut S := by
    rw [star_cut_energy, two_cut_eq_energy]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    by_cases hp : p u = p v
    · have hv := hS u v hp
      by_cases hu : u ∈ S
      · have hv' := hv.mp hu
        simp [hp, separated, mem_lift_proxy p hS, hu, hv']
      · have hv' : v ∉ S := fun h => hu (hv.mpr h)
        simp [hp, separated, mem_lift_proxy p hS, hu, hv']
    · simp [hp, separated]
  linarith

/-- A block-respecting shore plus one original vertex also lifts exactly.
Its proxy stays on the side of the rest of the block. -/
theorem star_cut_lift_insert (G : WeightedGraph V) (p : V → B) {S : Finset V}
    (hS : Respects p S) {s : V} (hs : s ∉ S) :
    (star G p).cut (insert (Sum.inl s) (lift p S)) = G.cut (insert s S) := by
  have he : 2 * (star G p).cut (insert (Sum.inl s) (lift p S)) =
      2 * G.cut (insert s S) := by
    rw [star_cut_energy, two_cut_eq_energy]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    by_cases huv : u = v
    · subst v
      simp [G.diag]
    by_cases hp : p u = p v
    · have hv := hS u v hp
      by_cases hus : u = s
      · subst u
        have hv' : v ∉ S := fun h => hs (hv.mpr h)
        simp [hp, separated, mem_lift_proxy p hS, hs, hv', Ne.symm huv]
      · by_cases hvs : v = s
        · subst v
          have hu' : u ∉ S := fun h => hs (hv.mp h)
          simp [hp, separated, mem_lift_proxy p hS, hs, hu', hus]
        · by_cases hu : u ∈ S
          · have hv' := hv.mp hu
            simp [hp, separated, mem_lift_proxy p hS, hu, hv', hus, hvs]
          · have hv' : v ∉ S := fun h => hu (hv.mpr h)
            simp [hp, separated, mem_lift_proxy p hS, hu, hv', hus, hvs]
    · simp [hp, separated]
  linarith

omit [Fintype B] in
@[simp] theorem originalShore_lift_insert (p : V → B) (S : Finset V) (s : V) :
    originalShore (insert (Sum.inl s) (lift p S)) = insert s S := by ext; simp

omit [DecidableEq V] [Fintype B] in
/-- Each spoke can be recovered from the original degree and the recorded
interblock edge endpoints; internal input edges need not be recovered. -/
theorem internalDegree_from_external (G : WeightedGraph V) (p : V → B) (u : V) :
    internalDegree G p u = G.degree u -
      ∑ v, if p u = p v then 0 else G.w u v := by
  have h : internalDegree G p u +
      (∑ v, if p u = p v then 0 else G.w u v) = G.degree u := by
    rw [internalDegree, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hp : p u = p v
    · simp [hp]
    · simp [hp, Ne.symm hp]
  linarith

omit [DecidableEq V] [DecidableEq B] in
/-- A surjective block map uses no more proxies than original vertices. -/
theorem star_vertex_bound (p : V → B) (hp : Function.Surjective p) :
    Fintype.card (V ⊕ B) ≤ 2 * Fintype.card V := by
  rw [Fintype.card_sum]
  have := Fintype.card_le_of_surjective p hp
  omega

end
end CutQueryComplexity.AllPairsAudit
