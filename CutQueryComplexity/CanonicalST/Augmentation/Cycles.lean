import CutQueryComplexity.CanonicalST.Augmentation.Support
import CutQueryComplexity.Certificate.MaxFlow
import CutQueryComplexity.DirectedUnitST.Repair.IntegralRounding
import Mathlib.Order.Extension.Well

/-!
# Circulation deletion and a topological numbering

Minimizing total absolute flow in a compact feasible box removes every
positive directed circulation. Integer rounding inside the resulting sign
support then retains acyclicity, capacities, and all divergences. Finally a
finite strict-order extension constructs an injective topological numbering.
Neither acyclicity nor a support bound is an assumed output certificate.
-/

set_option autoImplicit false

namespace CutQueryComplexity.CanonicalST.Augmentation

open Finset Certificate Filter Topology
open DirectedUnitST.Repair
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

def NoDirectedCycle (f : V → V → ℝ) : Prop :=
  ∀ u v, 0 < f u v → ¬ Relation.ReflTransGen (fun x y => 0 < f x y) v u

def flowMass (f : V → V → ℝ) : ℝ := ∑ u, ∑ v, |f u v|

def FlowBox (c : V → V → ℕ) (d : V → ℝ) : Set (V → V → ℝ) :=
  {f | IsFlow f ∧ (∀ u v, f u v ≤ c u v) ∧ ∀ u, netOut f u = d u}

theorem flowBox_compact (c : V → V → ℕ) (d : V → ℝ) : IsCompact (FlowBox c d) := by
  have hbox : IsCompact (Set.univ.pi fun u : V => Set.univ.pi fun v : V =>
      Set.Icc (-(c v u : ℝ)) (c u v : ℝ)) :=
    isCompact_univ_pi fun u => isCompact_univ_pi fun v => isCompact_Icc
  refine hbox.of_isClosed_subset ?_ ?_
  · have hev : ∀ u v : V, Continuous fun f : V → V → ℝ => f u v := fun u v => by fun_prop
    simp only [FlowBox, IsFlow, Set.ofPred_and, Set.ofPred_forall]
    refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_)
    · exact isClosed_iInter fun u => isClosed_iInter fun v =>
        isClosed_eq (hev v u) (hev u v).neg
    · exact isClosed_iInter fun u => isClosed_iInter fun v =>
        isClosed_le (hev u v) continuous_const
    · exact isClosed_iInter fun u => isClosed_eq (continuous_netOut u) continuous_const
  · intro f hf
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies]
    intro u v
    refine ⟨?_, hf.2.1 u v⟩
    have h := hf.2.1 v u
    rw [hf.1 u v] at h
    linarith

/-- A positive arc together with a return walk yields a nonzero conserving
direction supported with the same signs as the original flow. -/
theorem cycle_direction {f : V → V → ℝ} (hf : IsFlow f) {u v : V}
    (huv : 0 < f u v) (hpath : Relation.ReflTransGen (fun x y => 0 < f x y) v u) :
    ∃ g : V → V → ℝ, IsFlow g ∧ (∀ x, netOut g x = 0) ∧
      (∀ x y, 0 < g x y → 0 < f x y) ∧ 0 < g u v := by
  obtain ⟨w, hw, hwpos, hwnet⟩ := exists_walkFlow (fun x y => 0 < f x y) hpath
  let g : V → V → ℝ := fun x y => w x y + arc u v x y
  have hne : u ≠ v := by intro he; subst v; simpa [hf.self] using huv
  have hwuv : 0 ≤ w u v := by
    by_contra h
    have hrev : 0 < w v u := by rw [hw u v]; linarith
    have hfvu := hwpos v u hrev
    rw [hf u v] at hfvu
    linarith
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · intro x y
    dsimp [g]
    rw [hw x y, isFlow_arc u v x y]
    ring
  · intro x
    dsimp [g]
    rw [netOut_add, hwnet, netOut_arc]
    ring
  · intro x y hxy
    by_cases hwxy : 0 < w x y
    · exact hwpos x y hwxy
    · have ha : 0 < arc u v x y := by dsimp [g] at hxy; linarith
      obtain ⟨rfl, rfl⟩ := arc_pos ha
      exact huv
  · dsimp [g]
    have ha : arc u v u v = 1 := by simp [arc, hne, Ne.symm hne]
    rw [ha]
    linarith

private theorem eventually_shrink (x y : ℝ)
    (hpos : 0 < y → 0 < x) (hneg : y < 0 → x < 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      x - ε * y ≤ max 0 x ∧ |x - ε * y| = |x| - ε * |y| := by
  have heps : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  rcases lt_trichotomy y 0 with hy | hy | hy
  · have hx := hneg hy
    have hh := eventually_add_mul_lt (show (0 : ℝ) < -x by linarith) (-y)
    filter_upwards [heps, hh] with ε hε hh
    have he : x - ε * y ≤ 0 := by linarith
    refine ⟨he.trans (le_max_left _ _), ?_⟩
    rw [abs_of_nonpos he, abs_of_nonpos hx.le, abs_of_nonpos hy.le]
    ring
  · filter_upwards with ε
    simp [hy, le_max_right 0 x]
  · have hx := hpos hy
    have hh := eventually_add_mul_lt hx y
    filter_upwards [heps, hh] with ε hε hh
    have he : 0 ≤ x - ε * y := by linarith
    refine ⟨?_, ?_⟩
    · have hmax := le_max_right (0 : ℝ) x
      nlinarith
    · rw [abs_of_nonneg he, abs_of_nonneg hx.le, abs_of_nonneg hy.le]

theorem flowMass_pos {g : V → V → ℝ} {u v : V} (h : 0 < g u v) : 0 < flowMass g := by
  have hrow : |g u v| ≤ ∑ y, |g u y| :=
    single_le_sum (fun y _ => abs_nonneg (g u y)) (mem_univ v)
  have htotal : (∑ y, |g u y|) ≤ flowMass g :=
    single_le_sum (fun x _ => sum_nonneg fun y _ => abs_nonneg (g x y)) (mem_univ u)
  exact (lt_of_lt_of_le h (le_abs_self _)).trans_le (hrow.trans htotal)

theorem minimum_mass_noDirectedCycle (c : V → V → ℕ) (d : V → ℝ)
    {f : V → V → ℝ} (hf : f ∈ FlowBox c d)
    (hmin : ∀ g ∈ FlowBox c d, flowMass f ≤ flowMass g) : NoDirectedCycle f := by
  intro u v huv hpath
  obtain ⟨g, hgflow, hgdiv, hgpos, hguv⟩ := cycle_direction hf.1 huv hpath
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x y,
      f x y - ε * g x y ≤ max 0 (f x y) ∧
        |f x y - ε * g x y| = |f x y| - ε * |g x y| := by
    rw [eventually_all]
    intro x
    rw [eventually_all]
    intro y
    apply eventually_shrink _ _ (hgpos x y)
    intro hneg
    have hp : 0 < g y x := by rw [hgflow x y]; linarith
    have hfp := hgpos y x hp
    rw [hf.1 x y] at hfp
    linarith
  have heps : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε, hε, he⟩ := (heps.and hev).exists
  let f' : V → V → ℝ := fun x y => f x y - ε * g x y
  have hf' : f' ∈ FlowBox c d := by
    refine ⟨?_, ?_, ?_⟩
    · intro x y
      dsimp [f']
      rw [hf.1 x y, hgflow x y]
      ring
    · intro x y
      exact (he x y).1.trans (max_le (Nat.cast_nonneg _) (hf.2.1 x y))
    · intro x
      change (∑ y, (f x y - ε * g x y)) = d x
      rw [sum_sub_distrib, ← mul_sum]
      change netOut f x - ε * netOut g x = d x
      rw [hf.2.2 x, hgdiv x, mul_zero, sub_zero]
  have hmass : flowMass f' = flowMass f - ε * flowMass g := by
    unfold flowMass
    simp only [f', (fun x y => (he x y).2), sum_sub_distrib, ← mul_sum]
  have hm := hmin f' hf'
  rw [hmass] at hm
  have hpositive := flowMass_pos hguv
  nlinarith

/-- Actual circulation deletion: a minimum-mass feasible flow has no
positive cycle, and still has exactly the specified divergence. -/
theorem exists_cycle_free_flow (c : V → V → ℕ) (f : V → V → ℝ)
    (hf : IsFlow f) (hcap : ∀ u v, f u v ≤ c u v) :
    ∃ g : V → V → ℝ, IsFlow g ∧ (∀ u v, g u v ≤ c u v) ∧
      (∀ u, netOut g u = netOut f u) ∧ NoDirectedCycle g := by
  have hcont : Continuous (flowMass (V := V)) := by unfold flowMass; fun_prop
  obtain ⟨g, hg, hmin⟩ := (flowBox_compact c (netOut f)).exists_isMinOn
    ⟨f, hf, hcap, fun _ => rfl⟩ hcont.continuousOn
  exact ⟨g, hg.1, hg.2.1, hg.2.2, minimum_mass_noDirectedCycle c (netOut f) hg hmin⟩

/-- Integer rounding is restricted to the already acyclic sign support.
It cannot create a positive arc outside that support. -/
theorem exists_cycle_free_integral_flow (c : V → V → ℕ) (f : V → V → ℝ)
    (hf : IsFlow f) (hcap : ∀ u v, f u v ≤ c u v)
    (hdiv : ∀ u, IntegerValue (netOut f u)) :
    ∃ g : V → V → ℝ, IsFlow g ∧ (∀ u v, g u v ≤ c u v) ∧
      (∀ u, netOut g u = netOut f u) ∧ (∀ u v, IntegerValue (g u v)) ∧ NoDirectedCycle g := by
  obtain ⟨h, hhflow, hhcap, hhdiv, hhcycle⟩ := exists_cycle_free_flow c f hf hcap
  let lo : V → V → ℤ := fun u v => if 0 < h v u then -(c v u : ℤ) else 0
  let hi : V → V → ℤ := fun u v => if 0 < h u v then (c u v : ℤ) else 0
  have hbounds : ∀ u v, (lo u v : ℝ) ≤ h u v ∧ h u v ≤ (hi u v : ℝ) := by
    intro u v
    constructor
    · by_cases hp : 0 < h v u
      · simp only [lo, hp, ↓reduceIte, Int.cast_neg, Int.cast_natCast]
        have hc := hhcap v u
        rw [hhflow u v] at hc
        linarith
      · simp only [lo, hp, ↓reduceIte, Int.cast_zero]
        rw [hhflow u v] at hp
        linarith
    · by_cases hp : 0 < h u v
      · simpa only [hi, hp, ↓reduceIte, Int.cast_natCast] using hhcap u v
      · simp only [hi, hp, ↓reduceIte, Int.cast_zero]
        linarith
  obtain ⟨g, hgflow, hgdiv, hgbounds, hgint⟩ := bounded_integral_flow lo hi h hhflow
    (fun u => by rw [hhdiv u]; exact hdiv u) hbounds
  have hsupport : ∀ u v, 0 < g u v → 0 < h u v := by
    intro u v hp
    by_contra hh
    have hg := (hgbounds u v).2
    simp only [hi, hh, ↓reduceIte, Int.cast_zero] at hg
    linarith
  refine ⟨g, hgflow, ?_, fun u => (hgdiv u).trans (hhdiv u), hgint, ?_⟩
  · intro u v
    have hg := (hgbounds u v).2
    by_cases hp : 0 < h u v
    · simpa only [hi, hp, ↓reduceIte, Int.cast_natCast] using hg
    · simp only [hi, hp, ↓reduceIte, Int.cast_zero] at hg
      exact hg.trans (Nat.cast_nonneg _)
  · intro u v huv hpath
    apply hhcycle u v (hsupport u v huv)
    exact Relation.ReflTransGen.mono hsupport v u hpath

/-- The numbering is constructed from the proved absence of cycles. -/
theorem topological_numbering {f : V → V → ℝ} (hf : NoDirectedCycle f) :
    ∃ p : V → Fin (Fintype.card V), Function.Injective p ∧
      ∀ u v, 0 < f u v → p u < p v := by
  let R : V → V → Prop := Relation.TransGen (fun u v => 0 < f u v)
  letI : IsTrans V R := ⟨fun _ _ _ h₁ h₂ => h₁.trans h₂⟩
  letI : Std.Irrefl R := ⟨fun u hu => by
    obtain ⟨v, huv, hpath⟩ := Relation.TransGen.head'_iff.mp hu
    exact hf u v huv hpath⟩
  letI : WellFounded R := Finite.wellFounded_of_trans_of_irrefl R
  obtain ⟨r, hr, hrwell⟩ := WellFounded.exists_well_order_ge R
  letI : IsWellOrder V r := hrwell
  letI : LinearOrder V := IsWellOrder.linearOrder r
  let e : Fin (Fintype.card V) ≃o V := Fintype.orderIsoFinOfCardEq V rfl
  refine ⟨e.symm, e.symm.injective, ?_⟩
  intro u v huv
  apply e.symm.strictMono
  exact hr u v (Relation.TransGen.single huv)

end
end CutQueryComplexity.CanonicalST.Augmentation

#print axioms CutQueryComplexity.CanonicalST.Augmentation.flowBox_compact
#print axioms CutQueryComplexity.CanonicalST.Augmentation.cycle_direction
#print axioms CutQueryComplexity.CanonicalST.Augmentation.minimum_mass_noDirectedCycle
#print axioms CutQueryComplexity.CanonicalST.Augmentation.exists_cycle_free_flow
#print axioms CutQueryComplexity.CanonicalST.Augmentation.exists_cycle_free_integral_flow
#print axioms CutQueryComplexity.CanonicalST.Augmentation.topological_numbering
