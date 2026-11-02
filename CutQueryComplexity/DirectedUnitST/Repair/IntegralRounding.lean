import CutQueryComplexity.DirectedUnitST.Repair.Decomposition
import CutQueryComplexity.Model.Prog
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic.ByContra

/-! # Bounded integral circulation rounding

An integer-divergence flow has no leaf in its fractional support. A fractional
cycle gives a conserving signed-unit direction; a minimum-slack adjustment
reaches an integer boundary, and induction on the fractional support terminates.
The root-circulation reduction then rounds arbitrary divergences with error
at most one per vertex, hence at most `2n` for canonical pair divergence.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DirectedUnitST.Repair

open Finset Certificate DirectedCertificate

/-- A real coordinate is an integer, with an explicit integer witness. -/
def IntegerValue (x : ℝ) : Prop := ∃ z : ℤ, x = z

theorem IntegerValue.zero : IntegerValue 0 := ⟨0, by simp⟩

theorem IntegerValue.neg {x : ℝ} (hx : IntegerValue x) : IntegerValue (-x) := by
  obtain ⟨z, rfl⟩ := hx
  exact ⟨-z, by simp⟩

theorem IntegerValue.add {x y : ℝ} (hx : IntegerValue x) (hy : IntegerValue y) :
    IntegerValue (x + y) := by
  obtain ⟨z, rfl⟩ := hx
  obtain ⟨w, rfl⟩ := hy
  exact ⟨z + w, by simp⟩

theorem IntegerValue.sub {x y : ℝ} (hx : IntegerValue x) (hy : IntegerValue y) :
    IntegerValue (x - y) := by
  obtain ⟨z, rfl⟩ := hx
  obtain ⟨w, rfl⟩ := hy
  exact ⟨z - w, by simp⟩

/-- Nonnegative integral capacities have natural-number witnesses, as
required by whole-path integral bottleneck updates. -/
theorem IntegerValue.exists_nat {x : ℝ} (hx : IntegerValue x) (h0 : 0 ≤ x) :
    ∃ k : ℕ, x = k := by
  obtain ⟨z, rfl⟩ := hx
  have hz : 0 ≤ z := by exact_mod_cast h0
  refine ⟨z.toNat, ?_⟩
  exact_mod_cast (Int.toNat_of_nonneg hz).symm

theorem IntegerValue.sum {I : Type*} (S : Finset I) (x : I → ℝ)
    (hx : ∀ i ∈ S, IntegerValue (x i)) : IntegerValue (∑ i ∈ S, x i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using IntegerValue.zero
  | @insert a S ha ih =>
    obtain ⟨z, hz⟩ := hx a (mem_insert_self a S)
    obtain ⟨w, hw⟩ := ih (fun i hi => hx i (mem_insert_of_mem hi))
    refine ⟨z + w, ?_⟩
    rw [sum_insert ha, hz, hw, Int.cast_add]

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- The half-divergence discrepancy of two integral representations is
integral. This proves the parity fact by its explicit difference-flow witness. -/
theorem integer_comparison_discrepancy (G H : WeightedDiGraph V)
    (htot : ∀ u v, G.c u v + G.c v u = H.c u v + H.c v u)
    (hG : ∀ u v, IntegerValue (G.c u v))
    (hH : ∀ u v, IntegerValue (H.c u v)) (v : V) :
    IntegerValue ((capacityDiv G v - capacityDiv H v) / 2) := by
  rw [← comparison_divergence G H htot v]
  exact IntegerValue.sum univ (fun w => G.c v w - H.c v w)
    (fun w _ => (hG v w).sub (hH v w))

omit [DecidableEq V] in
/-- An integer row sum cannot have exactly one noninteger summand. This is
the local obstruction to a leaf in the fractional support of a circulation. -/
theorem fractional_neighbor (f : V → V → ℝ)
    (hdiv : ∀ u, IntegerValue (netOut f u)) {u v : V}
    (hfrac : ¬ IntegerValue (f u v)) :
    ∃ w, w ≠ v ∧ ¬ IntegerValue (f u w) := by
  classical
  by_contra! h
  have hrow := IntegerValue.sum (univ.erase v) (f u)
    (fun w hw => h w (mem_erase.mp hw).1)
  obtain ⟨a, ha⟩ := hdiv u
  obtain ⟨b, hb⟩ := hrow
  apply hfrac
  refine ⟨a - b, ?_⟩
  have hsum := sum_erase_add (univ : Finset V) (f u) (mem_univ v)
  change (∑ w, f u w) = (a : ℝ) at ha
  rw [Int.cast_sub]
  linarith

omit [DecidableEq V] in
/-- In an antisymmetric circulation the second fractional neighbor is also
different from the row vertex; a diagonal cannot be fractional. -/
theorem fractional_two_neighbors (f : V → V → ℝ) (hf : IsFlow f)
    (hdiv : ∀ u, IntegerValue (netOut f u)) {u v : V}
    (hfrac : ¬ IntegerValue (f u v)) :
    u ≠ v ∧ ∃ w, w ≠ u ∧ w ≠ v ∧ ¬ IntegerValue (f u w) := by
  have hne : u ≠ v := by
    intro h
    subst v
    exact hfrac (by rw [hf.self]; exact IntegerValue.zero)
  obtain ⟨w, hwv, hw⟩ := fractional_neighbor f hdiv hfrac
  refine ⟨hne, w, ?_, hwv, hw⟩
  intro h
  subst w
  exact hw (by rw [hf.self]; exact IntegerValue.zero)

/-- The undirected support of nonintegral signed coordinates. Antisymmetry
ensures that either both directions are integral or neither is. -/
def fractionalGraph (f : V → V → ℝ) (hf : IsFlow f) : SimpleGraph V where
  Adj u v := ¬ IntegerValue (f u v)
  symm := ⟨by
    intro u v huv hvu
    apply huv
    rw [hf v u]
    exact hvu.neg⟩
  loopless := ⟨by
    intro v h
    apply h
    rw [hf.self]
    exact IntegerValue.zero⟩

omit [DecidableEq V] in
/-- Any fractional coordinate in a finite flow of integer divergence lies
in a component containing a fractional cycle. If that component were a
tree, its degree-one vertex would contradict the no-fractional-leaf lemma.
The cycle is constructed without an integrality or rounding oracle. -/
theorem fractional_support_cycle (f : V → V → ℝ) (hf : IsFlow f)
    (hdiv : ∀ u, IntegerValue (netOut f u)) {u v : V}
    (hfrac : ¬ IntegerValue (f u v)) :
    ∃ (w : V) (p : (fractionalGraph f hf).Walk w w), p.IsCycle := by
  classical
  let G := fractionalGraph f hf
  by_contra! hcycle
  have hacyclic : G.IsAcyclic := by
    intro w p
    exact hcycle w p
  let C := G.connectedComponentMk u
  have hu : u ∈ C.supp := rfl
  have huv : G.Adj u v := hfrac
  have hv : v ∈ C.supp := C.mem_supp_of_adj_mem_supp hu huv
  letI : Fintype C := Fintype.ofFinite C
  letI : Nontrivial C := ⟨⟨⟨u, hu⟩, ⟨v, hv⟩, by
    intro h
    exact huv.ne (congrArg Subtype.val h)⟩⟩
  obtain ⟨w, hw⟩ := (hacyclic.isTree_connectedComponent C).exists_vert_degree_one_of_nontrivial
  obtain ⟨x, hx, hunique⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hw
  have hxfrac : ¬ IntegerValue (f w.val x.val) := hx
  obtain ⟨z, hzx, hz⟩ := fractional_neighbor f hdiv hxfrac
  have hzadj : G.Adj w.val z := hz
  have hzmem : z ∈ C.supp := C.mem_supp_of_adj_mem_supp w.property hzadj
  have hzsub : C.toSimpleGraph.Adj w ⟨z, hzmem⟩ := hzadj
  exact hzx (congrArg Subtype.val (hunique ⟨z, hzmem⟩ hzsub))

omit [DecidableEq V] in
/-- A nonintegral flow of integer divergence admits a nonzero conserving
signed-unit direction supported entirely on nonintegral coordinates. -/
theorem fractional_circulation_direction (f : V → V → ℝ) (hf : IsFlow f)
    (hdiv : ∀ u, IntegerValue (netOut f u)) {u v : V}
    (hfrac : ¬ IntegerValue (f u v)) :
    ∃ z : V → V → ℝ, IsFlow z ∧ (∀ a, netOut z a = 0) ∧
      (∀ a b, z a b = -1 ∨ z a b = 0 ∨ z a b = 1) ∧
      (∀ a b, z a b ≠ 0 → ¬ IntegerValue (f a b)) ∧ ∃ a b, z a b = 1 := by
  classical
  obtain ⟨w, p, hp⟩ := fractional_support_cycle f hf hdiv hfrac
  exact cycle_circulation_direction p hp

/-- Ordered coordinates that are still nonintegral. Both directions of each
fractional pair occur, which is harmless for the decreasing natural measure. -/
noncomputable def fractionalSupport (f : V → V → ℝ) : Finset (V × V) := by
  classical
  exact univ.filter fun e => ¬ IntegerValue (f e.1 e.2)

omit [DecidableEq V] in
/-- A fractional cycle can be adjusted until one coordinate reaches an
integer boundary. No previously integral coordinate moves, divergence is
preserved, and the finite fractional support strictly decreases. -/
theorem fractional_bounded_step (lo hi : V → V → ℤ) (f : V → V → ℝ)
    (hf : IsFlow f) (hdiv : ∀ u, IntegerValue (netOut f u))
    (hbounds : ∀ u v, (lo u v : ℝ) ≤ f u v ∧ f u v ≤ (hi u v : ℝ))
    {u v : V} (hfrac : ¬ IntegerValue (f u v)) :
    ∃ g : V → V → ℝ, IsFlow g ∧ (∀ a, netOut g a = netOut f a) ∧
      (∀ a b, (lo a b : ℝ) ≤ g a b ∧ g a b ≤ (hi a b : ℝ)) ∧
      fractionalSupport g ⊂ fractionalSupport f := by
  classical
  obtain ⟨z, hzflow, hzdiv, hzvalues, hzfrac, a, b, hab⟩ :=
    fractional_circulation_direction f hf hdiv hfrac
  let S : Finset (V × V) := univ.filter fun e => z e.1 e.2 ≠ 0
  have hS : S.Nonempty := ⟨(a, b), by simp [S, hab]⟩
  let slack := fun e : V × V =>
    if z e.1 e.2 = 1 then (hi e.1 e.2 : ℝ) - f e.1 e.2
    else f e.1 e.2 - (lo e.1 e.2 : ℝ)
  have hpositive (e : V × V) (he : e ∈ S) : 0 < slack e := by
    have hne : z e.1 e.2 ≠ 0 := (mem_filter.mp he).2
    have hn := hzfrac e.1 e.2 hne
    have hbd := hbounds e.1 e.2
    have hl : (lo e.1 e.2 : ℝ) < f e.1 e.2 := by
      by_contra h
      exact hn ⟨lo e.1 e.2, le_antisymm (le_of_not_gt h) hbd.1⟩
    have hh : f e.1 e.2 < (hi e.1 e.2 : ℝ) := by
      by_contra h
      exact hn ⟨hi e.1 e.2, le_antisymm hbd.2 (le_of_not_gt h)⟩
    dsimp [slack]
    split_ifs <;> linarith
  obtain ⟨e, he, hmin⟩ := S.exists_min_image slack hS
  let eps := slack e
  have heps : 0 < eps := hpositive e he
  let g := fun a b => f a b + eps * z a b
  have hgflow : IsFlow g := by
    intro a b
    dsimp [g]
    rw [hf a b, hzflow a b]
    ring
  have hgdiv (a : V) : netOut g a = netOut f a := by
    simp only [netOut, g, sum_add_distrib, ← mul_sum]
    change netOut f a + eps * netOut z a = netOut f a
    rw [hzdiv, mul_zero, add_zero]
  have hgbounds (a b : V) : (lo a b : ℝ) ≤ g a b ∧ g a b ≤ (hi a b : ℝ) := by
    have hbd := hbounds a b
    by_cases hz : z a b = 0
    · simpa only [g, hz, mul_zero, add_zero] using hbd
    · have hm : eps ≤ slack (a, b) := hmin (a, b) (by simp [S, hz])
      rcases hzvalues a b with hminus | hzero | hplus
      · simp only [slack, hminus] at hm
        norm_num at hm
        dsimp [g]
        rw [hminus]
        constructor <;> nlinarith
      · exact (hz hzero).elim
      · simp only [slack, hplus, ↓reduceIte] at hm
        dsimp [g]
        rw [hplus]
        constructor <;> nlinarith
  have hsub : fractionalSupport g ⊆ fractionalSupport f := by
    intro p hp
    simp only [fractionalSupport, mem_filter, mem_univ, true_and] at hp ⊢
    intro hpf
    have hzero : z p.1 p.2 = 0 := by
      by_contra h
      exact hzfrac p.1 p.2 h hpf
    exact hp (by simpa only [g, hzero, mul_zero, add_zero] using hpf)
  have hez : z e.1 e.2 ≠ 0 := (mem_filter.mp he).2
  have heg : IntegerValue (g e.1 e.2) := by
    rcases hzvalues e.1 e.2 with hminus | hzero | hplus
    · refine ⟨lo e.1 e.2, ?_⟩
      dsimp [g, eps, slack]
      rw [hminus]
      norm_num
    · exact (hez hzero).elim
    · refine ⟨hi e.1 e.2, ?_⟩
      dsimp [g, eps, slack]
      rw [hplus]
      norm_num
  refine ⟨g, hgflow, hgdiv, hgbounds, ?_⟩
  apply ssubset_iff_subset_ne.mpr
  refine ⟨hsub, ?_⟩
  intro heq
  have hef : e ∈ fractionalSupport f := by
    simp only [fractionalSupport, mem_filter, mem_univ, true_and]
    exact hzfrac e.1 e.2 hez
  have heg' : e ∈ fractionalSupport g := heq.symm ▸ hef
  exact (mem_filter.mp heg').2 heg

omit [DecidableEq V] in
/-- Integer divergence and integer arc bounds suffice for an integral
flow with exactly the same divergences. Strong induction on fractional
support proves termination of successive cycle adjustments. -/
theorem bounded_integral_flow (lo hi : V → V → ℤ) (f : V → V → ℝ)
    (hf : IsFlow f) (hdiv : ∀ u, IntegerValue (netOut f u))
    (hbounds : ∀ u v, (lo u v : ℝ) ≤ f u v ∧ f u v ≤ (hi u v : ℝ)) :
    ∃ g : V → V → ℝ, IsFlow g ∧ (∀ a, netOut g a = netOut f a) ∧
      (∀ a b, (lo a b : ℝ) ≤ g a b ∧ g a b ≤ (hi a b : ℝ)) ∧
      ∀ a b, IntegerValue (g a b) := by
  classical
  suffices h : ∀ k : ℕ, ∀ f : V → V → ℝ,
      (fractionalSupport f).card = k → IsFlow f →
      (∀ u, IntegerValue (netOut f u)) →
      (∀ u v, (lo u v : ℝ) ≤ f u v ∧ f u v ≤ (hi u v : ℝ)) →
      ∃ g : V → V → ℝ, IsFlow g ∧ (∀ a, netOut g a = netOut f a) ∧
        (∀ a b, (lo a b : ℝ) ≤ g a b ∧ g a b ≤ (hi a b : ℝ)) ∧
        ∀ a b, IntegerValue (g a b) by
    exact h _ f rfl hf hdiv hbounds
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro f hk hf hdiv hbounds
    by_cases hint : ∀ a b, IntegerValue (f a b)
    · exact ⟨f, hf, fun _ => rfl, hbounds, hint⟩
    · push Not at hint
      obtain ⟨u, v, huv⟩ := hint
      obtain ⟨g, hgflow, hgdiv, hgbounds, hstrict⟩ :=
        fractional_bounded_step lo hi f hf hdiv hbounds huv
      have hless : (fractionalSupport g).card < k := by
        rw [← hk]
        exact card_lt_card hstrict
      have hgintdiv : ∀ a, IntegerValue (netOut g a) := by
        intro a
        rw [hgdiv]
        exact hdiv a
      obtain ⟨j, hjflow, hjdiv, hjbounds, hjint⟩ :=
        ih _ hless g rfl hgflow hgintdiv hgbounds
      exact ⟨j, hjflow, fun a => (hjdiv a).trans (hgdiv a), hjbounds, hjint⟩

/-- Add one root whose signed incident flow balances each original vertex.
The root is `none`; original vertices are `some v`. -/
def rootExtend (f : V → V → ℝ) : Option V → Option V → ℝ
  | none, none => 0
  | none, some v => netOut f v
  | some u, none => -netOut f u
  | some u, some v => f u v

omit [DecidableEq V] in
theorem rootExtend_isFlow (f : V → V → ℝ) (hf : IsFlow f) : IsFlow (rootExtend f) := by
  intro u v
  cases u <;> cases v <;> simp only [rootExtend, neg_zero, neg_neg]
  exact hf _ _

omit [DecidableEq V] in
theorem rootExtend_conserves (f : V → V → ℝ) (hf : IsFlow f) (u : Option V) :
    netOut (rootExtend f) u = 0 := by
  cases u with
  | none =>
    simp only [netOut, Fintype.sum_option, rootExtend, zero_add]
    exact WeightedDiGraph.sum_univ_netOut hf
  | some u =>
    simp only [netOut, Fintype.sum_option, rootExtend]
    change -(netOut f u) + netOut f u = 0
    ring

omit [DecidableEq V] in
/-- Removing the root from any conserving antisymmetric flow identifies the
internal divergence with the root-to-vertex coordinate. -/
theorem root_restriction_divergence (g : Option V → Option V → ℝ) (hg : IsFlow g)
    (hzero : ∀ u, netOut g u = 0) (v : V) :
    netOut (fun u w => g (some u) (some w)) v = g none (some v) := by
  have h := hzero (some v)
  simp only [netOut, Fintype.sum_option] at h
  rw [hg none (some v)] at h
  change (∑ w, g (some v) (some w)) = g none (some v)
  linarith

/-- An already integral coordinate is fixed by its floor/ceiling interval.
In particular, pure unknown pairs need no learned correction. -/
theorem rounding_fixes_integer (x y : ℝ) (hx : IntegerValue x)
    (hlo : (⌊x⌋ : ℝ) ≤ y) (hhi : y ≤ (⌈x⌉ : ℝ)) : y = x := by
  obtain ⟨z, rfl⟩ := hx
  simp only [Int.floor_intCast, Int.ceil_intCast] at hlo hhi
  exact le_antisymm hhi hlo

/-- Floor/ceiling rounding stays inside every original interval with
integer endpoints, including the internal capacity bounds `[0,u]`. -/
theorem rounding_preserves_integer_bounds (x y : ℝ) (lo hi : ℤ)
    (hxlo : (lo : ℝ) ≤ x) (hxhi : x ≤ (hi : ℝ))
    (hylo : (⌊x⌋ : ℝ) ≤ y) (hyhi : y ≤ (⌈x⌉ : ℝ)) :
    (lo : ℝ) ≤ y ∧ y ≤ (hi : ℝ) := by
  have hfloor : (lo : ℝ) ≤ (⌊x⌋ : ℝ) := by exact_mod_cast (Int.le_floor.mpr hxlo)
  have hceil : (⌈x⌉ : ℝ) ≤ (hi : ℝ) := by exact_mod_cast (Int.ceil_le.mpr hxhi)
  exact ⟨hfloor.trans hylo, hyhi.trans hceil⟩

/-- Integer lower/upper rounding bounds imply a coordinate error below one.
The point chosen in the interval need not itself be integral for this bound. -/
theorem rounding_coordinate_error (x y : ℝ)
    (hlo : (⌊x⌋ : ℝ) ≤ y) (hhi : y ≤ (⌈x⌉ : ℝ)) : |y - x| ≤ 1 := by
  have hfloor := Int.lt_floor_add_one x
  have hceil := Int.ceil_lt_add_one x
  rw [abs_le]
  constructor <;> linarith

omit [DecidableEq V] in
/-- The factor two from canonical pair divergence gives the paper's `2n`
rounding error once the root-coordinate bounds have been established. -/
theorem rounding_divergence_l1 (x y : V → ℝ)
    (hlo : ∀ v, (⌊x v⌋ : ℝ) ≤ y v) (hhi : ∀ v, y v ≤ (⌈x v⌉ : ℝ)) :
    l1 (fun v => 2 * (y v - x v)) ≤ 2 * Fintype.card V := by
  unfold l1
  calc
    _ ≤ ∑ _ : V, (2 : ℝ) := by
      apply sum_le_sum
      intro v _
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      linarith [rounding_coordinate_error (x v) (y v) (hlo v) (hhi v)]
    _ = _ := by simp; ring

omit [DecidableEq V] in
/-- Full signed-flow rounding via a root circulation. All coordinates stay
between their original floor and ceiling; already integral coordinates are
fixed. Divergences are rounded within their own floor/ceiling intervals, so
canonical pair divergence changes by at most `2n` in total.

This is an offline mathematical existence theorem, not an outgoing-query
algorithm: discovering the fractional support is handled separately. -/
theorem signed_flow_rounding (f : V → V → ℝ) (hf : IsFlow f) :
    ∃ g : V → V → ℝ, IsFlow g ∧
      (∀ u v, IntegerValue (g u v) ∧ (⌊f u v⌋ : ℝ) ≤ g u v ∧ g u v ≤ (⌈f u v⌉ : ℝ)) ∧
      (∀ u v, IntegerValue (f u v) → g u v = f u v) ∧
      (∀ v, (⌊netOut f v⌋ : ℝ) ≤ netOut g v ∧ netOut g v ≤ (⌈netOut f v⌉ : ℝ)) ∧
      l1 (fun v => 2 * (netOut g v - netOut f v)) ≤ 2 * Fintype.card V := by
  classical
  have hFint (v : Option V) : IntegerValue (netOut (rootExtend f) v) := by
    rw [rootExtend_conserves f hf]
    exact IntegerValue.zero
  obtain ⟨g, hgflow, hgdiv, hgbounds, hgint⟩ :=
    bounded_integral_flow (fun u v => ⌊rootExtend f u v⌋)
      (fun u v => ⌈rootExtend f u v⌉) (rootExtend f)
      (rootExtend_isFlow f hf) hFint (fun u v => ⟨Int.floor_le _, Int.le_ceil _⟩)
  let rounded := fun u v => g (some u) (some v)
  have hroundflow : IsFlow rounded := fun u v => hgflow (some u) (some v)
  have hcoords (u v : V) : IntegerValue (rounded u v) ∧
      (⌊f u v⌋ : ℝ) ≤ rounded u v ∧ rounded u v ≤ (⌈f u v⌉ : ℝ) :=
    ⟨hgint (some u) (some v), hgbounds (some u) (some v)⟩
  have hconserves (v : Option V) : netOut g v = 0 :=
    (hgdiv v).trans (rootExtend_conserves f hf v)
  have hrestriction (v : V) : netOut rounded v = g none (some v) :=
    root_restriction_divergence g hgflow hconserves v
  have hdivbounds (v : V) :
      (⌊netOut f v⌋ : ℝ) ≤ netOut rounded v ∧ netOut rounded v ≤ (⌈netOut f v⌉ : ℝ) := by
    rw [hrestriction]
    exact hgbounds none (some v)
  refine ⟨rounded, hroundflow, hcoords, ?_, hdivbounds, ?_⟩
  · intro u v huv
    exact rounding_fixes_integer (f u v) (rounded u v) huv (hcoords u v).2.1 (hcoords u v).2.2
  · exact rounding_divergence_l1 (netOut f) (netOut rounded)
      (fun v => (hdivbounds v).1) (fun v => (hdivbounds v).2)

/-- An offline selector applied only to the public learned subflow `p`.
Unknown entries of `p` are zero; the hidden integral background is not an
argument to this choice. The root uses `netOut p`, which is also public. -/
noncomputable def learnedRounding (p : V → V → ℝ) (hp : IsFlow p) : V → V → ℝ :=
  Classical.choose (signed_flow_rounding p hp)

omit [DecidableEq V] in
theorem learnedRounding_isFlow (p : V → V → ℝ) (hp : IsFlow p) :
    IsFlow (learnedRounding p hp) :=
  (Classical.choose_spec (signed_flow_rounding p hp)).1

omit [DecidableEq V] in
theorem learnedRounding_integer (p : V → V → ℝ) (hp : IsFlow p) (u v : V) :
    IntegerValue (learnedRounding p hp u v) :=
  ((Classical.choose_spec (signed_flow_rounding p hp)).2.1 u v).1

omit [DecidableEq V] in
theorem learnedRounding_bounds (p : V → V → ℝ) (hp : IsFlow p) (u v : V) :
    (⌊p u v⌋ : ℝ) ≤ learnedRounding p hp u v ∧
      learnedRounding p hp u v ≤ (⌈p u v⌉ : ℝ) :=
  ((Classical.choose_spec (signed_flow_rounding p hp)).2.1 u v).2

omit [DecidableEq V] in
theorem learnedRounding_fixes_integer (p : V → V → ℝ) (hp : IsFlow p)
    (u v : V) (huv : IntegerValue (p u v)) : learnedRounding p hp u v = p u v :=
  (Classical.choose_spec (signed_flow_rounding p hp)).2.2.1 u v huv

/-- The explicit correction supported on the learned mask. -/
noncomputable def learnedCorrection (p : V → V → ℝ) (hp : IsFlow p) (u v : V) : ℝ :=
  learnedRounding p hp u v - p u v

omit [DecidableEq V] in
/-- In particular, unknown zero entries receive no correction. -/
theorem learnedCorrection_zero (p : V → V → ℝ) (hp : IsFlow p)
    (u v : V) (huv : p u v = 0) : learnedCorrection p hp u v = 0 := by
  rw [learnedCorrection, learnedRounding_fixes_integer p hp u v
    (by rw [huv]; exact IntegerValue.zero), sub_self]

omit [DecidableEq V] in
theorem learnedCorrection_isFlow (p : V → V → ℝ) (hp : IsFlow p) :
    IsFlow (learnedCorrection p hp) := by
  have hr := learnedRounding_isFlow p hp
  intro u v
  simp only [learnedCorrection, hr u v, hp u v]
  ring

omit [DecidableEq V] in
/-- The known correction to canonical capacity imbalance has L1 mass at
most `2n`. This uses only learned values, not full hidden-flow divergence. -/
theorem learnedCorrection_divergence_l1 (p : V → V → ℝ) (hp : IsFlow p) :
    l1 (fun v => 2 * netOut (learnedCorrection p hp) v) ≤ 2 * Fintype.card V := by
  have h := (Classical.choose_spec (signed_flow_rounding p hp)).2.2.2.2
  simpa only [learnedCorrection, learnedRounding, netOut, sum_sub_distrib] using h

omit [DecidableEq V] in
/-- The hidden full flow is mentioned only in the correctness proof. An
integral omitted background plus the public rounded entries is integral. -/
theorem learnedCorrection_realized_integer (p f : V → V → ℝ) (hp : IsFlow p)
    (hint : ∀ u v, IntegerValue (f u v - p u v)) (u v : V) :
    IntegerValue (f u v + learnedCorrection p hp u v) := by
  have h := (hint u v).add (learnedRounding_integer p hp u v)
  have heq : f u v + learnedCorrection p hp u v =
      (f u v - p u v) + learnedRounding p hp u v := by
    simp only [learnedCorrection]
    ring
  rw [heq]
  exact h

section Canonical

variable {W : Type*} [LinearOrder W]

/-- Public learned canonical capacities, extended antisymmetrically and
set to zero on every unlearned pair. Only entries with `u < v` are read. -/
def learnedCanonicalSubflow (known : Finset (W × W)) (a : W → W → ℝ)
    (u v : W) : ℝ :=
  if u < v then if (u, v) ∈ known then a u v else 0
  else if v < u then -(if (v, u) ∈ known then a v u else 0) else 0

theorem learnedCanonicalSubflow_isFlow (known : Finset (W × W)) (a : W → W → ℝ) :
    IsFlow (learnedCanonicalSubflow known a) := by
  intro u v
  by_cases huv : u < v
  · have hvu : ¬ v < u := not_lt.mpr huv.le
    simp only [learnedCanonicalSubflow, huv, hvu, ↓reduceIte]
  · by_cases hvu : v < u
    · simp only [learnedCanonicalSubflow, huv, hvu, ↓reduceIte, neg_neg]
    · simp only [learnedCanonicalSubflow, huv, hvu, ↓reduceIte, neg_zero]

/-- Exact learned entries and integral unlearned pairs discharge the
integral-background premise used by the rounding realization. No hidden
capacity is an argument of `learnedCanonicalSubflow`. -/
theorem learnedCanonicalSubflow_background_integer (H : WeightedDiGraph W)
    (known : Finset (W × W)) (a : W → W → ℝ)
    (hpair : ∀ u v, IntegerValue (H.c u v + H.c v u))
    (hknown : ∀ u v, u < v → (u, v) ∈ known → a u v = H.c u v)
    (hunknown : ∀ u v, u < v → (u, v) ∉ known →
      IntegerValue (H.c u v) ∧ IntegerValue (H.c v u)) (u v : W) :
    IntegerValue (H.c u v - learnedCanonicalSubflow known a u v) := by
  by_cases huv : u < v
  · by_cases hk : (u, v) ∈ known
    · simp only [learnedCanonicalSubflow, huv, hk, ↓reduceIte, hknown u v huv hk,
        sub_self]
      exact IntegerValue.zero
    · simpa only [learnedCanonicalSubflow, huv, hk, ↓reduceIte, sub_zero] using
        (hunknown u v huv hk).1
  · by_cases hvu : v < u
    · by_cases hk : (v, u) ∈ known
      · simpa only [learnedCanonicalSubflow, huv, hvu, hk, ↓reduceIte,
          hknown v u hvu hk, sub_neg_eq_add] using hpair u v
      · simpa only [learnedCanonicalSubflow, huv, hvu, hk, ↓reduceIte, neg_zero,
          sub_zero] using (hunknown v u hvu hk).2
    · have heq : u = v := le_antisymm (le_of_not_gt hvu) (le_of_not_gt huv)
      subst v
      simpa only [learnedCanonicalSubflow, lt_self_iff_false, ↓reduceIte,
        H.diag, sub_zero] using IntegerValue.zero

end Canonical

omit [DecidableEq V] in
/-- Adding the public correction preserves nonnegativity whenever the
omitted capacity background is integral. The integer translate of the
floor bound is enough; no hidden value is passed to the selector. -/
theorem learnedCorrection_nonneg (p : V → V → ℝ) (hp : IsFlow p)
    (u v : V) (x : ℝ) (hx : 0 ≤ x) (hint : IntegerValue (x - p u v)) :
    0 ≤ x + learnedCorrection p hp u v := by
  obtain ⟨z, hz⟩ := hint
  have hlo : ((-z : ℤ) : ℝ) ≤ p u v := by
    rw [Int.cast_neg]
    linarith
  have hfloor : ((-z : ℤ) : ℝ) ≤ (⌊p u v⌋ : ℝ) := by
    exact_mod_cast (Int.le_floor.mpr hlo)
  have hround := hfloor.trans (learnedRounding_bounds p hp u v).1
  rw [Int.cast_neg] at hround
  dsimp [learnedCorrection]
  linarith

omit [DecidableEq V] in
/-- An initially zero capacity remains zero. This ensures that all-arc
potential-rise bounds survive the integral rounding step. -/
theorem learnedCorrection_at_zero (p : V → V → ℝ) (hp : IsFlow p)
    (u v : V) (hint : IntegerValue (0 - p u v)) :
    learnedCorrection p hp u v = 0 := by
  have hpint : IntegerValue (p u v) := by
    simpa only [zero_sub, neg_neg] using hint.neg
  rw [learnedCorrection, learnedRounding_fixes_integer p hp u v hpint, sub_self]

/-- The realized rounded capacity graph. `H` and the integral-background
proof occur only in this mathematical realization; the zero-query program
below selects its correction from public `p` alone. -/
noncomputable def roundedRepresentation (H : WeightedDiGraph V)
    (p : V → V → ℝ) (hp : IsFlow p)
    (hint : ∀ u v, IntegerValue (H.c u v - p u v)) : WeightedDiGraph V where
  c u v := H.c u v + learnedCorrection p hp u v
  nonneg u v := learnedCorrection_nonneg p hp u v (H.c u v) (H.nonneg u v) (hint u v)
  diag v := by rw [H.diag, (learnedCorrection_isFlow p hp).self]; simp

omit [DecidableEq V] in
@[simp] theorem roundedRepresentation_c (H : WeightedDiGraph V)
    (p : V → V → ℝ) (hp : IsFlow p)
    (hint : ∀ u v, IntegerValue (H.c u v - p u v)) (u v : V) :
    (roundedRepresentation H p hp hint).c u v = H.c u v + learnedCorrection p hp u v := rfl

omit [DecidableEq V] in
theorem roundedRepresentation_integer (H : WeightedDiGraph V)
    (p : V → V → ℝ) (hp : IsFlow p)
    (hint : ∀ u v, IntegerValue (H.c u v - p u v)) (u v : V) :
    IntegerValue ((roundedRepresentation H p hp hint).c u v) :=
  learnedCorrection_realized_integer p H.c hp hint u v

omit [DecidableEq V] in
theorem roundedRepresentation_natural (H : WeightedDiGraph V)
    (p : V → V → ℝ) (hp : IsFlow p)
    (hint : ∀ u v, IntegerValue (H.c u v - p u v)) (u v : V) :
    ∃ k : ℕ, (roundedRepresentation H p hp hint).c u v = k :=
  (roundedRepresentation_integer H p hp hint u v).exists_nat
    ((roundedRepresentation H p hp hint).nonneg u v)

omit [DecidableEq V] in
theorem roundedRepresentation_pair_sum (H : WeightedDiGraph V)
    (p : V → V → ℝ) (hp : IsFlow p)
    (hint : ∀ u v, IntegerValue (H.c u v - p u v)) (u v : V) :
    (roundedRepresentation H p hp hint).c u v +
      (roundedRepresentation H p hp hint).c v u = H.c u v + H.c v u := by
  simp only [roundedRepresentation_c, (learnedCorrection_isFlow p hp) u v]
  ring

omit [DecidableEq V] in
theorem roundedRepresentation_pairBounded (H : WeightedDiGraph V)
    (p : V → V → ℝ) (hp : IsFlow p)
    (hint : ∀ u v, IntegerValue (H.c u v - p u v)) (hH : PairBounded H) :
    PairBounded (roundedRepresentation H p hp hint) := by
  intro u v
  rw [roundedRepresentation_pair_sum]
  exact hH u v

omit [DecidableEq V] in
theorem roundedRepresentation_zero (H : WeightedDiGraph V)
    (p : V → V → ℝ) (hp : IsFlow p)
    (hint : ∀ u v, IntegerValue (H.c u v - p u v)) (u v : V) (hz : H.c u v = 0) :
    (roundedRepresentation H p hp hint).c u v = 0 := by
  have hzero : IntegerValue (0 - p u v) := by simpa only [hz] using hint u v
  rw [roundedRepresentation_c, hz, learnedCorrection_at_zero p hp u v hzero, add_zero]

omit [DecidableEq V] in
/-- Every positive rounded arc was already positive before rounding. -/
theorem roundedRepresentation_positive (H : WeightedDiGraph V)
    (p : V → V → ℝ) (hp : IsFlow p)
    (hint : ∀ u v, IntegerValue (H.c u v - p u v)) (u v : V)
    (hpos : 0 < (roundedRepresentation H p hp hint).c u v) : 0 < H.c u v := by
  by_contra h
  have hz : H.c u v = 0 := le_antisymm (le_of_not_gt h) (H.nonneg u v)
  rw [roundedRepresentation_zero H p hp hint u v hz] at hpos
  exact (lt_irrefl 0) hpos

omit [DecidableEq V] in
/-- Transfer the rise bound for all positive arcs, before running repair. -/
theorem roundedRepresentation_rise (H : WeightedDiGraph V)
    (p : V → V → ℝ) (hp : IsFlow p)
    (hint : ∀ u v, IntegerValue (H.c u v - p u v)) (r : V → ℝ) (L : ℝ)
    (hrise : ∀ u v, 0 < H.c u v → r v - r u ≤ L) :
    ∀ u v, 0 < (roundedRepresentation H p hp hint).c u v → r v - r u ≤ L := by
  intro u v huv
  exact hrise u v (roundedRepresentation_positive H p hp hint u v huv)

omit [DecidableEq V] in
/-- The new represented divergence is computable from measured old
divergence plus the public correction. Hidden canonical divergence is not
needed by the rounding program. -/
theorem roundedRepresentation_capacityDiv (H : WeightedDiGraph V)
    (p : V → V → ℝ) (hp : IsFlow p)
    (hint : ∀ u v, IntegerValue (H.c u v - p u v)) (v : V) :
    capacityDiv (roundedRepresentation H p hp hint) v =
      capacityDiv H v + 2 * netOut (learnedCorrection p hp) v := by
  simp only [capacityDiv, roundedRepresentation_c,
    (learnedCorrection_isFlow p hp) v, netOut, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro w _
  ring

/-- A zero-query correction selected only from the public learned subflow.
The adapter lives here so residual search has no rounding dependency. -/
noncomputable def learnedRoundingProg {W : Type} [Fintype W]
    (p : W → W → ℝ) (hp : IsFlow p) : Prog (Finset W) ℝ (W → W → ℝ) :=
  .pure (learnedCorrection p hp)

@[simp] theorem learnedRoundingProg_eval {W : Type} [Fintype W]
    (read : Finset W → ℝ) (p : W → W → ℝ) (hp : IsFlow p) :
    (learnedRoundingProg p hp).eval read = learnedCorrection p hp := rfl

@[simp] theorem learnedRoundingProg_cost {W : Type} [Fintype W]
    (read : Finset W → ℝ) (p : W → W → ℝ) (hp : IsFlow p) :
    (learnedRoundingProg p hp).cost read = 0 := rfl

end CutQueryComplexity.DirectedUnitST.Repair

#print axioms CutQueryComplexity.DirectedUnitST.Repair.fractional_two_neighbors
#print axioms CutQueryComplexity.DirectedUnitST.Repair.fractional_support_cycle
#print axioms CutQueryComplexity.DirectedUnitST.Repair.fractional_circulation_direction
#print axioms CutQueryComplexity.DirectedUnitST.Repair.fractional_bounded_step
#print axioms CutQueryComplexity.DirectedUnitST.Repair.bounded_integral_flow
#print axioms CutQueryComplexity.DirectedUnitST.Repair.integer_comparison_discrepancy
#print axioms CutQueryComplexity.DirectedUnitST.Repair.rootExtend_conserves
#print axioms CutQueryComplexity.DirectedUnitST.Repair.root_restriction_divergence
#print axioms CutQueryComplexity.DirectedUnitST.Repair.rounding_fixes_integer
#print axioms CutQueryComplexity.DirectedUnitST.Repair.rounding_preserves_integer_bounds
#print axioms CutQueryComplexity.DirectedUnitST.Repair.rounding_divergence_l1
#print axioms CutQueryComplexity.DirectedUnitST.Repair.signed_flow_rounding
#print axioms CutQueryComplexity.DirectedUnitST.Repair.learnedCorrection_zero
#print axioms CutQueryComplexity.DirectedUnitST.Repair.learnedCorrection_divergence_l1
#print axioms CutQueryComplexity.DirectedUnitST.Repair.learnedCorrection_realized_integer
#print axioms CutQueryComplexity.DirectedUnitST.Repair.learnedCanonicalSubflow_background_integer
#print axioms CutQueryComplexity.DirectedUnitST.Repair.roundedRepresentation_integer
#print axioms CutQueryComplexity.DirectedUnitST.Repair.roundedRepresentation_pair_sum
#print axioms CutQueryComplexity.DirectedUnitST.Repair.roundedRepresentation_positive
#print axioms CutQueryComplexity.DirectedUnitST.Repair.roundedRepresentation_capacityDiv
