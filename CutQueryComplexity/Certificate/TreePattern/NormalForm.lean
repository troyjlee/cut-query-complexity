import CutQueryComplexity.Certificate.TreePattern.Verify
import Mathlib.Topology.Instances.Int

/-!
# Existence of the public tree normal form

The proof uses an actual minimum-cost feasible flow and finite residual
walks. It does not assume LP duality or an oracle choosing a successful tree.
-/

set_option autoImplicit false

namespace CutQueryComplexity.Certificate.TreePattern

open Finset Filter _root_.SimpleGraph
open scoped Classical Topology
noncomputable section

variable {n : ℕ}

/-- Directed walks retain the orientation of every residual arc. -/
inductive DirectedWalk (R : Fin n → Fin n → Prop) : Fin n → Fin n → Type
  | nil {u : Fin n} : DirectedWalk R u u
  | cons {u v w : Fin n} (h : R u v) (p : DirectedWalk R v w) : DirectedWalk R u w

namespace DirectedWalk

variable {R : Fin n → Fin n → Prop}

def length {u v : Fin n} : DirectedWalk R u v → ℕ
  | .nil => 0
  | .cons _ p => p.length + 1

def support {u v : Fin n} : DirectedWalk R u v → List (Fin n)
  | .nil => [u]
  | .cons _ p => u :: p.support

def cost {u v : Fin n} : DirectedWalk R u v → ℤ
  | .nil => 0
  | @cons _ _ u v _ _ p => publicCost u v + p.cost

def flow {u v : Fin n} : DirectedWalk R u v → Fin n → Fin n → ℝ
  | .nil => fun _ _ => 0
  | @cons _ _ u v _ _ p => fun a b => arc u v a b + p.flow a b

def append {u v w : Fin n} : DirectedWalk R u v → DirectedWalk R v w → DirectedWalk R u w
  | .nil, q => q
  | .cons h p, q => .cons h (p.append q)

@[simp] theorem support_length {u v : Fin n} (p : DirectedWalk R u v) :
    p.support.length = p.length + 1 := by
  induction p <;> simp [support, length, *]

@[simp] theorem cost_append {u v w : Fin n} (p : DirectedWalk R u v) (q : DirectedWalk R v w) :
    (p.append q).cost = p.cost + q.cost := by
  induction p <;> simp [append, cost, *, add_assoc]

theorem suffix_support_sublist {u v w : Fin n} (p : DirectedWalk R u v) (q : DirectedWalk R v w) :
    q.support.Sublist (p.append q).support := by
  induction p with
  | nil => exact List.Sublist.refl _
  | cons h p ih => exact (ih q).cons _

theorem split_mem {u v x : Fin n} (p : DirectedWalk R u v) (hx : x ∈ p.support) :
    ∃ q : DirectedWalk R u x, ∃ r : DirectedWalk R x v, p = q.append r := by
  induction p with
  | @nil a =>
      have hxu : x = a := by simpa [support] using hx
      subst x
      exact ⟨.nil, .nil, rfl⟩
  | @cons u v w h p ih =>
      simp only [support, List.mem_cons] at hx
      rcases hx with hx | hx
      · subst x
        exact ⟨.nil, .cons h p, rfl⟩
      · obtain ⟨q, r, heq⟩ := ih hx
        exact ⟨.cons h q, r, by rw [heq]; rfl⟩

theorem isFlow {u v : Fin n} (p : DirectedWalk R u v) : IsFlow p.flow := by
  induction p with
  | nil => intro a b; simp [flow]
  | @cons u v w h p ih =>
      intro a b
      change arc u v b a + p.flow b a = -(arc u v a b + p.flow a b)
      rw [isFlow_arc u v a b, ih a b]
      ring

theorem flow_pos {u v : Fin n} (p : DirectedWalk R u v) (a b : Fin n)
    (h : 0 < p.flow a b) : R a b := by
  induction p with
  | nil => simp [flow] at h
  | @cons u v w huv p ih =>
      change 0 < arc u v a b + p.flow a b at h
      by_cases ha : 0 < arc u v a b
      · obtain ⟨rfl, rfl⟩ := arc_pos ha
        exact huv
      · exact ih (by linarith)

theorem netOut_flow {u v : Fin n} (p : DirectedWalk R u v) (x : Fin n) :
    netOut p.flow x = (if x = u then 1 else 0) - (if x = v then 1 else 0) := by
  induction p with
  | nil => simp [flow, netOut]
  | @cons u v w h p ih =>
      rw [flow, netOut_add, netOut_arc, ih]
      ring

/-- Removing closed subwalks cannot increase cost when all closed walks
have nonnegative cost. The resulting path has distinct vertices. -/
theorem exists_simple_le (hcycles : ∀ u, ∀ p : DirectedWalk R u u, 0 ≤ p.cost)
    {u v : Fin n} (p : DirectedWalk R u v) :
    ∃ q : DirectedWalk R u v, q.support.Nodup ∧ q.cost ≤ p.cost := by
  induction p with
  | nil => exact ⟨.nil, by simp [support], le_rfl⟩
  | @cons u v w h p ih =>
      obtain ⟨q, hq, hle⟩ := ih
      by_cases hu : u ∈ q.support
      · obtain ⟨a, b, heq⟩ := q.split_mem hu
        have hb : b.support.Nodup := by
          rw [heq] at hq
          exact hq.sublist (a.suffix_support_sublist b)
        have hloop := hcycles u (.cons h a)
        have hsum : q.cost = a.cost + b.cost := by rw [heq, cost_append]
        refine ⟨b, hb, ?_⟩
        change b.cost ≤ publicCost u v + p.cost
        change 0 ≤ publicCost u v + a.cost at hloop
        omega
      · refine ⟨.cons h q, ?_, ?_⟩
        · simpa [support] using (List.nodup_cons.mpr ⟨hu, hq⟩)
        · change publicCost u v + q.cost ≤ publicCost u v + p.cost
          omega

end DirectedWalk

/-- A finite public bound used only to choose minimum-cost simple walks. -/
def totalCostMagnitude (n : ℕ) : ℤ := ∑ u : Fin n, ∑ v : Fin n, |publicCost u v|

theorem totalCostMagnitude_nonneg (n : ℕ) : 0 ≤ totalCostMagnitude n := by
  exact sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _

theorem abs_publicCost_le_total (u v : Fin n) : |publicCost u v| ≤ totalCostMagnitude n := by
  have h1 : |publicCost u v| ≤ ∑ w : Fin n, |publicCost u w| :=
    single_le_sum (f := fun w : Fin n => |publicCost u w|)
      (fun _ _ => abs_nonneg _) (mem_univ v)
  have h2 : (∑ w : Fin n, |publicCost u w|) ≤ totalCostMagnitude n :=
    single_le_sum (f := fun x : Fin n => ∑ w : Fin n, |publicCost x w|)
      (fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) (mem_univ u)
  exact h1.trans h2

theorem DirectedWalk.abs_cost_le {R : Fin n → Fin n → Prop} {u v : Fin n}
    (p : DirectedWalk R u v) : |p.cost| ≤ (p.length : ℤ) * totalCostMagnitude n := by
  induction p with
  | nil => simp [DirectedWalk.cost, DirectedWalk.length]
  | @cons u v w h p ih =>
      calc
        |publicCost u v + p.cost| ≤ |publicCost u v| + |p.cost| := abs_add_le _ _
        _ ≤ totalCostMagnitude n + (p.length : ℤ) * totalCostMagnitude n :=
          add_le_add (abs_publicCost_le_total u v) ih
        _ = ((DirectedWalk.cons h p).length : ℤ) * totalCostMagnitude n := by
          simp [DirectedWalk.length]
          ring

theorem DirectedWalk.simple_cost_bounds {R : Fin n → Fin n → Prop} {u v : Fin n}
    (p : DirectedWalk R u v) (hp : p.support.Nodup) :
    -(n : ℤ) * totalCostMagnitude n ≤ p.cost ∧ p.cost ≤ (n : ℤ) * totalCostMagnitude n := by
  have hlen : p.length ≤ n := by
    have h := hp.length_le_card
    rw [p.support_length, Fintype.card_fin] at h
    omega
  have hcast : (p.length : ℤ) ≤ n := by exact_mod_cast hlen
  have hb := p.abs_cost_le.trans (mul_le_mul_of_nonneg_right hcast (totalCostMagnitude_nonneg n))
  have ha := abs_le.mp hb
  constructor <;> linarith

def simpleWalkCosts (R : Fin n → Fin n → Prop) (v : Fin n) : Finset ℤ :=
  (Icc (-(n : ℤ) * totalCostMagnitude n) ((n : ℤ) * totalCostMagnitude n)).filter
    fun c => ∃ u, ∃ p : DirectedWalk R u v, p.support.Nodup ∧ p.cost = c

theorem simpleWalkCosts_nonempty (R : Fin n → Fin n → Prop) (v : Fin n) :
    (simpleWalkCosts R v).Nonempty := by
  refine ⟨0, mem_filter.mpr ⟨?_, v, .nil, by simp [DirectedWalk.support], rfl⟩⟩
  have h : 0 ≤ (n : ℤ) * totalCostMagnitude n :=
    mul_nonneg (by positivity) (totalCostMagnitude_nonneg n)
  exact mem_Icc.mpr ⟨by linarith, h⟩

def shortestCost (R : Fin n → Fin n → Prop) (v : Fin n) : ℤ :=
  (simpleWalkCosts R v).min' (simpleWalkCosts_nonempty R v)

theorem shortestCost_realized (R : Fin n → Fin n → Prop) (v : Fin n) :
    ∃ u, ∃ p : DirectedWalk R u v, p.support.Nodup ∧ p.cost = shortestCost R v := by
  exact (mem_filter.mp ((simpleWalkCosts R v).min'_mem (simpleWalkCosts_nonempty R v))).2

theorem shortestCost_le_walk {R : Fin n → Fin n → Prop}
    (hcycles : ∀ u, ∀ p : DirectedWalk R u u, 0 ≤ p.cost)
    {u v : Fin n} (p : DirectedWalk R u v) : shortestCost R v ≤ p.cost := by
  obtain ⟨q, hq, hle⟩ := DirectedWalk.exists_simple_le hcycles p
  have hmem : q.cost ∈ simpleWalkCosts R v :=
    mem_filter.mpr ⟨mem_Icc.mpr (q.simple_cost_bounds hq), u, q, hq, rfl⟩
  exact (min'_le _ _ hmem).trans hle

theorem shortestCost_arc {R : Fin n → Fin n → Prop}
    (hcycles : ∀ u, ∀ p : DirectedWalk R u u, 0 ≤ p.cost)
    {u v : Fin n} (huv : R u v) : shortestCost R v ≤ shortestCost R u + publicCost u v := by
  obtain ⟨r, p, _, hp⟩ := shortestCost_realized R u
  have h := shortestCost_le_walk hcycles (p.append (.cons huv .nil))
  simpa [DirectedWalk.cost_append, DirectedWalk.cost, hp] using h

/-- A real potential satisfying every residual difference constraint,
constructed from a finite minimum over simple walk costs. -/
theorem exists_residual_potential (R : Fin n → Fin n → Prop)
    (hcycles : ∀ u, ∀ p : DirectedWalk R u u, 0 ≤ p.cost) :
    ∃ p : Fin n → ℝ, ∀ u v, R u v → 0 ≤ (publicCost u v : ℝ) - (p u - p v) := by
  refine ⟨fun v => -(shortestCost R v : ℝ), fun u v huv => ?_⟩
  have h : (shortestCost R v : ℝ) ≤ (shortestCost R u : ℝ) + (publicCost u v : ℝ) :=
    by exact_mod_cast shortestCost_arc hcycles huv
  linarith

/-- Twice the usual canonically oriented objective; the harmless factor two
lets the antisymmetric representation use all ordered pairs. -/
def flowObjective (f : Fin n → Fin n → ℝ) : ℝ :=
  ∑ u, ∑ v, (publicCost u v : ℝ) * f u v

theorem flowObjective_add (f g : Fin n → Fin n → ℝ) :
    flowObjective (fun u v => f u v + g u v) = flowObjective f + flowObjective g := by
  simp [flowObjective, mul_add, sum_add_distrib]

theorem flowObjective_smul (a : ℝ) (f : Fin n → Fin n → ℝ) :
    flowObjective (fun u v => a * f u v) = a * flowObjective f := by
  unfold flowObjective
  rw [mul_sum]
  apply sum_congr rfl
  intro u _
  rw [mul_sum]
  apply sum_congr rfl
  intro v _
  ring

theorem flowObjective_arc (u v : Fin n) : flowObjective (arc u v) = 2 * (publicCost u v : ℝ) := by
  have heq : flowObjective (arc u v) = (publicCost u v : ℝ) - (publicCost v u : ℝ) := by
    simp [flowObjective, arc, mul_sub, sum_sub_distrib, ite_and, mul_ite]
  rw [heq, publicCost_reverse u v, Int.cast_neg]
  ring

theorem DirectedWalk.flowObjective_flow {R : Fin n → Fin n → Prop} {u v : Fin n}
    (p : DirectedWalk R u v) : flowObjective p.flow = 2 * (p.cost : ℝ) := by
  induction p with
  | nil => simp [DirectedWalk.flow, DirectedWalk.cost, flowObjective]
  | @cons u v w h p ih =>
      rw [DirectedWalk.flow, flowObjective_add, flowObjective_arc, ih, DirectedWalk.cost,
        Int.cast_add]
      ring

def FlowFiber (G : WeightedGraph (Fin n)) (b : Fin n → ℝ) : Set (Fin n → Fin n → ℝ) :=
  {f | IsFlow f ∧ (∀ u v, |f u v| ≤ G.w u v) ∧ ∀ v, netOut f v = b v}

theorem isCompact_flowFiber (G : WeightedGraph (Fin n)) (b : Fin n → ℝ) :
    IsCompact (FlowFiber G b) := by
  have hbox : IsCompact (Set.univ.pi fun u : Fin n => Set.univ.pi fun v : Fin n =>
      Set.Icc (-G.w u v) (G.w u v)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  refine hbox.of_isClosed_subset ?_ ?_
  · have hev : ∀ u v : Fin n, Continuous fun f : Fin n → Fin n → ℝ => f u v :=
      fun _ _ => by fun_prop
    simp only [FlowFiber, IsFlow, Set.ofPred_and, Set.ofPred_forall]
    refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_)
    · exact isClosed_iInter fun u => isClosed_iInter fun v =>
        isClosed_eq (hev v u) (hev u v).neg
    · exact isClosed_iInter fun u => isClosed_iInter fun v =>
        isClosed_le (hev u v).abs continuous_const
    · exact isClosed_iInter fun v => isClosed_eq (continuous_netOut v) continuous_const
  · intro f hf
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies]
    exact fun u v => abs_le.mp (hf.2.1 u v)

theorem exists_minCost_flow (G : WeightedGraph (Fin n)) (b : Fin n → ℝ)
    (hfeas : ∃ f, Feasible G f ∧ ∀ v, netOut f v = b v) :
    ∃ f, Feasible G f ∧ (∀ v, netOut f v = b v) ∧
      ∀ g, Feasible G g → (∀ v, netOut g v = b v) → flowObjective f ≤ flowObjective g := by
  obtain ⟨f₀, hf₀, hdiv₀⟩ := hfeas
  have hne : (FlowFiber G b).Nonempty := ⟨f₀, hf₀.1, hf₀.2, hdiv₀⟩
  have hcont : Continuous (flowObjective (n := n)) := by
    unfold flowObjective
    fun_prop
  obtain ⟨f, hf, hmin⟩ := (isCompact_flowFiber G b).exists_isMinOn hne hcont.continuousOn
  exact ⟨f, ⟨hf.1, hf.2.1⟩, hf.2.2, fun g hg hd => hmin ⟨hg.1, hg.2, hd⟩⟩

/-- Negative-cost closed residual walks contradict the actual compact minimum. -/
theorem minCost_closedWalk_nonneg (G : WeightedGraph (Fin n)) (b : Fin n → ℝ)
    {f : Fin n → Fin n → ℝ} (hf : Feasible G f) (hd : ∀ v, netOut f v = b v)
    (hmin : ∀ g, Feasible G g → (∀ v, netOut g v = b v) → flowObjective f ≤ flowObjective g)
    (u : Fin n) (p : DirectedWalk (fun u v => f u v < G.w u v) u u) : 0 ≤ p.cost := by
  by_contra hnonneg
  have hcost : (p.cost : ℝ) < 0 := by exact_mod_cast (lt_of_not_ge hnonneg)
  have hev := (eventually_feasible_add hf p.isFlow p.flow_pos).and
    (self_mem_nhdsWithin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε)
  obtain ⟨ε, hεf, hε⟩ := hev.exists
  let g := fun u v => f u v + ε * p.flow u v
  have hg : Feasible G g := by
    refine ⟨fun u v => ?_, hεf⟩
    dsimp [g]
    rw [hf.1 u v, p.isFlow u v]
    ring
  have hgd : ∀ v, netOut g v = b v := by
    intro v
    rw [netOut_add, netOut_smul, p.netOut_flow, sub_self, mul_zero, add_zero, hd]
  have h := hmin g hg hgd
  change flowObjective f ≤ flowObjective (fun u v => f u v + ε * p.flow u v) at h
  rw [flowObjective_add, flowObjective_smul, p.flowObjective_flow] at h
  have hprod : ε * (p.cost : ℝ) < 0 := mul_neg_of_pos_of_neg hε hcost
  nlinarith [hprod]

def realReduced (p : Fin n → ℝ) (u v : Fin n) : ℝ :=
  (publicCost u v : ℝ) - (p u - p v)

theorem realReduced_reverse (p : Fin n → ℝ) (u v : Fin n) :
    realReduced p v u = -realReduced p u v := by
  unfold realReduced
  rw [publicCost_reverse, Int.cast_neg]
  ring

def Complementary (G : WeightedGraph (Fin n)) (f : Fin n → Fin n → ℝ) (p : Fin n → ℝ) : Prop :=
  ∀ u v, (0 < realReduced p u v → f u v = -G.w u v) ∧
    (realReduced p u v < 0 → f u v = G.w u v)

theorem complementary_of_residual_potential (G : WeightedGraph (Fin n))
    {f : Fin n → Fin n → ℝ} (hf : Feasible G f) (p : Fin n → ℝ)
    (hp : ∀ u v, f u v < G.w u v → 0 ≤ realReduced p u v) : Complementary G f p := by
  have hneg : ∀ u v, realReduced p u v < 0 → f u v = G.w u v := by
    intro u v hr
    apply le_antisymm (hf.le u v)
    by_contra hw
    have hres : f u v < G.w u v := lt_of_not_ge hw
    exact (not_lt_of_ge (hp u v hres)) hr
  intro u v
  refine ⟨fun hr => ?_, hneg u v⟩
  have hrev : realReduced p v u < 0 := by rw [realReduced_reverse]; linarith
  have h := hneg v u hrev
  rw [hf.1 u v, G.symm v u] at h
  linarith

/-- Both objects are constructed: a real feasible minimum-cost flow and a
compatible residual potential. No dual optimizer is assumed. -/
theorem exists_flow_complementary_potential (G : WeightedGraph (Fin n)) (b : Fin n → ℝ)
    (hfeas : ∃ f, Feasible G f ∧ ∀ v, netOut f v = b v) :
    ∃ f, ∃ p : Fin n → ℝ, Feasible G f ∧ (∀ v, netOut f v = b v) ∧ Complementary G f p := by
  obtain ⟨f, hf, hd, hmin⟩ := exists_minCost_flow G b hfeas
  obtain ⟨p, hp⟩ := exists_residual_potential (fun u v => f u v < G.w u v)
    (minCost_closedWalk_nonneg G b hf hd hmin)
  exact ⟨f, p, hf, hd, complementary_of_residual_potential G hf p hp⟩

/-- Moving toward an arrangement boundary may turn signs into zero but
never changes a nonzero sign to its opposite. -/
def SignRefines (p q : Fin n → ℝ) : Prop :=
  ∀ u v, (0 < realReduced q u v → 0 < realReduced p u v) ∧
    (realReduced q u v < 0 → realReduced p u v < 0)

theorem SignRefines.refl (p : Fin n → ℝ) : SignRefines p p :=
  fun _ _ => ⟨id, id⟩

theorem SignRefines.trans {p q r : Fin n → ℝ} (hpq : SignRefines p q) (hqr : SignRefines q r) :
    SignRefines p r := fun u v =>
  ⟨fun h => (hpq u v).1 ((hqr u v).1 h), fun h => (hpq u v).2 ((hqr u v).2 h)⟩

theorem SignRefines.zeroGraph_le {p q : Fin n → ℝ} (h : SignRefines p q) :
    zeroGraph p ≤ zeroGraph q := by
  intro u v huv
  refine ⟨huv.1, ?_⟩
  have hp : realReduced p u v = 0 := by simp [realReduced, huv.2]
  have hq : realReduced q u v = 0 := by
    rcases lt_trichotomy (realReduced q u v) 0 with hn | hz | hp'
    · have := (h u v).2 hn
      rw [hp] at this
      exact (lt_irrefl _ this).elim
    · exact hz
    · have := (h u v).1 hp'
      rw [hp] at this
      exact (lt_irrefl _ this).elim
  exact sub_eq_zero.mp hq

theorem sub_sign_refines {x t : ℝ} (h : |t| ≤ |x|) :
    (0 < x - t → 0 < x) ∧ (x - t < 0 → x < 0) := by
  constructor
  · intro hx
    by_contra hn
    have hxn : x ≤ 0 := le_of_not_gt hn
    rw [abs_of_nonpos hxn] at h
    have ht := neg_abs_le t
    linarith
  · intro hx
    by_contra hn
    have hxn : 0 ≤ x := le_of_not_gt hn
    rw [abs_of_nonneg hxn] at h
    have ht := le_abs_self t
    linarith

def shiftedPotential (p : Fin n → ℝ) (A : Finset (Fin n)) (t : ℝ) (v : Fin n) : ℝ :=
  p v + if v ∈ A then t else 0

theorem realReduced_shift (p : Fin n → ℝ) (A : Finset (Fin n)) (t : ℝ) (u v : Fin n) :
    realReduced (shiftedPotential p A t) u v = realReduced p u v -
      ((if u ∈ A then t else 0) - (if v ∈ A then t else 0)) := by
  unfold shiftedPotential realReduced
  ring

/-- Translating one zero-edge component to its first crossing hyperplane
strictly enlarges the zero graph while retaining all nonzero signs. -/
theorem exists_strict_zeroGraph_extension (hn : 2 ≤ n) (p : Fin n → ℝ)
    (hconn : ¬(zeroGraph p).Connected) :
    ∃ q : Fin n → ℝ, SignRefines p q ∧ zeroGraph p < zeroGraph q := by
  letI : Nonempty (Fin n) := ⟨treeRoot hn⟩
  have hnot : ¬∀ u v, (zeroGraph p).Reachable u v := by
    intro h
    exact hconn ⟨h⟩
  push Not at hnot
  obtain ⟨u, v, huv⟩ := hnot
  let A : Finset (Fin n) := univ.filter fun x => (zeroGraph p).Reachable u x
  have hu : u ∈ A := mem_filter.mpr ⟨mem_univ _, .refl u⟩
  have hv : v ∉ A := fun h => huv (mem_filter.mp h).2
  have hcross : ∀ a ∈ A, ∀ b ∈ Aᶜ, realReduced p a b ≠ 0 := by
    intro a ha b hb hz
    have hne : a ≠ b := by
      intro heq
      exact (mem_compl.mp hb) (heq ▸ ha)
    have hadj : (zeroGraph p).Adj a b := ⟨hne, sub_eq_zero.mp hz⟩
    exact (mem_compl.mp hb) (mem_filter.mpr
      ⟨mem_univ _, ((mem_filter.mp ha).2).trans hadj.reachable⟩)
  let P := A ×ˢ Aᶜ
  have hP : P.Nonempty := ⟨(u,v), mem_product.mpr ⟨hu, mem_compl.mpr hv⟩⟩
  obtain ⟨e, he, hmin⟩ := exists_min_image P (fun ab => |realReduced p ab.1 ab.2|) hP
  have heA := (mem_product.mp he).1
  have heB := (mem_product.mp he).2
  let t := realReduced p e.1 e.2
  let q := shiftedPotential p A t
  have habs : ∀ a b, |((if a ∈ A then t else 0) - (if b ∈ A then t else 0))| ≤
      |realReduced p a b| := by
    intro a b
    by_cases ha : a ∈ A <;> by_cases hb : b ∈ A
    · simp [ha, hb]
    · simpa [ha, hb, t] using hmin (a,b) (mem_product.mpr ⟨ha, mem_compl.mpr hb⟩)
    · have hm := hmin (b,a) (mem_product.mpr ⟨hb, mem_compl.mpr ha⟩)
      rw [realReduced_reverse p a b, abs_neg] at hm
      simpa [ha, hb, t] using hm
    · simp [ha, hb]
  have href : SignRefines p q := by
    intro a b
    rw [show realReduced q a b = realReduced p a b -
      ((if a ∈ A then t else 0) - (if b ∈ A then t else 0)) from realReduced_shift p A t a b]
    exact sub_sign_refines (habs a b)
  have hne : e.1 ≠ e.2 := by
    intro h
    exact (mem_compl.mp heB) (h ▸ heA)
  have hnew : (zeroGraph q).Adj e.1 e.2 := by
    refine ⟨hne, ?_⟩
    apply sub_eq_zero.mp
    change realReduced q e.1 e.2 = 0
    rw [realReduced_shift]
    simp [heA, mem_compl.mp heB, t]
  have hold : ¬(zeroGraph p).Adj e.1 e.2 := by
    intro h
    exact hcross e.1 heA e.2 heB (by simp [realReduced, h.2])
  refine ⟨q, href, lt_of_le_of_ne href.zeroGraph_le ?_⟩
  intro heq
  apply hold
  rw [heq]
  exact hnew

theorem realReduced_treePotential (hn : 2 ≤ n) (T : LabelledTree n) (u v : Fin n) :
    realReduced (fun x => (treePotential hn T x : ℝ)) u v = (reducedCost hn T u v : ℝ) := by
  simp [realReduced, reducedCost]

/-- The finite maximum is over actual realized sign refinements. If its
zero forest were disconnected, the explicit component shift would enlarge it. -/
theorem exists_sign_refining_tree (hn : 2 ≤ n) (p : Fin n → ℝ) :
    ∃ T : LabelledTree n, SignRefines p (fun v => (treePotential hn T v : ℝ)) := by
  let S : Finset (SimpleGraph (Fin n)) := univ.filter fun H =>
    ∃ q : Fin n → ℝ, SignRefines p q ∧ zeroGraph q = H
  have hS : S.Nonempty := ⟨zeroGraph p,
    mem_filter.mpr ⟨mem_univ _, p, SignRefines.refl p, rfl⟩⟩
  obtain ⟨H, hH, hmax⟩ := exists_max_image S (fun H => H.edgeFinset.card) hS
  obtain ⟨q, hpq, hqH⟩ := (mem_filter.mp hH).2
  have hconn : (zeroGraph q).Connected := by
    by_contra hnot
    obtain ⟨r, hqr, hlt⟩ := exists_strict_zeroGraph_extension hn q hnot
    have hrS : zeroGraph r ∈ S := mem_filter.mpr
      ⟨mem_univ _, r, hpq.trans hqr, rfl⟩
    have hcard := card_lt_card (SimpleGraph.edgeFinset_strict_mono hlt)
    have hle := hmax (zeroGraph r) hrS
    rw [← hqH] at hle
    omega
  let T : LabelledTree n := ⟨zeroGraph q, ⟨hconn, zeroGraph_isAcyclic q⟩⟩
  have hpot : ∀ v, (treePotential hn T v : ℝ) = q v - q (treeRoot hn) :=
    treePotential_unique hn T q (fun _ _ h => h.2)
  have heq : ∀ u v, realReduced (fun x => (treePotential hn T x : ℝ)) u v = realReduced q u v := by
    intro u v
    change (publicCost u v : ℝ) -
      ((treePotential hn T u : ℝ) - (treePotential hn T v : ℝ)) =
      (publicCost u v : ℝ) - (q u - q v)
    rw [hpot u, hpot v]
    ring
  refine ⟨T, fun u v => ?_⟩
  rw [heq]
  exact hpq u v

/-- For a fixed public tree, the prescribed non-tree values and divergence
determine the entire signed flow uniquely. -/
theorem normalForm_flow_unique (hn : 2 ≤ n) (T : LabelledTree n)
    (G : WeightedGraph (Fin n)) {f g : Fin n → Fin n → ℝ}
    (hf : IsFlow f) (hg : IsFlow g) (hdiv : ∀ v, netOut f v = netOut g v)
    (hoff : ∀ u v, ¬T.val.Adj u v → f u v = nonTreeFlow hn T G u v)
    (hgoff : ∀ u v, ¬T.val.Adj u v → g u v = nonTreeFlow hn T G u v) : f = g := by
  have hd : IsFlow (fun u v => f u v - g u v) := by
    intro u v
    change f v u - g v u = -(f u v - g u v)
    rw [hf u v, hg u v]
    ring
  have heq : (fun u v => f u v - g u v) = (fun _ _ => (0 : ℝ)) := by
    apply treeSupported_flow_unique T hd (by intro u v; simp)
    · intro u v huv
      rw [hoff u v huv, hgoff u v huv, sub_self]
    · intro u v _
      rfl
    · intro v
      simp only [netOut, sum_sub_distrib, sum_const_zero]
      change netOut f v - netOut g v = 0
      rw [hdiv v, sub_self]
  funext u v
  exact sub_eq_zero.mp (congrFun (congrFun heq u) v)

/-- Every feasible divergence admits the source's actual normal-form flow.
The flow comes from a compact minimum, and the tree from component shifts. -/
theorem exists_normalForm (hn : 2 ≤ n) (G : WeightedGraph (Fin n)) (b : Fin n → ℝ)
    (hfeas : ∃ f, Feasible G f ∧ ∀ v, netOut f v = b v) :
    ∃ T : LabelledTree n, ∃ f : Fin n → Fin n → ℝ,
      Feasible G f ∧ (∀ v, netOut f v = b v) ∧
      ∀ u v, ¬T.val.Adj u v → f u v = nonTreeFlow hn T G u v := by
  obtain ⟨f, p, hf, hd, hcomp⟩ := exists_flow_complementary_potential G b hfeas
  obtain ⟨T, href⟩ := exists_sign_refining_tree hn p
  refine ⟨T, f, hf, hd, fun u v hnot => ?_⟩
  by_cases huv : u = v
  · subst v
    rw [hf.1.self]
    simp [nonTreeFlow, G.diag]
  · have hne : reducedCost hn T u v ≠ 0 :=
      fun h => hnot ((reducedCost_eq_zero_iff hn T huv).mp h)
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have hr : realReduced (fun x => (treePotential hn T x : ℝ)) u v < 0 := by
        rw [realReduced_treePotential]
        exact_mod_cast hneg
      rw [(hcomp u v).2 ((href u v).2 hr)]
      simp [nonTreeFlow, hnot, hneg]
    · have hr : 0 < realReduced (fun x => (treePotential hn T x : ℝ)) u v := by
        rw [realReduced_treePotential]
        exact_mod_cast hpos
      rw [(hcomp u v).1 ((href u v).1 hr)]
      simp [nonTreeFlow, hnot, not_lt.mpr hpos.le]

/-- The constructed normal form passes the same public query verifier. -/
theorem exists_accepting_tree (hn : 2 ≤ n) (G : WeightedGraph (Fin n)) (b : Fin n → ℝ)
    (hfeas : ∃ f, Feasible G f ∧ ∀ v, netOut f v = b v) :
    ∃ T : LabelledTree n, accepts hn T b G.cut := by
  obtain ⟨T, f, hf, hd, hoff⟩ := exists_normalForm hn G b hfeas
  exact ⟨T, accepts_of_normalForm hn T G b hf hd hoff⟩

end
end CutQueryComplexity.Certificate.TreePattern

#print axioms CutQueryComplexity.Certificate.TreePattern.DirectedWalk.exists_simple_le
#print axioms CutQueryComplexity.Certificate.TreePattern.shortestCost_realized
#print axioms CutQueryComplexity.Certificate.TreePattern.shortestCost_arc
#print axioms CutQueryComplexity.Certificate.TreePattern.exists_residual_potential
#print axioms CutQueryComplexity.Certificate.TreePattern.exists_minCost_flow
#print axioms CutQueryComplexity.Certificate.TreePattern.minCost_closedWalk_nonneg
#print axioms CutQueryComplexity.Certificate.TreePattern.exists_flow_complementary_potential
#print axioms CutQueryComplexity.Certificate.TreePattern.exists_strict_zeroGraph_extension
#print axioms CutQueryComplexity.Certificate.TreePattern.exists_sign_refining_tree
#print axioms CutQueryComplexity.Certificate.TreePattern.normalForm_flow_unique
#print axioms CutQueryComplexity.Certificate.TreePattern.exists_normalForm
#print axioms CutQueryComplexity.Certificate.TreePattern.exists_accepting_tree
