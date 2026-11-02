import CutQueryComplexity.CanonicalST.Augmentation.Cycles
import CutQueryComplexity.DirectedCertificate.Flow
import CutQueryComplexity.AllPairsAudit.MinimalShore
import CutQueryComplexity.Graph.Integral

/-!
# Actual integral terminal flows and residual augmentation primitives

The existence statements invoke the repository's proved max-flow/min-cut
theorem, followed by circulation deletion and integer rounding. Public
minimum-shore and maximum-flow choices below use the explicit learned graph.
-/

set_option autoImplicit false

namespace CutQueryComplexity.CanonicalST.Augmentation

open Finset Certificate DirectedCertificate
open DirectedUnitST.Repair
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

def capacityCut (c : V → V → ℕ) (S : Finset V) : ℕ := ∑ u ∈ S, ∑ v ∈ Sᶜ, c u v

def naturalDigraph (c : V → V → ℕ) (hdiag : ∀ v, c v v = 0) : WeightedDiGraph V where
  c u v := c u v
  nonneg u v := Nat.cast_nonneg _
  diag v := by simp [hdiag v]

theorem naturalDigraph_out (c : V → V → ℕ) (hdiag : ∀ v, c v v = 0) (S : Finset V) :
    (naturalDigraph c hdiag).out S = (capacityCut c S : ℝ) := by
  simp [naturalDigraph, WeightedDiGraph.out, capacityCut, Nat.cast_sum]

theorem st_divergence {f : V → V → ℝ} (hf : IsFlow f) {s t : V} (hst : s ≠ t)
    (hc : ∀ x, x ≠ s → x ≠ t → netOut f x = 0) :
    ∀ x, netOut f x = (if x = s then netOut f s else 0) -
      (if x = t then netOut f s else 0) := by
  have hfun : ∀ x, netOut f x = (if x = s then netOut f s else 0) +
      (if x = t then netOut f t else 0) := by
    intro x
    by_cases hxs : x = s
    · subst x
      simp [hst]
    · by_cases hxt : x = t
      · subst x
        simp [hxs]
      · simp [hxs, hxt, hc x hxs hxt]
  have hsum : netOut f s + netOut f t = 0 := by
    calc
      netOut f s + netOut f t = ∑ x,
          ((if x = s then netOut f s else 0) + (if x = t then netOut f t else 0)) := by
        simp only [sum_add_distrib, sum_ite_eq', mem_univ, ↓reduceIte]
      _ = ∑ x, netOut f x := sum_congr rfl (fun x _ => (hfun x).symm)
      _ = 0 := WeightedDiGraph.sum_univ_netOut hf
  have ht : netOut f t = -netOut f s := by linarith
  intro x
  rw [hfun x, ht]
  split_ifs <;> ring

/-- A cut lower bound produces a real flow of the exact requested value,
using actual max-flow/min-cut and, if necessary, scaling its maximum flow. -/
theorem exists_flow_of_cut_lower (c : V → V → ℕ) (hdiag : ∀ v, c v v = 0)
    {s t : V} (hst : s ≠ t) {r : ℝ} (hr : 0 ≤ r)
    (hcut : ∀ S : Finset V, s ∈ S → t ∉ S → r ≤ (capacityCut c S : ℝ)) :
    ∃ f : V → V → ℝ, IsFlow f ∧ (∀ u v, f u v ≤ c u v) ∧
      ∀ x, netOut f x = (if x = s then r else 0) - (if x = t then r else 0) := by
  by_cases hr0 : r = 0
  · refine ⟨fun _ _ => 0, fun _ _ => by simp, fun _ _ => Nat.cast_nonneg _, ?_⟩
    intro x
    simp [netOut, hr0]
  · obtain ⟨f, S, hf, hs, ht, hval⟩ := (naturalDigraph c hdiag).exists_maxFlow_minCut hst
    have hrle : r ≤ netOut f s := by
      rw [hval, naturalDigraph_out]
      exact hcut S hs ht
    have hvalpos : 0 < netOut f s := lt_of_lt_of_le (lt_of_le_of_ne hr (Ne.symm hr0)) hrle
    let θ := r / netOut f s
    have hθ0 : 0 ≤ θ := div_nonneg hr hvalpos.le
    have hθ1 : θ ≤ 1 := (div_le_one hvalpos).mpr hrle
    have hθr : θ * netOut f s = r := div_mul_cancel₀ _ hvalpos.ne'
    have hdiv := st_divergence hf.1.1 hst hf.2
    refine ⟨fun u v => θ * f u v, ?_, ?_, ?_⟩
    · intro u v
      change θ * f v u = -(θ * f u v)
      rw [hf.1.1 u v]
      ring
    · intro u v
      have hc : f u v ≤ (c u v : ℝ) := hf.1.2 u v
      calc
        θ * f u v ≤ θ * (c u v : ℝ) := mul_le_mul_of_nonneg_left hc hθ0
        _ ≤ (c u v : ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) (c u v)]
    · intro x
      rw [netOut_smul, hdiv, mul_sub, mul_ite, mul_ite, hθr, mul_zero]

/-- Exact integer divergence makes the preceding actual flow integral,
while simultaneously removing all positive directed cycles. -/
theorem exists_acyclic_integral_of_cut_lower (c : V → V → ℕ)
    (hdiag : ∀ v, c v v = 0) {s t : V} (hst : s ≠ t) {r : ℝ}
    (hr : 0 ≤ r) (hrint : IntegerValue r)
    (hcut : ∀ S : Finset V, s ∈ S → t ∉ S → r ≤ (capacityCut c S : ℝ)) :
    ∃ f : V → V → ℝ, IsFlow f ∧ (∀ u v, f u v ≤ c u v) ∧
      (∀ x, netOut f x = (if x = s then r else 0) - (if x = t then r else 0)) ∧
      (∀ u v, IntegerValue (f u v)) ∧ NoDirectedCycle f := by
  obtain ⟨f, hf, hcap, hdiv⟩ := exists_flow_of_cut_lower c hdiag hst hr hcut
  have hdivint : ∀ x, IntegerValue (netOut f x) := by
    intro x
    rw [hdiv]
    apply IntegerValue.sub
    · split_ifs <;> first | exact hrint | exact IntegerValue.zero
    · split_ifs <;> first | exact hrint | exact IntegerValue.zero
  obtain ⟨g, hg, hgcap, hgdiv, hgint, hgcyc⟩ :=
    exists_cycle_free_integral_flow c f hf hcap hdivint
  exact ⟨g, hg, hgcap, fun x => (hgdiv x).trans (hdiv x), hgint, hgcyc⟩

/-- Integral maximum flow/minimum cut for a genuine finite natural-capacity
network. The matching shore and both sides of the equality are explicit. -/
theorem exists_integral_maxFlow (c : V → V → ℕ) (hdiag : ∀ v, c v v = 0)
    {s t : V} (hst : s ≠ t) :
    ∃ f : V → V → ℝ, ∃ S : Finset V, s ∈ S ∧ t ∉ S ∧ IsFlow f ∧
      (∀ u v, f u v ≤ c u v) ∧
      (∀ x, netOut f x = (if x = s then (capacityCut c S : ℝ) else 0) -
        (if x = t then (capacityCut c S : ℝ) else 0)) ∧
      (∀ u v, IntegerValue (f u v)) ∧
      (∀ T : Finset V, s ∈ T → t ∉ T → capacityCut c S ≤ capacityCut c T) := by
  obtain ⟨g, S, hg, hs, ht, hval, _, hmin⟩ := (naturalDigraph c hdiag).maxFlow_minCut hst
  have hminN : ∀ T : Finset V, s ∈ T → t ∉ T → capacityCut c S ≤ capacityCut c T := by
    intro T hsT htT
    have h := hmin T hsT htT
    simp only [naturalDigraph_out] at h
    exact_mod_cast h
  have hrint : IntegerValue (capacityCut c S : ℝ) :=
    ⟨(capacityCut c S : ℤ), by simp⟩
  obtain ⟨f, hf, hfcap, hfdiv, hfint, _⟩ := exists_acyclic_integral_of_cut_lower c hdiag hst
    (Nat.cast_nonneg (capacityCut c S)) hrint (by
      intro T hsT htT
      exact_mod_cast hminN T hsT htT)
  exact ⟨f, S, hs, ht, hf, hfcap, hfdiv, hfint, hminN⟩

def unitCapacity (H : WeightedGraph V) (u v : V) : ℕ := if 0 < H.w u v then 1 else 0

theorem unitCapacity_cast {H : WeightedGraph V} (hH : AllPairsAudit.Unweighted H) (u v : V) :
    (unitCapacity H u v : ℝ) = H.w u v := by
  rcases hH u v with h | h <;> simp [unitCapacity, h]

theorem unitCapacity_diag (H : WeightedGraph V) (v : V) : unitCapacity H v v = 0 := by
  simp [unitCapacity, H.diag]

theorem unitCapacity_cut {H : WeightedGraph V} (hH : AllPairsAudit.Unweighted H) (S : Finset V) :
    (capacityCut (unitCapacity H) S : ℝ) = H.cut S := by
  simp only [capacityCut, Nat.cast_sum, unitCapacity_cast hH, WeightedGraph.cut]

def terminalShore (H : WeightedGraph V) (s t : V) : Finset V :=
  if h : s ≠ t then Classical.choose (AllPairsAudit.exists_st_minimum H h) else ∅

def terminalValue (H : WeightedGraph V) (s t : V) : ℝ := H.cut (terminalShore H s t)

theorem terminalShore_spec (H : WeightedGraph V) {s t : V} (hst : s ≠ t) :
    IsSTMinCut H s t (terminalShore H s t) := by
  rw [terminalShore, dite_eq_left hst]
  exact Classical.choose_spec (AllPairsAudit.exists_st_minimum H hst)

theorem terminalValue_nonneg (H : WeightedGraph V) (s t : V) : 0 ≤ terminalValue H s t :=
  H.cut_nonneg _

theorem terminalValue_le_cut (H : WeightedGraph V) {s t : V} (hst : s ≠ t)
    {S : Finset V} (hs : s ∈ S) (ht : t ∉ S) : terminalValue H s t ≤ H.cut S :=
  (terminalShore_spec H hst).2.2 S hs ht

theorem terminalValue_mono {H G : WeightedGraph V} {s t : V}
    (hst : s ≠ t) (hHG : H.IsSubgraph G) : terminalValue H s t ≤ terminalValue G s t := by
  have hS := terminalShore_spec G hst
  exact (terminalValue_le_cut H hst hS.1 hS.2.1).trans (hHG.cut_le _)

theorem terminalValue_integer {H : WeightedGraph V} (hH : AllPairsAudit.Unweighted H)
    (s t : V) : IntegerValue (terminalValue H s t) := by
  refine ⟨(capacityCut (unitCapacity H) (terminalShore H s t) : ℤ), ?_⟩
  simpa only [terminalValue, Int.cast_natCast] using
    (unitCapacity_cut hH (terminalShore H s t)).symm

def FlowSpec (H : WeightedGraph V) (s t : V) (r : ℝ) (f : V → V → ℝ) : Prop :=
  Certificate.Feasible H f ∧
    (∀ x, netOut f x = (if x = s then r else 0) - (if x = t then r else 0)) ∧
    ∀ u v, IntegerValue (f u v)

/-- A true integral maximum flow in the explicit learned unit graph. -/
theorem exists_maximumFlow (H : WeightedGraph V) (hH : AllPairsAudit.Unweighted H)
    {s t : V} (hst : s ≠ t) :
    ∃ f : V → V → ℝ, FlowSpec H s t (terminalValue H s t) f := by
  obtain ⟨f, S, hs, ht, hf, hcap, hdiv, hint, hmin⟩ :=
    exists_integral_maxFlow (unitCapacity H) (unitCapacity_diag H) hst
  have hval : (capacityCut (unitCapacity H) S : ℝ) = terminalValue H s t := by
    have hS : H.cut S ≤ terminalValue H s t := by
      have htshore := terminalShore_spec H hst
      have h := hmin (terminalShore H s t) htshore.1 htshore.2.1
      have hR : (capacityCut (unitCapacity H) S : ℝ) ≤
          (capacityCut (unitCapacity H) (terminalShore H s t) : ℝ) := by exact_mod_cast h
      simpa only [terminalValue, unitCapacity_cut hH] using hR
    rw [unitCapacity_cut hH]
    exact le_antisymm hS (terminalValue_le_cut H hst hs ht)
  refine ⟨f, ⟨hf, ?_⟩, ?_, hint⟩
  · intro u v
    rw [abs_le]
    have huv := hcap u v
    have hvu := hcap v u
    rw [unitCapacity_cast hH] at huv hvu
    rw [hf u v, H.symm v u] at hvu
    exact ⟨by linarith, huv⟩
  · intro x
    simpa only [hval] using hdiv x

/-- A public choice from the proved finite-graph maximum-flow theorem.
Malformed public inputs use zero and still do not consult a hidden graph. -/
def maximumFlow (H : WeightedGraph V) (s t : V) : V → V → ℝ :=
  if h : AllPairsAudit.Unweighted H ∧ s ≠ t then
    Classical.choose (exists_maximumFlow H h.1 h.2)
  else fun _ _ => 0

theorem maximumFlow_spec (H : WeightedGraph V) (hH : AllPairsAudit.Unweighted H)
    {s t : V} (hst : s ≠ t) : FlowSpec H s t (terminalValue H s t) (maximumFlow H s t) := by
  rw [maximumFlow, dite_eq_left ⟨hH, hst⟩]
  exact Classical.choose_spec (exists_maximumFlow H hH hst)

def naturalPositive (f : V → V → ℝ) (u v : V) : ℕ := ⌊max (f u v) 0⌋₊

theorem naturalPositive_cast {f : V → V → ℝ} (hf : ∀ u v, IntegerValue (f u v))
    (u v : V) : (naturalPositive f u v : ℝ) = max (f u v) 0 := by
  by_cases hpos : 0 ≤ f u v
  · obtain ⟨m, hm⟩ := (hf u v).exists_nat hpos
    simp [naturalPositive, max_eq_left hpos, hm]
  · have hnonpos : f u v ≤ 0 := (not_le.mp hpos).le
    simp [naturalPositive, max_eq_right hnonpos]

theorem naturalPositive_pos {f : V → V → ℝ} (hf : ∀ u v, IntegerValue (f u v))
    (u v : V) : 0 < naturalPositive f u v ↔ 0 < f u v := by
  have he := naturalPositive_cast hf u v
  have hn : (0 : ℝ) < naturalPositive f u v ↔ 0 < naturalPositive f u v := by norm_cast
  rw [← hn, he, lt_max_iff]
  simp

theorem naturalPositive_div {f : V → V → ℝ} (hf : IsFlow f)
    (hint : ∀ u v, IntegerValue (f u v)) (u : V) :
    arcDiv (naturalPositive f) u = netOut f u := by
  rw [arcDiv, ← sum_sub_distrib]
  apply sum_congr rfl
  intro v _
  rw [naturalPositive_cast hint, naturalPositive_cast hint, hf u v]
  by_cases h : 0 ≤ f u v
  · rw [max_eq_left h, max_eq_right (by linarith)]
    ring
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
    ring

/-- Acyclicity and integrality now discharge the rank premise of Support. -/
theorem cycle_free_support_bound {f : V → V → ℝ} (hf : IsFlow f)
    (hint : ∀ u v, IntegerValue (f u v)) (hcycle : NoDirectedCycle f)
    (s t : V) {r : ℝ} (hr : 0 ≤ r)
    (hdiv : ∀ x, netOut f x = (if x = s then r else 0) - (if x = t then r else 0)) :
    (supportSize (naturalPositive f) : ℝ) ≤
      Real.sqrt 2 * Fintype.card V * Real.sqrt r := by
  obtain ⟨p, hp, horder⟩ := topological_numbering hcycle
  exact supportSize_le (naturalPositive f) p hp
    (fun u v h => horder u v ((naturalPositive_pos hint u v).mp h)) s t hr
    (fun x => (naturalPositive_div hf hint x).trans (hdiv x))

theorem FlowSpec.mono {H G : WeightedGraph V} {s t : V} {r : ℝ} {f : V → V → ℝ}
    (hf : FlowSpec H s t r f) (hHG : H.IsSubgraph G) : FlowSpec G s t r f :=
  ⟨⟨hf.1.1, fun u v => (hf.1.2 u v).trans (hHG u v)⟩, hf.2⟩

/-- Integral unit-capacity flow has only the three explicit signed values.
This supports the residual-reachability split into unused edges and known
reverse arcs. -/
theorem FlowSpec.unit_values {H : WeightedGraph V} (hH : AllPairsAudit.Unweighted H)
    {s t : V} {r : ℝ} {f : V → V → ℝ} (hf : FlowSpec H s t r f) (u v : V) :
    f u v = -1 ∨ f u v = 0 ∨ f u v = 1 := by
  obtain ⟨z, hz⟩ := hf.2.2 u v
  have hab : |f u v| ≤ 1 := (hf.1.2 u v).trans (AllPairsAudit.unweighted_edge_le_one hH u v)
  rw [hz, abs_le] at hab
  have hlo : (-1 : ℤ) ≤ z := by exact_mod_cast hab.1
  have hhi : z ≤ (1 : ℤ) := by exact_mod_cast hab.2
  have hc : z = -1 ∨ z = 0 ∨ z = 1 := by omega
  rcases hc with hc | hc | hc <;> simp [hz, hc]

theorem FlowSpec.cut_flow {H : WeightedGraph V} {s t : V} {r : ℝ} {f : V → V → ℝ}
    (hf : FlowSpec H s t r f) {S : Finset V} (hs : s ∈ S) (ht : t ∉ S) :
    (∑ u ∈ S, ∑ v ∈ Sᶜ, f u v) = r := by
  rw [← sum_netOut_eq hf.1.1]
  simp only [hf.2.1, sum_sub_distrib, sum_ite_eq', hs, ht, ↓reduceIte, sub_zero]

theorem FlowSpec.value_le_cut {H : WeightedGraph V} {s t : V} {r : ℝ}
    {f : V → V → ℝ} (hf : FlowSpec H s t r f) {S : Finset V}
    (hs : s ∈ S) (ht : t ∉ S) : r ≤ H.cut S := by
  rw [← hf.cut_flow hs ht]
  apply sum_le_sum
  intro u _
  exact sum_le_sum fun v _ => (le_abs_self _).trans (hf.1.2 u v)

theorem FlowSpec.value_le_terminalValue {H : WeightedGraph V} {s t : V} {r : ℝ}
    {f : V → V → ℝ} (hf : FlowSpec H s t r f) (hst : s ≠ t) :
    r ≤ terminalValue H s t := by
  have hshore := terminalShore_spec H hst
  exact hf.value_le_cut hshore.1 hshore.2.1

/-- Equality in the cut bound saturates every crossing capacity separately. -/
theorem FlowSpec.saturated_of_cut_eq {H : WeightedGraph V} {s t : V} {r : ℝ}
    {f : V → V → ℝ} (hf : FlowSpec H s t r f) {S : Finset V}
    (hs : s ∈ S) (ht : t ∉ S) (hcut : H.cut S = r) :
    ∀ u ∈ S, ∀ v ∉ S, f u v = H.w u v := by
  have hslack (u v : V) : 0 ≤ H.w u v - f u v :=
    sub_nonneg.mpr ((le_abs_self _).trans (hf.1.2 u v))
  have hsum : (∑ u ∈ S, ∑ v ∈ Sᶜ, (H.w u v - f u v)) = 0 := by
    simp only [sum_sub_distrib]
    change H.cut S - (∑ u ∈ S, ∑ v ∈ Sᶜ, f u v) = 0
    rw [hcut, hf.cut_flow hs ht, sub_self]
  intro u hu v hv
  have hrow := (sum_eq_zero_iff_of_nonneg
    (fun x (_ : x ∈ S) => sum_nonneg fun y (_ : y ∈ Sᶜ) => hslack x y)).mp hsum u hu
  have hpair := (sum_eq_zero_iff_of_nonneg
    (fun y (_ : y ∈ Sᶜ) => hslack u y)).mp hrow v (mem_compl.mpr hv)
  exact (sub_eq_zero.mp hpair).symm

/-- A flow meeting the actual minimum-cut value has no residual path from
source to sink. The barrier is its genuinely minimizing saturated shore. -/
theorem FlowSpec.no_residual_path {H : WeightedGraph V} {s t : V} {r : ℝ}
    {f : V → V → ℝ} (hf : FlowSpec H s t r f) (hst : s ≠ t)
    (hoptimal : r = terminalValue H s t) :
    ¬ Relation.ReflTransGen (fun u v => f u v < H.w u v) s t := by
  let S := terminalShore H s t
  have hS := terminalShore_spec H hst
  have hsat : ∀ u ∈ S, ∀ v ∉ S, f u v = H.w u v :=
    hf.saturated_of_cut_eq hS.1 hS.2.1 hoptimal.symm
  have hclosed : ∀ v, Relation.ReflTransGen (fun u v => f u v < H.w u v) s v → v ∈ S := by
    intro v hv
    induction hv with
    | refl => exact hS.1
    | @tail u v _ huv ih =>
      by_contra hnot
      rw [hsat u ih v hnot] at huv
      exact (lt_irrefl _) huv
  exact fun h => hS.2.1 (hclosed t h)

theorem maximumFlow_no_residual_path (H : WeightedGraph V)
    (hH : AllPairsAudit.Unweighted H) {s t : V} (hst : s ≠ t) :
    ¬ Relation.ReflTransGen (fun u v => maximumFlow H s t u v < H.w u v) s t :=
  (maximumFlow_spec H hH hst).no_residual_path hst rfl

def residualCapacity (G : WeightedGraph V) (f : V → V → ℝ) (u v : V) : ℕ :=
  ⌊G.w u v - f u v⌋₊

theorem residualCapacity_cast {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G)
    {s t : V} {r : ℝ} {f : V → V → ℝ} (hf : FlowSpec G s t r f) (u v : V) :
    (residualCapacity G f u v : ℝ) = G.w u v - f u v := by
  have hint : IntegerValue (G.w u v - f u v) := by
    apply IntegerValue.sub
    · rcases hG u v with h | h
      · exact ⟨0, by simpa using h⟩
      · exact ⟨1, by simpa using h⟩
    · exact hf.2.2 u v
  have hnonneg : 0 ≤ G.w u v - f u v :=
    sub_nonneg.mpr ((le_abs_self _).trans (hf.1.2 u v))
  obtain ⟨m, hm⟩ := hint.exists_nat hnonneg
  simp [residualCapacity, hm]

theorem residualCapacity_diag (G : WeightedGraph V) {f : V → V → ℝ}
    (hf : IsFlow f) (v : V) : residualCapacity G f v v = 0 := by
  simp [residualCapacity, G.diag, hf.self]

theorem residualCapacity_cut {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G)
    {s t : V} {r : ℝ} {f : V → V → ℝ} (hf : FlowSpec G s t r f)
    {S : Finset V} (hs : s ∈ S) (ht : t ∉ S) :
    (capacityCut (residualCapacity G f) S : ℝ) = G.cut S - r := by
  simp only [capacityCut, Nat.cast_sum, residualCapacity_cast hG hf, sum_sub_distrib]
  rw [hf.cut_flow hs ht]
  rfl

/-- The capacity inequality for the actual residual network translates back
to a feasible undirected flow after the signed augmentation is added. -/
theorem add_residual_flow {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G)
    {s t : V} {r q : ℝ} {f a : V → V → ℝ} (hf : FlowSpec G s t r f)
    (ha : IsFlow a) (hcap : ∀ u v, a u v ≤ residualCapacity G f u v)
    (hdiv : ∀ x, netOut a x = (if x = s then q else 0) - (if x = t then q else 0))
    (hint : ∀ u v, IntegerValue (a u v)) :
    FlowSpec G s t (r + q) (fun u v => f u v + a u v) := by
  have hflow : IsFlow (fun u v => f u v + a u v) := by
    intro u v
    change f v u + a v u = -(f u v + a u v)
    rw [hf.1.1 u v, ha u v]
    ring
  have hupper : ∀ u v, f u v + a u v ≤ G.w u v := by
    intro u v
    have h := hcap u v
    rw [residualCapacity_cast hG hf] at h
    linarith
  refine ⟨⟨hflow, ?_⟩, ?_, ?_⟩
  · intro u v
    rw [abs_le]
    have hrev := hupper v u
    rw [hf.1.1 u v, ha u v, G.symm v u] at hrev
    exact ⟨by linarith, hupper u v⟩
  · intro x
    rw [netOut_add, hf.2.1, hdiv]
    split_ifs <;> ring
  · intro u v
    exact (hf.2.2 u v).add (hint u v)

/-- Every feasible target yields an actual acyclic integer augmentation in
the residual capacities of an explicit learned flow. -/
theorem exists_residual_augmentation {H G : WeightedGraph V}
    (hG : AllPairsAudit.Unweighted G) (hHG : H.IsSubgraph G)
    {s t : V} (hst : s ≠ t) {r target : ℝ} {g : V → V → ℝ}
    (hg : FlowSpec H s t r g) (htarget : IntegerValue target) (hr : r ≤ target)
    (hfeas : target ≤ terminalValue G s t) :
    ∃ a : V → V → ℝ, IsFlow a ∧
      (∀ u v, a u v ≤ residualCapacity G g u v) ∧
      (∀ x, netOut a x = (if x = s then target - r else 0) -
        (if x = t then target - r else 0)) ∧
      (∀ u v, IntegerValue (a u v)) ∧ NoDirectedCycle a := by
  have hgG := hg.mono hHG
  have hrint : IntegerValue r := by
    have h := (hg.2.1 s)
    simp only [hst, ↓reduceIte, sub_zero] at h
    have hi : IntegerValue (netOut g s) := by
      unfold netOut
      exact IntegerValue.sum univ (fun v => g s v) (fun v _ => hg.2.2 s v)
    rwa [h] at hi
  apply exists_acyclic_integral_of_cut_lower (residualCapacity G g)
    (residualCapacity_diag G hg.1.1) hst (sub_nonneg.mpr hr) (htarget.sub hrint)
  intro S hs ht
  rw [residualCapacity_cut hG hgG hs ht]
  exact sub_le_sub_right (hfeas.trans (terminalValue_le_cut G hst hs ht)) r

end
end CutQueryComplexity.CanonicalST.Augmentation

#print axioms CutQueryComplexity.CanonicalST.Augmentation.exists_flow_of_cut_lower
#print axioms CutQueryComplexity.CanonicalST.Augmentation.exists_acyclic_integral_of_cut_lower
#print axioms CutQueryComplexity.CanonicalST.Augmentation.exists_integral_maxFlow
#print axioms CutQueryComplexity.CanonicalST.Augmentation.exists_maximumFlow
#print axioms CutQueryComplexity.CanonicalST.Augmentation.maximumFlow_spec
#print axioms CutQueryComplexity.CanonicalST.Augmentation.naturalPositive_div
#print axioms CutQueryComplexity.CanonicalST.Augmentation.cycle_free_support_bound
#print axioms CutQueryComplexity.CanonicalST.Augmentation.residualCapacity_cut
#print axioms CutQueryComplexity.CanonicalST.Augmentation.add_residual_flow
#print axioms CutQueryComplexity.CanonicalST.Augmentation.exists_residual_augmentation

#print axioms CutQueryComplexity.CanonicalST.Augmentation.terminalValue_mono
#print axioms CutQueryComplexity.CanonicalST.Augmentation.FlowSpec.unit_values

#print axioms CutQueryComplexity.CanonicalST.Augmentation.FlowSpec.saturated_of_cut_eq
#print axioms CutQueryComplexity.CanonicalST.Augmentation.FlowSpec.no_residual_path
#print axioms CutQueryComplexity.CanonicalST.Augmentation.maximumFlow_no_residual_path
