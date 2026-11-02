import CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.Basic
import CutQueryComplexity.Graph.Integral
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Tauto

/-!
# Public fake edges from the actual clone-matching history

A `MarkedRound` annotates the existing `CutMatching.Matching`; it does not
replace it. Markers contain both endpoints of each selected pair. Projection
uses the existing graph contraction, retaining parallel-edge multiplicity
and discarding projected loops. Natural edge counts count clone pairs before
projection and add across rounds, so they never collapse parallel copies.

No hidden graph, flow, cut player, or desired degree/count certificate is an
input to this construction. Completion-deficit and real-route congestion
bounds remain separate obligations of the producer of the matching history.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges

open Finset WeightedGraph CutMatching
open scoped Classical
noncomputable section

variable {C V : Type} [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]

/-- Public endpoint annotation of the literal matching returned by a round. -/
structure MarkedRound (C : Type) where
  matching : Matching C
  fakeEndpoints : Finset C
  fake_mate : ∀ c, matching.mate c ∈ fakeEndpoints ↔ c ∈ fakeEndpoints

/-- Select actual matching edges, retaining their clone endpoints. -/
def markedSimple (r : MarkedRound C) : _root_.SimpleGraph C where
  Adj c d := c ∈ r.fakeEndpoints ∧ r.matching.mate c = d
  symm := ⟨by
    intro c d h
    refine ⟨?_, (r.matching.paired_iff c d).mp h.2⟩
    rw [← h.2]
    exact (r.fake_mate c).mpr h.1⟩
  loopless := ⟨fun c h => r.matching.no_fixed c h.2⟩

@[simp] theorem markedSimple_adj (r : MarkedRound C) (c d : C) :
    (markedSimple r).Adj c d ↔ c ∈ r.fakeEndpoints ∧ r.matching.mate c = d := Iff.rfl

def markedGraph (r : MarkedRound C) : WeightedGraph C :=
  SimpleGraph.toWeighted (markedSimple r)

@[simp] theorem markedGraph_w (r : MarkedRound C) (c d : C) :
    (markedGraph r).w c d =
      if c ∈ r.fakeEndpoints ∧ r.matching.mate c = d then 1 else 0 := by
  simp only [markedGraph, SimpleGraph.toWeighted_w, markedSimple_adj]

/-- This counts actual selected clone pairs, not distinct original endpoints. -/
def pairCount (r : MarkedRound C) : ℕ := (markedSimple r).edgeFinset.card

theorem markedSimple_degree (r : MarkedRound C) (c : C) :
    (markedSimple r).degree c = if c ∈ r.fakeEndpoints then 1 else 0 := by
  rw [← (markedSimple r).card_neighborFinset_eq_degree]
  have he : (markedSimple r).neighborFinset c =
      if c ∈ r.fakeEndpoints then {r.matching.mate c} else ∅ := by
    ext d
    by_cases hc : c ∈ r.fakeEndpoints <;> simp [hc, eq_comm]
  rw [he]
  split <;> simp

theorem two_mul_pairCount (r : MarkedRound C) :
    2 * pairCount r = r.fakeEndpoints.card := by
  have h := (markedSimple r).sum_degrees_eq_twice_card_edges
  simpa [markedSimple_degree, pairCount] using h.symm

theorem pairCount_eq_half (r : MarkedRound C) :
    pairCount r = r.fakeEndpoints.card / 2 := by
  have h := two_mul_pairCount r
  omega

/-- The one-sided fake set used by clone assignment counts each selected pair once. -/
theorem pairCount_eq_shore (r : MarkedRound C) (S : Finset C)
    (hcross : r.matching.Crosses S) :
    pairCount r = (S.filter (fun c => c ∈ r.fakeEndpoints)).card := by
  have he : r.fakeEndpoints.filter (fun c => c ∉ S) =
      (r.fakeEndpoints.filter (fun c => c ∈ S)).image r.matching.mate := by
    ext c
    constructor
    · intro hc
      obtain ⟨hf, hout⟩ := mem_filter.mp hc
      have hin : r.matching.mate c ∈ S :=
        (hcross (r.matching.mate c)).mpr (by
          rw [r.matching.involutive c]
          exact hout)
      exact mem_image.mpr ⟨r.matching.mate c,
        mem_filter.mpr ⟨(r.fake_mate c).mpr hf, hin⟩, r.matching.involutive c⟩
    · intro hc
      obtain ⟨d, hd, rfl⟩ := mem_image.mp hc
      obtain ⟨hf, hin⟩ := mem_filter.mp hd
      exact mem_filter.mpr ⟨(r.fake_mate d).mpr hf, (hcross d).mp hin⟩
  have hc := card_filter_add_card_filter_not (s := r.fakeEndpoints) (fun c => c ∈ S)
  rw [he, card_image_of_injective _ r.matching.mate.injective] at hc
  have hp := two_mul_pairCount r
  have hs : S.filter (fun c => c ∈ r.fakeEndpoints) =
      r.fakeEndpoints.filter (fun c => c ∈ S) := by ext c; simp [and_comm]
  rw [hs]
  omega

def crossingEndpoints (M : Matching C) (S : Finset C) : Finset C :=
  S.filter (fun c => M.mate c ∉ S)

def fakeCrossing (r : MarkedRound C) (S : Finset C) : ℕ :=
  ((crossingEndpoints r.matching S).filter (fun c => c ∈ r.fakeEndpoints)).card

def realCrossing (r : MarkedRound C) (S : Finset C) : ℕ :=
  ((crossingEndpoints r.matching S).filter (fun c => c ∉ r.fakeEndpoints)).card

theorem matching_cut_count (M : Matching C) (S : Finset C) :
    M.graph.cut S = ((crossingEndpoints M S).card : ℝ) := by
  simp only [WeightedGraph.cut, Matching.graph, crossingEndpoints, card_filter,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply sum_congr rfl
  intro c _
  simp [eq_comm]

theorem markedGraph_cut (r : MarkedRound C) (S : Finset C) :
    (markedGraph r).cut S = (fakeCrossing r S : ℝ) := by
  simp only [WeightedGraph.cut, markedGraph_w, fakeCrossing, crossingEndpoints,
    filter_filter, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply sum_congr rfl
  intro c _
  by_cases hf : c ∈ r.fakeEndpoints <;> simp [hf, eq_comm]

/-- Exact partition of actual matching crossings; no routing claim is assumed. -/
theorem matching_cut_split (r : MarkedRound C) (S : Finset C) :
    r.matching.graph.cut S = (fakeCrossing r S : ℝ) + (realCrossing r S : ℝ) := by
  rw [matching_cut_count]
  have h := card_filter_add_card_filter_not
    (s := crossingEndpoints r.matching S) (fun c => c ∈ r.fakeEndpoints)
  change ((crossingEndpoints r.matching S).card : ℝ) = _
  exact_mod_cast h.symm

variable {b : ℕ}

/-- Full original fibers, so a projected loop never crosses this shore. -/
def cloneShore (T : Finset V) : Finset (V × Fin b) := pull Prod.fst T

@[simp] theorem mem_cloneShore (T : Finset V) (c : V × Fin b) :
    c ∈ cloneShore (b := b) T ↔ c.1 ∈ T := mem_pull _ _ _

theorem cloneShore_eq_product (T : Finset V) :
    cloneShore (b := b) T = T ×ˢ (univ : Finset (Fin b)) := by
  ext c
  simp

@[simp] theorem cloneShore_card (T : Finset V) :
    (cloneShore (b := b) T).card = T.card * b := by rw [cloneShore_eq_product]; simp

/-- Endpoint occurrences whose projection is not a loop. -/
def survivingEndpoints (r : MarkedRound (V × Fin b)) : Finset (V × Fin b) :=
  r.fakeEndpoints.filter (fun c => (r.matching.mate c).1 ≠ c.1)

theorem survivingEndpoints_mate (r : MarkedRound (V × Fin b)) (c : V × Fin b) :
    r.matching.mate c ∈ survivingEndpoints r ↔ c ∈ survivingEndpoints r := by
  simp only [survivingEndpoints, mem_filter, r.fake_mate]
  rw [r.matching.involutive c]
  exact and_congr_right fun _ => ne_comm

/-- Same literal matching, with precisely the projected-loop endpoints removed. -/
def survivingRound (r : MarkedRound (V × Fin b)) : MarkedRound (V × Fin b) where
  matching := r.matching
  fakeEndpoints := survivingEndpoints r
  fake_mate := survivingEndpoints_mate r

def roundEdgeCount (r : MarkedRound (V × Fin b)) : ℕ := pairCount (survivingRound r)

def roundDegree (r : MarkedRound (V × Fin b)) (v : V) : ℕ :=
  ((survivingEndpoints r).filter (fun c => c.1 = v)).card

/-- Contraction sums clone-edge copies between original fibers and drops loops. -/
def roundGraph (r : MarkedRound (V × Fin b)) : WeightedGraph V :=
  (markedGraph r).contract Prod.fst

@[simp] theorem roundGraph_diag (r : MarkedRound (V × Fin b)) (v : V) :
    (roundGraph r).w v v = 0 := (roundGraph r).diag v

theorem roundGraph_cut (r : MarkedRound (V × Fin b)) (T : Finset V) :
    (roundGraph r).cut T = (fakeCrossing r (cloneShore T) : ℝ) := by
  change ((markedGraph r).contract Prod.fst).cut T = _
  rw [cut_contract]
  exact markedGraph_cut r (cloneShore T)

theorem roundGraph_degree (r : MarkedRound (V × Fin b)) (v : V) :
    (roundGraph r).degree v = (roundDegree r v : ℝ) := by
  rw [← cut_singleton, roundGraph_cut]
  unfold fakeCrossing roundDegree
  apply congrArg (fun S : Finset (V × Fin b) => (S.card : ℝ))
  ext c
  by_cases hv : c.1 = v
  · simp [crossingEndpoints, survivingEndpoints, hv, and_comm]
  · simp [crossingEndpoints, survivingEndpoints, hv]

theorem fst_fiber_card (v : V) : (fiber (Prod.fst : V × Fin b → V) v).card = b := by
  have he : fiber (Prod.fst : V × Fin b → V) v = {v} ×ˢ (univ : Finset (Fin b)) := by
    ext c
    simp only [mem_fiber, mem_product, mem_singleton, mem_univ, and_true]
  rw [he]
  simp

theorem roundDegree_le (r : MarkedRound (V × Fin b)) (v : V) : roundDegree r v ≤ b := by
  have hs : (survivingEndpoints r).filter (fun c => c.1 = v) ⊆
      fiber (Prod.fst : V × Fin b → V) v := by
    intro c hc
    exact (mem_fiber _ _ _).mpr (mem_filter.mp hc).2
  simpa only [roundDegree, fst_fiber_card] using card_le_card hs

theorem sum_roundDegree (r : MarkedRound (V × Fin b)) :
    (∑ v, roundDegree r v) = (survivingEndpoints r).card := by
  simp only [roundDegree, card_filter]
  rw [sum_comm]
  simp [eq_comm]

theorem two_mul_roundEdgeCount (r : MarkedRound (V × Fin b)) :
    2 * roundEdgeCount r = (survivingEndpoints r).card := two_mul_pairCount (survivingRound r)

theorem roundGraph_sum_degrees (r : MarkedRound (V × Fin b)) :
    (∑ v, (roundGraph r).degree v) = 2 * (roundEdgeCount r : ℝ) := by
  simp only [roundGraph_degree, ← Nat.cast_sum, sum_roundDegree,
    ← two_mul_roundEdgeCount, Nat.cast_mul, Nat.cast_ofNat]

theorem roundEdgeCount_le_pairCount (r : MarkedRound (V × Fin b)) :
    roundEdgeCount r ≤ pairCount r := by
  have hc : (survivingEndpoints r).card ≤ r.fakeEndpoints.card :=
    card_le_card (filter_subset _ _)
  have hfirst := two_mul_roundEdgeCount r
  have hsecond := two_mul_pairCount r
  omega

theorem roundEdgeCount_zero_of_projected_loops (r : MarkedRound (V × Fin b))
    (hloops : ∀ c ∈ r.fakeEndpoints, (r.matching.mate c).1 = c.1) :
    roundEdgeCount r = 0 := by
  have he : survivingEndpoints r = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro c hc
    obtain ⟨hf, hn⟩ := mem_filter.mp hc
    exact hn (hloops c hf)
  have h := two_mul_roundEdgeCount r
  rw [he, card_empty] at h
  omega

theorem pairCount_zero_of_no_fake (r : MarkedRound C) (h : r.fakeEndpoints = ∅) :
    pairCount r = 0 := by
  have hc := two_mul_pairCount r
  rw [h, card_empty] at hc
  omega

/-- Real weights are exact natural edge-copy counts, including parallel pairs. -/
def roundMultiplicity (r : MarkedRound (V × Fin b)) (u v : V) : ℕ :=
  if u = v then 0 else
    ((fiber (Prod.fst : V × Fin b → V) u).filter
      (fun c => c ∈ r.fakeEndpoints ∧ (r.matching.mate c).1 = v)).card

theorem roundGraph_w (r : MarkedRound (V × Fin b)) (u v : V) :
    (roundGraph r).w u v = (roundMultiplicity r u v : ℝ) := by
  by_cases huv : u = v
  · simp [huv, roundMultiplicity]
  · simp only [roundGraph, contract, huv, if_false, cross, markedGraph_w,
      roundMultiplicity, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    apply sum_congr rfl
    intro c _
    by_cases hf : c ∈ r.fakeEndpoints <;> simp [hf, eq_comm]

def fakeGraph : List (MarkedRound (V × Fin b)) → WeightedGraph V
  | [] => 0
  | r :: history => graphAdd (roundGraph r) (fakeGraph history)

def edgeCount (history : List (MarkedRound (V × Fin b))) : ℕ :=
  (history.map roundEdgeCount).sum

def degreeTable (history : List (MarkedRound (V × Fin b))) (v : V) : ℕ :=
  (history.map (fun r => roundDegree r v)).sum

def multiplicity (history : List (MarkedRound (V × Fin b))) (u v : V) : ℕ :=
  (history.map (fun r => roundMultiplicity r u v)).sum

def realCutCount (history : List (MarkedRound (V × Fin b))) (T : Finset V) : ℕ :=
  (history.map (fun r => realCrossing r (cloneShore T))).sum

def fakeCutCount (history : List (MarkedRound (V × Fin b))) (T : Finset V) : ℕ :=
  (history.map (fun r => fakeCrossing r (cloneShore T))).sum

theorem graphAdd_degree (G H : WeightedGraph V) (v : V) :
    (graphAdd G H).degree v = G.degree v + H.degree v := by
  simp only [WeightedGraph.degree, graphAdd, sum_add_distrib]

@[simp] theorem fakeGraph_nil : fakeGraph ([] : List (MarkedRound (V × Fin b))) = 0 := rfl

theorem fakeGraph_w (history : List (MarkedRound (V × Fin b))) (u v : V) :
    (fakeGraph history).w u v = (multiplicity history u v : ℝ) := by
  induction history with
  | nil => simp [fakeGraph, multiplicity]
  | cons r history ih =>
      simp only [fakeGraph, graphAdd, roundGraph_w, ih, multiplicity,
        List.map_cons, List.sum_cons, Nat.cast_add]

theorem fakeGraph_degree (history : List (MarkedRound (V × Fin b))) (v : V) :
    (fakeGraph history).degree v = (degreeTable history v : ℝ) := by
  induction history with
  | nil => simp [fakeGraph, WeightedGraph.degree, degreeTable]
  | cons r history ih =>
      simp only [fakeGraph, graphAdd_degree, roundGraph_degree, ih, degreeTable,
        List.map_cons, List.sum_cons, Nat.cast_add]

theorem degreeTable_le (history : List (MarkedRound (V × Fin b))) (v : V) :
    degreeTable history v ≤ history.length * b := by
  induction history with
  | nil => simp [degreeTable]
  | cons r history ih =>
      simp only [degreeTable, List.map_cons, List.sum_cons, List.length_cons]
      have h := roundDegree_le r v
      change roundDegree r v + degreeTable history v ≤ (history.length + 1) * b
      calc
        _ ≤ b + history.length * b := Nat.add_le_add h ih
        _ = _ := by ring

theorem fakeGraph_degree_le (history : List (MarkedRound (V × Fin b))) (v : V) :
    (fakeGraph history).degree v ≤ (history.length * b : ℕ) := by
  rw [fakeGraph_degree]
  exact_mod_cast degreeTable_le history v

/-- The exact handshake equation required by the pruning network. -/
theorem sum_degrees (history : List (MarkedRound (V × Fin b))) :
    (∑ v, (fakeGraph history).degree v) = 2 * (edgeCount history : ℝ) := by
  induction history with
  | nil => simp [fakeGraph, WeightedGraph.degree, edgeCount]
  | cons r history ih =>
      simp only [fakeGraph, graphAdd_degree, sum_add_distrib, roundGraph_sum_degrees, ih,
        edgeCount, List.map_cons, List.sum_cons, Nat.cast_add]
      ring

theorem fakeGraph_cut (history : List (MarkedRound (V × Fin b))) (T : Finset V) :
    (fakeGraph history).cut T = (fakeCutCount history T : ℝ) := by
  induction history with
  | nil => simp [fakeGraph, fakeCutCount]
  | cons r history ih =>
      simp only [fakeGraph, graphAdd_cut, roundGraph_cut, ih, fakeCutCount,
        List.map_cons, List.sum_cons, Nat.cast_add]

theorem cut_le_degree_sum (history : List (MarkedRound (V × Fin b))) (T : Finset V) :
    (fakeGraph history).cut T ≤ ∑ v ∈ T, (degreeTable history v : ℝ) := by
  have h := (fakeGraph history).cut_add_internal T
  have hn : 0 ≤ ∑ u ∈ T, ∑ v ∈ T, (fakeGraph history).w u v :=
    sum_nonneg fun u _ => sum_nonneg fun v _ => (fakeGraph history).nonneg u v
  simp only [fakeGraph_degree] at h
  linarith

theorem edgeCount_le_pairCount (history : List (MarkedRound (V × Fin b))) :
    edgeCount history ≤ (history.map pairCount).sum := by
  induction history with
  | nil => simp [edgeCount]
  | cons r history ih =>
      exact Nat.add_le_add (roundEdgeCount_le_pairCount r) ih

theorem pairCount_sum_le (history : List (MarkedRound (V × Fin b))) (K : ℕ)
    (h : ∀ r ∈ history, pairCount r ≤ K) :
    (history.map pairCount).sum ≤ history.length * K := by
  induction history with
  | nil => simp
  | cons r history ih =>
      have hr := h r (List.mem_cons_self ..)
      have hh := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      calc
        _ ≤ K + history.length * K := Nat.add_le_add hr hh
        _ = _ := by ring

/-- Completion supplies only the actual per-round deficit bound, separately. -/
theorem edgeCount_le_budget (history : List (MarkedRound (V × Fin b))) (R β : ℕ)
    (hlength : history.length ≤ R) (hcounts : ∀ r ∈ history, pairCount r ≤ β * b) :
    edgeCount history ≤ R * β * b := by
  calc
    edgeCount history ≤ (history.map pairCount).sum := edgeCount_le_pairCount history
    _ ≤ history.length * (β * b) := pairCount_sum_le history (β * b) hcounts
    _ ≤ R * (β * b) := Nat.mul_le_mul_right _ hlength
    _ = _ := (Nat.mul_assoc R β b).symm

/-- This is the real/fake split of the original literal matching history. -/
theorem history_cut_split (history : List (MarkedRound (V × Fin b))) (T : Finset V) :
    (historyGraph (history.map MarkedRound.matching)).cut (cloneShore T) =
      (fakeGraph history).cut T + (realCutCount history T : ℝ) := by
  induction history with
  | nil => simp [fakeGraph, realCutCount]
  | cons r history ih =>
      simp only [List.map_cons, historyGraph_cons_cut, matching_cut_split, ih,
        fakeGraph, graphAdd_cut, roundGraph_cut, realCutCount, List.sum_cons, Nat.cast_add]
      ring

/-- Chronological round records also support the player's newest-first history.
The producer still has to prove that this is its actual returned history. -/
theorem history_cut_split_reverse (history : List (MarkedRound (V × Fin b))) (T : Finset V) :
    (historyGraph ((history.map MarkedRound.matching).reverse)).cut (cloneShore T) =
      (fakeGraph history).cut T + (realCutCount history T : ℝ) := by
  have h := history_cut_split history.reverse T
  simpa only [List.map_reverse, fakeGraph_cut, fakeCutCount, realCutCount,
    List.sum_reverse] using h

/-- Parallel copies in different rounds add; they are never deduplicated. -/
theorem fakeGraph_append_w (left right : List (MarkedRound (V × Fin b))) (u v : V) :
    (fakeGraph (left ++ right)).w u v = (fakeGraph left).w u v + (fakeGraph right).w u v := by
  simp only [fakeGraph_w, multiplicity, List.map_append, List.sum_append, Nat.cast_add]

theorem edgeCount_append (left right : List (MarkedRound (V × Fin b))) :
    edgeCount (left ++ right) = edgeCount left + edgeCount right := by
  simp only [edgeCount, List.map_append, List.sum_append]

theorem fakeGraph_integral (history : List (MarkedRound (V × Fin b))) :
    (fakeGraph history).IsIntegral := fun u v => ⟨multiplicity history u v, fakeGraph_w history u v⟩

theorem edgeCount_zero_of_no_fake (history : List (MarkedRound (V × Fin b)))
    (h : ∀ r ∈ history, r.fakeEndpoints = ∅) : edgeCount history = 0 := by
  have hp : (history.map pairCount).sum ≤ history.length * 0 :=
    pairCount_sum_le history 0 (fun r hr => le_of_eq (pairCount_zero_of_no_fake r (h r hr)))
  have he := edgeCount_le_pairCount history
  omega

/-- Zero constructed edge count really gives the empty weighted multigraph. -/
theorem fakeGraph_zero_of_edgeCount_zero (history : List (MarkedRound (V × Fin b)))
    (h : edgeCount history = 0) : fakeGraph history = 0 := by
  have ht : (∑ u, ∑ v, (fakeGraph history).w u v) = 0 := by
    simpa only [WeightedGraph.degree, h, Nat.cast_zero, mul_zero] using sum_degrees history
  ext u v
  change (fakeGraph history).w u v = 0
  have hrow : (fakeGraph history).w u v ≤ ∑ w, (fakeGraph history).w u w :=
    single_le_sum (fun w _ => (fakeGraph history).nonneg u w) (mem_univ v)
  have hall : (∑ w, (fakeGraph history).w u w) ≤ ∑ x, ∑ w, (fakeGraph history).w x w :=
    single_le_sum (fun x _ => sum_nonneg fun w _ => (fakeGraph history).nonneg x w) (mem_univ u)
  exact le_antisymm (by simpa only [ht] using hrow.trans hall) ((fakeGraph history).nonneg u v)

theorem fakeGraph_zero_of_no_fake (history : List (MarkedRound (V × Fin b)))
    (h : ∀ r ∈ history, r.fakeEndpoints = ∅) : fakeGraph history = 0 :=
  fakeGraph_zero_of_edgeCount_zero history (edgeCount_zero_of_no_fake history h)

end
end CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges.two_mul_pairCount
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges.pairCount_eq_half
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges.pairCount_eq_shore
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges.markedGraph_cut
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges.matching_cut_split
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges.roundGraph_degree
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges.roundDegree_le
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges.roundGraph_sum_degrees
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges.roundEdgeCount_zero_of_projected_loops
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges.fakeGraph_w
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges.fakeGraph_degree
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges.degreeTable_le
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges.sum_degrees
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges.cut_le_degree_sum
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges.edgeCount_le_budget
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges.history_cut_split
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges.history_cut_split_reverse
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges.fakeGraph_append_w
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges.fakeGraph_integral
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges.edgeCount_zero_of_no_fake
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges.fakeGraph_zero_of_no_fake
