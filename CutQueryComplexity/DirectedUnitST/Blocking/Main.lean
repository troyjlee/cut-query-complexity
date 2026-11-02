import CutQueryComplexity.DirectedUnitST.Blocking.Cost
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FinCases

/-!
# Public capped integral terminal repair

The executable inputs are learned state and a public supply bound. Hidden
graphs and feasibility witnesses occur only in the correctness statements.
The zero-supply branch returns immediately. All-answer query limits come
from an actual budgeted decision tree, with exact execution on valid graphs.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DirectedUnitST.Blocking

open Finset DirectedCertificate Certificate Prog
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem source_ne_sink : (source : Node V) ≠ sink := by simp [source, sink]

omit [DecidableEq V] in
theorem node_card : Fintype.card (Node V) = Fintype.card V + 2 := by
  simp only [Node, Fintype.card_sum, Fintype.card_fin]

theorem internalVertices_card :
    (Repair.internalVertices (source : Node V) sink).card = Fintype.card V := by
  have he : Repair.internalVertices (source : Node V) sink =
      (univ : Finset V).map (Function.Embedding.inl : V ↪ Node V) := by
    ext x
    rw [Repair.internalVertices, mem_filter]
    simp only [mem_univ, true_and]
    cases x with
    | inl v => simp [source, sink]
    | inr i => fin_cases i <;> simp [source, sink]
  rw [he, card_map, card_univ]

omit [Fintype V] [DecidableEq V] in
theorem internal_pair_bound (H : WeightedDiGraph (Node V))
    (hcap : Repair.PairBounded (internalGraph H)) :
    ∀ u v, u ≠ source → u ≠ sink → v ≠ source → v ≠ sink → H.c u v + H.c v u ≤ 2 := by
  intro u v hus hut hvs hvt
  cases u with
  | inr i => fin_cases i <;> simp [source, sink] at hus hut
  | inl a =>
      cases v with
      | inr i => fin_cases i <;> simp [source, sink] at hvs hvt
      | inl b => exact hcap a b

/-- Explicit public source/sink arcs for an integral discrepancy vector. -/
def terminalNat (q : V → ℤ) : Node V → Node V → ℕ
  | .inr i, .inl v => if i = 0 then (q v).toNat else 0
  | .inl u, .inr j => if j = 1 then (-q u).toNat else 0
  | _, _ => 0

def augmentedGraph (H : WeightedDiGraph V) (q : V → ℤ) : WeightedDiGraph (Node V) where
  c x y := match x, y with
    | .inl u, .inl v => H.c u v
    | _, _ => (terminalNat q x y : ℝ)
  nonneg x y := by
    cases x <;> cases y
    · exact H.nonneg _ _
    all_goals exact Nat.cast_nonneg _
  diag x := by
    cases x with
    | inl u => exact H.diag u
    | inr i => simp [terminalNat]

def augmentedState (st : State V) (q : V → ℤ) : NetworkState V :=
  ⟨st, fun x y => (terminalNat q x y : ℝ)⟩

theorem augmentedState_realizes {G H : WeightedDiGraph V} {st : State V}
    (hr : st.Realizes G H) (q : V → ℤ) :
    (augmentedState st q).Realizes G (augmentedGraph H q) := by
  refine ⟨hr, ?_, ?_⟩
  · intro i y
    cases y <;> rfl
  · intro x j
    cases x <;> rfl

omit [Fintype V] [DecidableEq V] in
theorem augmentedGraph_integral (H : WeightedDiGraph V) (q : V → ℤ)
    (hint : ∀ u v, ∃ k : ℕ, H.c u v = k) : IntegralCap (augmentedGraph H q) := by
  intro x y
  cases x with
  | inl u =>
      cases y with
      | inl v => exact hint u v
      | inr j => exact ⟨terminalNat q (.inl u) (.inr j), rfl⟩
  | inr i =>
      cases y with
      | inl v => exact ⟨terminalNat q (.inr i) (.inl v), rfl⟩
      | inr j => exact ⟨0, rfl⟩

def totalSupply (q : V → ℤ) : ℕ := ∑ v, (q v).toNat

theorem augmentedGraph_source_cut (H : WeightedDiGraph V) (q : V → ℤ) :
    (augmentedGraph H q).out {source} = totalSupply q := by
  rw [WeightedDiGraph.out_singleton, WeightedDiGraph.outdeg, Fintype.sum_sum_type]
  simp [augmentedGraph, source, terminalNat, totalSupply, Nat.cast_sum]

/-- A proof witness for feasibility only: this is never called by repairProg. -/
def liftFlow (f : V → V → ℝ) (q : V → ℤ) : Node V → Node V → ℝ
  | .inl u, .inl v => f u v
  | .inr i, .inl v => if i = 0 then ((q v).toNat : ℝ) else -((-q v).toNat : ℝ)
  | .inl u, .inr j => if j = 0 then -((q u).toNat : ℝ) else ((-q u).toNat : ℝ)
  | _, _ => 0

omit [Fintype V] [DecidableEq V] in
theorem int_positive_parts (z : ℤ) :
    (z : ℝ) = (z.toNat : ℝ) - ((-z).toNat : ℝ) := by
  cases z <;> simp

omit [Fintype V] [DecidableEq V] in
theorem liftFlow_feasible (H : WeightedDiGraph V) (q : V → ℤ)
    (f : V → V → ℝ) (hf : H.Feasible f) :
    (augmentedGraph H q).Feasible (liftFlow f q) := by
  refine ⟨?_, ?_⟩
  · intro x y
    cases x with
    | inl u =>
        cases y with
        | inl v => exact hf.1 u v
        | inr j => fin_cases j <;> simp [liftFlow]
    | inr i =>
        cases y with
        | inl v => fin_cases i <;> simp [liftFlow]
        | inr j => simp [liftFlow]
  · intro x y
    cases x with
    | inl u =>
        cases y with
        | inl v => exact hf.2 u v
        | inr j => fin_cases j <;> simp [liftFlow, augmentedGraph, terminalNat]
    | inr i =>
        cases y with
        | inl v => fin_cases i <;> simp [liftFlow, augmentedGraph, terminalNat]
        | inr j => simp [liftFlow, augmentedGraph, terminalNat]

omit [DecidableEq V] in
theorem liftFlow_STFlow (H : WeightedDiGraph V) (q : V → ℤ)
    (f : V → V → ℝ) (hf : H.Feasible f) (hdiv : ∀ v, netOut f v = (q v : ℝ)) :
    (augmentedGraph H q).STFlow source sink (liftFlow f q) := by
  refine ⟨liftFlow_feasible H q f hf, ?_⟩
  intro x hxs hxt
  cases x with
  | inr i => fin_cases i <;> simp [source, sink] at hxs hxt
  | inl v =>
      unfold netOut
      rw [Fintype.sum_sum_type]
      simp only [liftFlow, Fin.sum_univ_two, ↓reduceIte]
      change netOut f v + (-((q v).toNat : ℝ) + ((-q v).toNat : ℝ)) = 0
      rw [hdiv, int_positive_parts]
      ring

omit [DecidableEq V] in
theorem liftFlow_source (f : V → V → ℝ) (q : V → ℤ) :
    netOut (liftFlow f q) source = totalSupply q := by
  unfold netOut
  rw [Fintype.sum_sum_type]
  simp [liftFlow, source, totalSupply, Nat.cast_sum]

/-- An explicit nonasymptotic repair bound. N=n+2 includes the two terminals. -/
def repairBound (V : Type) [Fintype V] (R : ℕ) : ℝ :=
  (2 * (Fintype.card (Node V) : ℝ) +
    4 * (Fintype.card (Node V) : ℝ) *
      min (R : ℝ) (6 * (Fintype.card V : ℝ) ^ (2 / 3 : ℝ)) +
    7 * (Fintype.card V : ℝ) * Real.sqrt R) * edgeQueryBound V

def repairBudget (V : Type) [Fintype V] (R : ℕ) : ℕ :=
  if R = 0 then 0 else ⌈repairBound V R⌉₊

def repairProg (st : NetworkState V) (R : ℕ) : Prog (Finset V) ℝ (SolveResult V) :=
  if R = 0 then .pure (solveEmpty st {source} true) else solveProg st source sink

def repairTree (st : NetworkState V) (R : ℕ) :
    DTree (Finset V) ℝ (Option (SolveResult V)) (repairBudget V R) :=
  (repairProg st R).toDTree (repairBudget V R)

theorem repairProg_complete (G : WeightedDiGraph V) (H : WeightedDiGraph (Node V))
    (st : NetworkState V) (hr : st.Realizes G H) (hint : IntegralCap H)
    (R : ℕ) (hsource : H.out {source} ≤ R) :
    SolveCorrect G H source sink ((repairProg st R).eval G.out) := by
  by_cases hR : R = 0
  · have hz : H.out {source} = 0 := by
      rw [hR, Nat.cast_zero] at hsource
      exact le_antisymm hsource (H.out_nonneg _)
    simp only [repairProg, hR, ↓reduceIte, Prog.eval_pure]
    exact solveEmpty_correct G H st hr source sink {source} (by simp)
      (by simpa using Ne.symm (source_ne_sink (V := V))) hz
  · simp only [repairProg, hR, ↓reduceIte]
    exact solveProg_complete G H st hr hint source sink source_ne_sink

/-- The sharp bound is proved for the actual original-cut program before
the budgeted-tree truncation is used to protect arbitrary answer histories. -/
theorem repairProg_cost (G : WeightedDiGraph V) (H : WeightedDiGraph (Node V))
    (st : NetworkState V) (hr : st.Realizes G H) (hint : IntegralCap H)
    (hcap : Repair.PairBounded (internalGraph H)) (R : ℕ)
    (hRn : (R : ℝ) ≤ (Fintype.card V : ℝ) ^ 2) (hsource : H.out {source} ≤ R) :
    (repairProg st R).cost G.out ≤ repairBudget V R := by
  by_cases hR : R = 0
  · simp [repairProg, repairBudget, hR]
  · have hRone : (1 : ℝ) ≤ R := by exact_mod_cast (show 1 ≤ R by omega)
    have hn : (1 : ℝ) ≤ Fintype.card V := by
      have hn0 : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
      nlinarith
    have h := solveProg_cost_sharp G H st hr hint source sink source_ne_sink
      (internal_pair_bound H hcap) (R : ℝ)
      (by simpa only [internalVertices_card] using hn) hRone
      (by simpa only [internalVertices_card] using hRn) hsource
    simp only [internalVertices_card] at h
    have hceil : ((solveProg st source sink).cost G.out : ℝ) ≤
        (⌈repairBound V R⌉₊ : ℝ) := h.trans (Nat.le_ceil _)
    simp only [repairProg, repairBudget, hR, ↓reduceIte]
    exact_mod_cast hceil

/-- The tree has its advertised cap for every sequence of answers. -/
theorem repairTree_cost (read : Finset V → ℝ) (st : NetworkState V) (R : ℕ) :
    (repairTree st R).cost read ≤ repairBudget V R := DTree.cost_le _ _

/-- On valid graphs, the cap never truncates: the tree returns the actual
program output and that output includes a feasible minimum-cut witness. -/
theorem repairTree_correct (G : WeightedDiGraph V) (H : WeightedDiGraph (Node V))
    (st : NetworkState V) (hr : st.Realizes G H) (hint : IntegralCap H)
    (hcap : Repair.PairBounded (internalGraph H)) (R : ℕ)
    (hRn : (R : ℝ) ≤ (Fintype.card V : ℝ) ^ 2) (hsource : H.out {source} ≤ R) :
    ∃ result, (repairTree st R).eval G.out = some result ∧
      SolveCorrect G H source sink result := by
  refine ⟨(repairProg st R).eval G.out, ?_, repairProg_complete G H st hr hint R hsource⟩
  exact Prog.toDTree_eval G.out (repairProg st R) (repairBudget V R)
    (repairProg_cost G H st hr hint hcap R hRn hsource)

/-- A proof-only feasible supply witness forces the operational solve to
route the full requested supply; no witness is consulted by the program. -/
theorem repairProg_value_eq (G : WeightedDiGraph V) (H : WeightedDiGraph (Node V))
    (st : NetworkState V) (hr : st.Realizes G H) (hint : IntegralCap H)
    (R : ℕ) (hsource : H.out {source} ≤ R)
    (f : Node V → Node V → ℝ) (hf : H.STFlow source sink f)
    (hvalue : netOut f source = R) :
    (((repairProg st R).eval G.out).value : ℝ) = R := by
  have hc := repairProg_complete G H st hr hint R hsource
  have hlo := WeightedDiGraph.netOut_le_out hf hc.source_mem hc.target_notMem
  rw [hvalue, ← hc.value_eq_cut] at hlo
  have hhi := hc.min_cut {source} (by simp)
    (by simpa using Ne.symm (source_ne_sink (V := V)))
  rw [← hc.value_eq_cut] at hhi
  exact le_antisymm (hhi.trans hsource) hlo

theorem saturated_row (H : WeightedDiGraph (Node V)) (f : Node V → Node V → ℝ)
    (hf : H.Feasible f) (s : Node V) (hvalue : netOut f s = H.out {s}) (v : Node V) :
    f s v = H.c s v := by
  have hg (w : Node V) : 0 ≤ H.c s w - f s w := sub_nonneg.mpr (hf.2 s w)
  have hsum : ∑ w, (H.c s w - f s w) = 0 := by
    rw [sum_sub_distrib]
    change H.outdeg s - netOut f s = 0
    rw [hvalue, H.out_singleton, sub_self]
  have hle : H.c s v - f s v ≤ ∑ w, (H.c s w - f s w) :=
    single_le_sum (fun w _ => hg w) (mem_univ v)
  rw [hsum] at hle
  linarith [hg v]

omit [DecidableEq V] in
theorem saturated_column (H : WeightedDiGraph (Node V)) (f : Node V → Node V → ℝ)
    (hf : H.Feasible f) (t : Node V)
    (hvalue : -netOut f t = ∑ w, H.c w t) (v : Node V) : f v t = H.c v t := by
  have hg (w : Node V) : 0 ≤ H.c w t - f w t := sub_nonneg.mpr (hf.2 w t)
  have hflow : ∑ w, f w t = -netOut f t := by
    simp only [netOut, hf.1 t, ← sum_neg_distrib]
  have hsum : ∑ w, (H.c w t - f w t) = 0 := by
    rw [sum_sub_distrib, hflow, hvalue, sub_self]
  have hle : H.c v t - f v t ≤ ∑ w, (H.c w t - f w t) :=
    single_le_sum (fun w _ => hg w) (mem_univ v)
  rw [hsum] at hle
  linarith [hg v]

omit [DecidableEq V] in
theorem totalSupply_neg (q : V → ℤ) (hzero : ∑ v, (q v : ℝ) = 0) :
    (totalSupply (fun v => -q v) : ℝ) = totalSupply q := by
  have he : ∑ v, (q v : ℝ) =
      (totalSupply q : ℝ) - totalSupply (fun v => -q v) := by
    simp only [totalSupply, Nat.cast_sum, ← sum_sub_distrib]
    exact sum_congr rfl (fun v _ => int_positive_parts (q v))
  rw [hzero] at he
  linarith

omit [DecidableEq V] in
theorem augmentedGraph_sink_column (H : WeightedDiGraph V) (q : V → ℤ) :
    ∑ w, (augmentedGraph H q).c w sink = totalSupply (fun v => -q v) := by
  rw [Fintype.sum_sum_type]
  simp [augmentedGraph, sink, terminalNat, totalSupply, Nat.cast_sum]

def internalFlow (result : SolveResult V) (u v : V) : ℝ := result.flow (.inl u) (.inl v)

/-- Routing the full terminal supply gives the requested internal divergence,
by saturation of both explicit stars and conservation at every original vertex. -/
theorem internalFlow_repairs {G H : WeightedDiGraph V} (q : V → ℤ)
    (hzero : ∑ v, (q v : ℝ) = 0) {result : SolveResult V}
    (hc : SolveCorrect G (augmentedGraph H q) source sink result)
    (hvalue : (result.value : ℝ) = totalSupply q) :
    H.Feasible (internalFlow result) ∧ ∀ v, netOut (internalFlow result) v = (q v : ℝ) := by
  refine ⟨⟨fun u v => hc.feasible.1 (.inl u) (.inl v),
    fun u v => hc.feasible.2 (.inl u) (.inl v)⟩, ?_⟩
  have hsource : netOut result.flow source = (augmentedGraph H q).out {source} := by
    rw [hc.divergence, augmentedGraph_source_cut, ← hvalue]
    simp [source_ne_sink]
  have hsink : -netOut result.flow sink = ∑ w, (augmentedGraph H q).c w sink := by
    rw [hc.divergence, augmentedGraph_sink_column, totalSupply_neg q hzero, ← hvalue]
    simp [Ne.symm (source_ne_sink (V := V))]
  intro v
  have hfrom := saturated_row (augmentedGraph H q) result.flow hc.feasible source hsource (.inl v)
  have hto := saturated_column (augmentedGraph H q) result.flow hc.feasible sink hsink (.inl v)
  simp only [augmentedGraph, terminalNat, source, sink, ↓reduceIte] at hfrom hto
  change result.flow source (.inl v) = ((q v).toNat : ℝ) at hfrom
  change result.flow (.inl v) sink = ((-q v).toNat : ℝ) at hto
  have hv := hc.divergence (.inl v)
  simp only [source, sink, Sum.inl_ne_inr, ↓reduceIte, sub_self] at hv
  unfold netOut at hv
  rw [Fintype.sum_sum_type, Fin.sum_univ_two] at hv
  change netOut (internalFlow result) v +
    (result.flow (.inl v) source + result.flow (.inl v) sink) = 0 at hv
  rw [hc.feasible.1 source (.inl v), hfrom, hto] at hv
  have hparts := int_positive_parts (q v)
  linarith

def discrepancyRepairTree (st : State V) (q : V → ℤ) :
    DTree (Finset V) ℝ (Option (SolveResult V)) (repairBudget V (totalSupply q)) :=
  repairTree (augmentedState st q) (totalSupply q)

/-- Public exact conversion of an already proved integral real demand. -/
def integerDemand (q : V → ℝ) (v : V) : ℤ := ⌊q v⌋

omit [Fintype V] [DecidableEq V] in
theorem integerDemand_cast (q : V → ℝ) (hq : ∀ v, ∃ z : ℤ, q v = z) (v : V) :
    (integerDemand q v : ℝ) = q v := by
  obtain ⟨z, hz⟩ := hq v
  simp [integerDemand, hz]

omit [Fintype V] [DecidableEq V] in
theorem int_toNat_cast (z : ℤ) : (z.toNat : ℝ) = max (z : ℝ) 0 := by
  have h : (z.toNat : ℤ) = max z 0 := by omega
  exact_mod_cast h

omit [DecidableEq V] in
theorem totalSupply_integerDemand (q : V → ℝ) (hq : ∀ v, ∃ z : ℤ, q v = z) :
    (totalSupply (integerDemand q) : ℝ) = Repair.supply q := by
  simp only [totalSupply, Repair.supply, Nat.cast_sum]
  apply sum_congr rfl
  intro v _
  rw [int_toNat_cast, integerDemand_cast q hq v]

/-- Casting each original Nat cut answer preserves the exact same query tree. -/
def discrepancyRepairTreeNat (st : State V) (q : V → ℤ) :
    DTree (Finset V) ℕ (Option (SolveResult V)) (repairBudget V (totalSupply q)) :=
  DTree.mapAnswers (fun n : ℕ => (n : ℝ)) (discrepancyRepairTree st q)

theorem discrepancyRepairTreeNat_eval (read : Finset V → ℕ) (st : State V) (q : V → ℤ) :
    (discrepancyRepairTreeNat st q).eval read =
      (discrepancyRepairTree st q).eval (fun S => (read S : ℝ)) := by
  simp [discrepancyRepairTreeNat, DTree.eval, DTree.run_mapAnswers, Function.comp_def]

theorem discrepancyRepairTreeNat_cost (read : Finset V → ℕ) (st : State V) (q : V → ℤ) :
    (discrepancyRepairTreeNat st q).cost read =
      (discrepancyRepairTree st q).cost (fun S => (read S : ℝ)) := by
  simp [discrepancyRepairTreeNat, DTree.cost, DTree.run_mapAnswers, Function.comp_def]

/-- Public-state integral discrepancy repair. Its feasible witness is a
proof-only transshipment in the supplied graph; the tree receives only st and q. -/
theorem discrepancyRepairTree_correct (G H : WeightedDiGraph V) (st : State V)
    (hr : st.Realizes G H) (q : V → ℤ)
    (hint : ∀ u v, ∃ k : ℕ, H.c u v = k) (hcap : Repair.PairBounded H)
    (hRn : (totalSupply q : ℝ) ≤ (Fintype.card V : ℝ) ^ 2)
    (f : V → V → ℝ) (hf : H.Feasible f) (hdiv : ∀ v, netOut f v = (q v : ℝ)) :
    ∃ result, (discrepancyRepairTree st q).eval G.out = some result ∧
      H.Feasible (internalFlow result) ∧
      ∀ v, netOut (internalFlow result) v = (q v : ℝ) := by
  let network := augmentedState st q
  let full := augmentedGraph H q
  have hreal : network.Realizes G full := augmentedState_realizes hr q
  have hfullint : IntegralCap full := augmentedGraph_integral H q hint
  have hsource : full.out {source} ≤ (totalSupply q : ℝ) := (augmentedGraph_source_cut H q).le
  have hcost := repairProg_cost G full network hreal hfullint hcap (totalSupply q) hRn hsource
  let result := (repairProg network (totalSupply q)).eval G.out
  have hc : SolveCorrect G full source sink result :=
    repairProg_complete G full network hreal hfullint (totalSupply q) hsource
  have hv : (result.value : ℝ) = totalSupply q :=
    repairProg_value_eq G full network hreal hfullint (totalSupply q) hsource
      (liftFlow f q) (liftFlow_STFlow H q f hf hdiv) (liftFlow_source f q)
  have hzero : ∑ v, (q v : ℝ) = 0 := by
    simp only [← hdiv]
    exact WeightedDiGraph.sum_univ_netOut hf.1
  refine ⟨result, ?_, internalFlow_repairs q hzero hc hv⟩
  exact Prog.toDTree_eval G.out (repairProg network (totalSupply q))
    (repairBudget V (totalSupply q)) hcost



theorem repairProg_flow_integer (read : Finset V → ℝ) (st : NetworkState V) (R : ℕ) :
    ∀ u v, ∃ z : ℤ, ((repairProg st R).eval read).flow u v = z := by
  by_cases hR : R = 0
  · simp only [repairProg, hR, ↓reduceIte, Prog.eval_pure]
    intro u v
    refine ⟨0, ?_⟩
    simp [solveEmpty]
  · simpa only [repairProg, hR, ↓reduceIte, solveProg] using
      solveRun_flow_integer read source sink (Fintype.card (Node V)) st

/-- All information needed to continue with a second operational terminal
solve is exported from the actual repair result. No new graph learning is used. -/
theorem discrepancyRepairTree_continue (G H : WeightedDiGraph V) (st : State V)
    (hr : st.Realizes G H) (q : V → ℤ)
    (hint : ∀ u v, ∃ k : ℕ, H.c u v = k) (hcap : Repair.PairBounded H)
    (hRn : (totalSupply q : ℝ) ≤ (Fintype.card V : ℝ) ^ 2)
    (f : V → V → ℝ) (hf : H.Feasible f) (hdiv : ∀ v, netOut f v = (q v : ℝ)) :
    ∃ result, (discrepancyRepairTree st q).eval G.out = some result ∧
      ∃ hfeas : H.Feasible (internalFlow result),
        (∀ v, netOut (internalFlow result) v = (q v : ℝ)) ∧
        result.network.internal.Realizes G (Repair.residual H _ hfeas) ∧
        (∀ u v, ∃ k : ℕ, (Repair.residual H _ hfeas).c u v = k) ∧
        Repair.PairBounded (Repair.residual H _ hfeas) := by
  let network := augmentedState st q
  let full := augmentedGraph H q
  have hreal : network.Realizes G full := augmentedState_realizes hr q
  have hfullint : IntegralCap full := augmentedGraph_integral H q hint
  have hsource : full.out {source} ≤ (totalSupply q : ℝ) := (augmentedGraph_source_cut H q).le
  let result := (repairProg network (totalSupply q)).eval G.out
  have hc : SolveCorrect G full source sink result :=
    repairProg_complete G full network hreal hfullint (totalSupply q) hsource
  have hv : (result.value : ℝ) = totalSupply q :=
    repairProg_value_eq G full network hreal hfullint (totalSupply q) hsource
      (liftFlow f q) (liftFlow_STFlow H q f hf hdiv) (liftFlow_source f q)
  have hzero : ∑ v, (q v : ℝ) = 0 := by
    simp only [← hdiv]
    exact WeightedDiGraph.sum_univ_netOut hf.1
  obtain ⟨hfeas, hnet⟩ := internalFlow_repairs q hzero hc hv
  have hi := integralCap_residual_flow hfullint result.flow hc.feasible
    (repairProg_flow_integer G.out network (totalSupply q))
  refine ⟨result, ?_, hfeas, hnet, ?_, ?_, hcap.residual (internalFlow result) hfeas⟩
  · exact Prog.toDTree_eval G.out (repairProg network (totalSupply q)) _
      (repairProg_cost G full network hreal hfullint hcap (totalSupply q) hRn hsource)
  · exact hc.realizes.internal
  · intro u v
    exact hi (.inl u) (.inl v)


omit [DecidableEq V] in
theorem repairBound_mono {R S : ℕ} (hRS : R ≤ S) : repairBound V R ≤ repairBound V S := by
  have hcast : (R : ℝ) ≤ S := by exact_mod_cast hRS
  have hm := min_le_min hcast (le_refl (6 * (Fintype.card V : ℝ) ^ (2 / 3 : ℝ)))
  have hp := mul_le_mul_of_nonneg_left hm
    (by positivity : 0 ≤ 4 * (Fintype.card (Node V) : ℝ))
  have hs := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcast)
    (by positivity : 0 ≤ 7 * (Fintype.card V : ℝ))
  unfold repairBound
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  linarith

omit [DecidableEq V] in
theorem repairBudget_mono {R S : ℕ} (hRS : R ≤ S) : repairBudget V R ≤ repairBudget V S := by
  by_cases hR : R = 0
  · simp [repairBudget, hR]
  · have hS : S ≠ 0 := by omega
    simp only [repairBudget, hR, hS, ↓reduceIte]
    exact Nat.ceil_mono (repairBound_mono hRS)

/-- A fixed public cap for composition after adaptive preparation. Rcap is
chosen before answers; huge inconsistent reported demands can only truncate. -/
def cappedDiscrepancyRepairTree (st : State V) (q : V → ℤ) (Rcap : ℕ) :
    DTree (Finset V) ℝ (Option (SolveResult V)) (repairBudget V Rcap) :=
  (repairProg (augmentedState st q) (totalSupply q)).toDTree (repairBudget V Rcap)

theorem cappedDiscrepancyRepairTree_cost (read : Finset V → ℝ)
    (st : State V) (q : V → ℤ) (Rcap : ℕ) :
    (cappedDiscrepancyRepairTree st q Rcap).cost read ≤ repairBudget V Rcap :=
  DTree.cost_le _ _

/-- The honest-input numerical bound justifies nontruncation; the executable
budget itself is public and holds on every oracle without a supply assumption. -/
theorem cappedDiscrepancyRepairTree_continue (G H : WeightedDiGraph V) (st : State V)
    (hr : st.Realizes G H) (q : V → ℤ)
    (hint : ∀ u v, ∃ k : ℕ, H.c u v = k) (hcap : Repair.PairBounded H)
    (hRn : (totalSupply q : ℝ) ≤ (Fintype.card V : ℝ) ^ 2)
    (f : V → V → ℝ) (hf : H.Feasible f) (hdiv : ∀ v, netOut f v = (q v : ℝ))
    (Rcap : ℕ) (hRcap : totalSupply q ≤ Rcap) :
    ∃ result, (cappedDiscrepancyRepairTree st q Rcap).eval G.out = some result ∧
      ∃ hfeas : H.Feasible (internalFlow result),
        (∀ v, netOut (internalFlow result) v = (q v : ℝ)) ∧
        result.network.internal.Realizes G (Repair.residual H _ hfeas) ∧
        (∀ u v, ∃ k : ℕ, (Repair.residual H _ hfeas).c u v = k) ∧
        Repair.PairBounded (Repair.residual H _ hfeas) := by
  obtain ⟨result, he, hrest⟩ := discrepancyRepairTree_continue G H st hr q hint hcap hRn f hf hdiv
  have hc := repairProg_cost G (augmentedGraph H q) (augmentedState st q)
    (augmentedState_realizes hr q) (augmentedGraph_integral H q hint) hcap
    (totalSupply q) hRn (augmentedGraph_source_cut H q).le
  have hold := Prog.toDTree_eval G.out (repairProg (augmentedState st q) (totalSupply q)) _ hc
  have hnew := Prog.toDTree_eval G.out (repairProg (augmentedState st q) (totalSupply q))
    (repairBudget V Rcap) (hc.trans (repairBudget_mono hRcap))
  exact ⟨result, hnew.trans (hold.symm.trans he), hrest⟩

def cappedDiscrepancyRepairTreeNat (st : State V) (q : V → ℤ) (Rcap : ℕ) :
    DTree (Finset V) ℕ (Option (SolveResult V)) (repairBudget V Rcap) :=
  DTree.mapAnswers (fun n : ℕ => (n : ℝ)) (cappedDiscrepancyRepairTree st q Rcap)

theorem cappedDiscrepancyRepairTreeNat_eval (read : Finset V → ℕ)
    (st : State V) (q : V → ℤ) (Rcap : ℕ) :
    (cappedDiscrepancyRepairTreeNat st q Rcap).eval read =
      (cappedDiscrepancyRepairTree st q Rcap).eval (fun S => (read S : ℝ)) := by
  simp [cappedDiscrepancyRepairTreeNat, DTree.eval, DTree.run_mapAnswers, Function.comp_def]

theorem cappedDiscrepancyRepairTreeNat_cost (read : Finset V → ℕ)
    (st : State V) (q : V → ℤ) (Rcap : ℕ) :
    (cappedDiscrepancyRepairTreeNat st q Rcap).cost read ≤ repairBudget V Rcap :=
  DTree.cost_le _ _

/-- Restrict an actual full-network shore to the original vertices. -/
def originalShore (S : Finset (Node V)) : Finset V := univ.filter fun v => Sum.inl v ∈ S

@[simp] theorem mem_originalShore (S : Finset (Node V)) (v : V) :
    v ∈ originalShore S ↔ Sum.inl v ∈ S := by simp [originalShore]

@[simp] theorem originalShore_compl (S : Finset (Node V)) :
    originalShore Sᶜ = (originalShore S)ᶜ := by ext v; simp

/-- Whole-shore lift with both auxiliary terminal sides fixed. -/
def terminalLift (W : Finset V) : Finset (Node V) :=
  insert source (W.map (Function.Embedding.inl : V ↪ Node V))

omit [Fintype V] in
@[simp] theorem terminalLift_source (W : Finset V) : source ∈ terminalLift W := by
  simp [terminalLift]

omit [Fintype V] in
@[simp] theorem terminalLift_sink (W : Finset V) : sink ∉ terminalLift W := by
  simp [terminalLift, source, sink]

@[simp] theorem originalShore_terminalLift (W : Finset V) :
    originalShore (terminalLift W) = W := by
  ext v
  simp [terminalLift, source]

theorem sum_node_shore (S : Finset (Node V)) (f : Node V → ℝ) :
    ∑ x ∈ S, f x = (∑ v ∈ originalShore S, f (.inl v)) +
      ((if source ∈ S then f source else 0) + (if sink ∈ S then f sink else 0)) := by
  calc
    (∑ x ∈ S, f x) = ∑ x, if x ∈ S then f x else 0 := by simp
    _ = _ := by
      rw [Fintype.sum_sum_type, Fin.sum_univ_two]
      simp only [originalShore, sum_filter, source, sink]
      rfl

/-- Exact cut accounting for the explicit integral demand stars. -/
theorem augmentedGraph_out (H : WeightedDiGraph V) (q : V → ℤ)
    (S : Finset (Node V)) (hs : source ∈ S) (ht : sink ∉ S) :
    (augmentedGraph H q).out S = H.out (originalShore S) +
      (∑ v ∈ (originalShore S)ᶜ, ((q v).toNat : ℝ)) +
      ∑ v ∈ originalShore S, ((-q v).toNat : ℝ) := by
  rw [WeightedDiGraph.out, sum_node_shore]
  simp only [hs, ht, ↓reduceIte, add_zero]
  have ht' : (Sum.inr (1 : Fin 2) : Node V) ∉ S := ht
  have hrow (u : V) :
      (∑ y ∈ Sᶜ, (augmentedGraph H q).c (.inl u) y) =
        (∑ v ∈ (originalShore S)ᶜ, H.c u v) + ((-q u).toNat : ℝ) := by
    rw [sum_node_shore, originalShore_compl]
    simp [augmentedGraph, terminalNat, source, sink, ht']
  rw [sum_congr rfl (fun u _ => hrow u), sum_add_distrib, sum_node_shore,
    originalShore_compl]
  simp only [augmentedGraph, terminalNat, source, sink, ↓reduceIte,
    Nat.cast_zero, ite_self, add_zero]
  change H.out (originalShore S) + _ + _ = _
  ring

/-- A terminal solve requests public n-unit stars, but need not route n units. -/
def terminalDemand (s t : V) (M : ℕ) (v : V) : ℤ :=
  if v = s then (M : ℤ) else if v = t then -(M : ℤ) else 0

omit [Fintype V] in
theorem terminalDemand_pos (s t : V) (M : ℕ) (v : V) :
    (terminalDemand s t M v).toNat = if v = s then M else 0 := by
  unfold terminalDemand
  split_ifs <;> simp

omit [Fintype V] in
theorem terminalDemand_neg (s t : V) (hst : s ≠ t) (M : ℕ) (v : V) :
    (-terminalDemand s t M v).toNat = if v = t then M else 0 := by
  by_cases hvs : v = s
  · subst v
    simp [terminalDemand, hst]
  · simp only [terminalDemand, hvs, ↓reduceIte]
    split_ifs <;> simp

theorem totalSupply_terminalDemand (s t : V) (M : ℕ) :
    totalSupply (terminalDemand s t M) = M := by
  simp [totalSupply, terminalDemand_pos]

theorem terminalGraph_out (H : WeightedDiGraph V) (s t : V) (hst : s ≠ t)
    (M : ℕ) (S : Finset (Node V)) (hs : source ∈ S) (ht : sink ∉ S) :
    (augmentedGraph H (terminalDemand s t M)).out S =
      H.out (originalShore S) + (if s ∈ originalShore S then 0 else (M : ℝ)) +
        (if t ∈ originalShore S then (M : ℝ) else 0) := by
  rw [augmentedGraph_out H _ S hs ht]
  simp only [terminalDemand_pos, terminalDemand_neg s t hst, apply_ite, Nat.cast_zero]
  simp only [sum_ite_eq', mem_compl, ite_not]
  split_ifs <;> rfl

/-- Minimum full-network shores with value below the star capacity extract
an exact original terminal cut, without a full-supply feasibility premise. -/
theorem terminalSolve_extract (G H : WeightedDiGraph V) (s t : V) (hst : s ≠ t)
    (M : ℕ) (hsmall : H.out {s} < M) (result : SolveResult V)
    (hc : SolveCorrect G (augmentedGraph H (terminalDemand s t M)) source sink result) :
    s ∈ originalShore result.shore ∧ t ∉ originalShore result.shore ∧
      (result.value : ℝ) = H.out (originalShore result.shore) ∧
      ∀ W : Finset V, s ∈ W → t ∉ W →
        H.out (originalShore result.shore) ≤ H.out W := by
  have hlift (W : Finset V) (hs : s ∈ W) (ht : t ∉ W) :
      (augmentedGraph H (terminalDemand s t M)).out (terminalLift W) = H.out W := by
    rw [terminalGraph_out H s t hst M _ (terminalLift_source W) (terminalLift_sink W)]
    simp [hs, ht]
  have hmin := hc.min_cut (terminalLift {s}) (terminalLift_source _) (terminalLift_sink _)
  rw [hlift {s} (by simp) (by simpa using Ne.symm hst)] at hmin
  have hvalue : (augmentedGraph H (terminalDemand s t M)).out result.shore < M :=
    hmin.trans_lt hsmall
  have he := terminalGraph_out H s t hst M result.shore hc.source_mem hc.target_notMem
  have hnonneg := H.out_nonneg (originalShore result.shore)
  have hs : s ∈ originalShore result.shore := by
    by_contra hs
    rw [he, ite_eq_right hs] at hvalue
    split_ifs at hvalue <;> linarith [Nat.cast_nonneg (α := ℝ) M]
  have ht : t ∉ originalShore result.shore := by
    intro ht
    rw [he, ite_eq_left hs, ite_eq_left ht] at hvalue
    linarith
  simp only [hs, ht, ↓reduceIte, add_zero] at he
  refine ⟨hs, ht, hc.value_eq_cut.trans he, ?_⟩
  intro W hWs hWt
  have h := hc.min_cut (terminalLift W) (terminalLift_source _) (terminalLift_sink _)
  simpa only [he, hlift W hWs hWt] using h

structure TerminalResult (V : Type) where
  shore : Finset V
  value : ℝ

/-- The second solve ends with the requested original outgoing-cut query. -/
def terminalProg (st : State V) (s t : V) : Prog (Finset V) ℝ (TerminalResult V) :=
  (repairProg (augmentedState st (terminalDemand s t (Fintype.card V)))
    (Fintype.card V)).bind fun result =>
      (Prog.ask (originalShore result.shore)).map fun value =>
        ⟨originalShore result.shore, value⟩

def terminalTree (st : State V) (s t : V) :
    DTree (Finset V) ℝ (Option (TerminalResult V)) (repairBudget V (Fintype.card V) + 1) :=
  (terminalProg st s t).toDTree (repairBudget V (Fintype.card V) + 1)

theorem terminalProg_cost (G H : WeightedDiGraph V) (st : State V)
    (hr : st.Realizes G H) (hint : ∀ u v, ∃ k : ℕ, H.c u v = k)
    (hcap : Repair.PairBounded H) (s t : V) :
    (terminalProg st s t).cost G.out ≤ repairBudget V (Fintype.card V) + 1 := by
  have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨s⟩
  have hRn : (Fintype.card V : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
    have hnone : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
    nlinarith
  have hc := repairProg_cost G (augmentedGraph H (terminalDemand s t (Fintype.card V)))
    _ (augmentedState_realizes hr _) (augmentedGraph_integral H _ hint)
    hcap (Fintype.card V) hRn
    (by rw [augmentedGraph_source_cut, totalSupply_terminalDemand])
  simpa only [terminalProg, Prog.cost_bind, Prog.cost_map, Prog.cost_ask] using
    Nat.add_le_add_right hc 1

/-- The public final query returns the original value; cut equivalence is
used only to transfer the minimizing shore from the restored representation. -/
theorem terminalProg_correct (G H : WeightedDiGraph V) (st : State V)
    (hr : st.Realizes G H) (hint : ∀ u v, ∃ k : ℕ, H.c u v = k)
    (hequiv : ∀ W : Finset V, H.out W = G.out W)
    (s t : V) (hst : s ≠ t) (hsmall : G.out {s} < Fintype.card V) :
    let result := (terminalProg st s t).eval G.out
    s ∈ result.shore ∧ t ∉ result.shore ∧ result.value = G.out result.shore ∧
      ∀ W : Finset V, s ∈ W → t ∉ W → G.out result.shore ≤ G.out W := by
  have hc := repairProg_complete G (augmentedGraph H (terminalDemand s t (Fintype.card V)))
    _ (augmentedState_realizes hr _) (augmentedGraph_integral H _ hint)
    (Fintype.card V) (by rw [augmentedGraph_source_cut, totalSupply_terminalDemand])
  obtain ⟨hs, ht, _, hmin⟩ := terminalSolve_extract G H s t hst (Fintype.card V)
    (by simpa only [hequiv] using hsmall) _ hc
  simp only [terminalProg, Prog.eval_bind, Prog.eval_map, Prog.eval_ask]
  refine ⟨hs, ht, True.intro, ?_⟩
  intro W hWs hWt
  simpa only [hequiv] using hmin W hWs hWt

theorem terminalTree_cost (read : Finset V → ℝ) (st : State V) (s t : V) :
    (terminalTree st s t).cost read ≤ repairBudget V (Fintype.card V) + 1 :=
  DTree.cost_le _ _

theorem terminalTree_correct (G H : WeightedDiGraph V) (st : State V)
    (hr : st.Realizes G H) (hint : ∀ u v, ∃ k : ℕ, H.c u v = k)
    (hcap : Repair.PairBounded H) (hequiv : ∀ W : Finset V, H.out W = G.out W)
    (s t : V) (hst : s ≠ t) (hsmall : G.out {s} < Fintype.card V) :
    ∃ result, (terminalTree st s t).eval G.out = some result ∧
      s ∈ result.shore ∧ t ∉ result.shore ∧ result.value = G.out result.shore ∧
      ∀ W : Finset V, s ∈ W → t ∉ W → G.out result.shore ≤ G.out W := by
  refine ⟨(terminalProg st s t).eval G.out, ?_,
    terminalProg_correct G H st hr hint hequiv s t hst hsmall⟩
  exact Prog.toDTree_eval G.out (terminalProg st s t) _
    (terminalProg_cost G H st hr hint hcap s t)


/-- The strict singleton bound for an actual unit-capacity input graph. -/
theorem unit_singleton_lt_card (G : WeightedDiGraph V)
    (hunit : ∀ u v, G.c u v ≤ 1) (s : V) : G.out {s} < Fintype.card V := by
  have h : (∑ v, G.c s v) < ∑ _v : V, (1 : ℝ) :=
    sum_lt_sum (fun v _ => hunit s v) ⟨s, mem_univ s, by simp [G.diag]⟩
  simpa only [WeightedDiGraph.out_singleton, WeightedDiGraph.outdeg, sum_const,
    card_univ, nsmul_eq_mul, mul_one] using h

/-- Nat original answers use the same capped tree after an exact cast. -/
def terminalTreeNat (st : State V) (s t : V) :
    DTree (Finset V) ℕ (Option (TerminalResult V)) (repairBudget V (Fintype.card V) + 1) :=
  DTree.mapAnswers (fun n : ℕ => (n : ℝ)) (terminalTree st s t)

theorem terminalTreeNat_eval (read : Finset V → ℕ) (st : State V) (s t : V) :
    (terminalTreeNat st s t).eval read =
      (terminalTree st s t).eval (fun S => (read S : ℝ)) := by
  simp [terminalTreeNat, DTree.eval, DTree.run_mapAnswers, Function.comp_def]

theorem terminalTreeNat_cost (read : Finset V → ℕ) (st : State V) (s t : V) :
    (terminalTreeNat st s t).cost read ≤ repairBudget V (Fintype.card V) + 1 :=
  DTree.cost_le _ _

theorem terminalTree_unit_correct (G H : WeightedDiGraph V) (st : State V)
    (hr : st.Realizes G H) (hint : ∀ u v, ∃ k : ℕ, H.c u v = k)
    (hcap : Repair.PairBounded H) (hequiv : ∀ W : Finset V, H.out W = G.out W)
    (hunit : ∀ u v, G.c u v ≤ 1) (s t : V) (hst : s ≠ t) :
    ∃ result, (terminalTree st s t).eval G.out = some result ∧
      s ∈ result.shore ∧ t ∉ result.shore ∧ result.value = G.out result.shore ∧
      ∀ W : Finset V, s ∈ W → t ∉ W → G.out result.shore ≤ G.out W :=
  terminalTree_correct G H st hr hint hcap hequiv s t hst (unit_singleton_lt_card G hunit s)

end
end CutQueryComplexity.DirectedUnitST.Blocking

#print axioms CutQueryComplexity.DirectedUnitST.Blocking.repairProg_complete
#print axioms CutQueryComplexity.DirectedUnitST.Blocking.repairProg_cost
#print axioms CutQueryComplexity.DirectedUnitST.Blocking.repairTree_correct
#print axioms CutQueryComplexity.DirectedUnitST.Blocking.repairProg_value_eq
#print axioms CutQueryComplexity.DirectedUnitST.Blocking.augmentedState_realizes
#print axioms CutQueryComplexity.DirectedUnitST.Blocking.discrepancyRepairTree_correct

#print axioms CutQueryComplexity.DirectedUnitST.Blocking.terminalSolve_extract
#print axioms CutQueryComplexity.DirectedUnitST.Blocking.terminalTree_correct

#print axioms CutQueryComplexity.DirectedUnitST.Blocking.terminalTree_unit_correct

#print axioms CutQueryComplexity.DirectedUnitST.Blocking.discrepancyRepairTree_continue

#print axioms CutQueryComplexity.DirectedUnitST.Blocking.cappedDiscrepancyRepairTree_continue
#print axioms CutQueryComplexity.DirectedUnitST.Blocking.cappedDiscrepancyRepairTreeNat_eval
#print axioms CutQueryComplexity.DirectedUnitST.Blocking.terminalTreeNat_cost
