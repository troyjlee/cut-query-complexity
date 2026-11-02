import CutQueryComplexity.StarContraction2022.Certificates.Semantics
import CutQueryComplexity.StarContraction2022.Common.Quotient
import CutQueryComplexity.Graph.EdgeSum

/-! # Original-endpoint state and least-layer insertion

The public state stores individual original edges. Quotient capacities are
their sums, not the Boolean support of the union. Each layer has a construction
trace joining different components; different layers can use parallel quotient
edges. The hidden input occurs only in correctness predicates.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Certificates

noncomputable section
open scoped Classical

variable {V Q : Type} [Fintype V] [DecidableEq V] [Fintype Q] [DecidableEq Q]

/-- Individual original endpoints crossing the public quotient. -/
abbrev OriginalEdge (π : PublicQuotient V Q) :=
  {e : V × V // π.map e.1 ≠ π.map e.2}

namespace OriginalEdge

variable {π : PublicQuotient V Q}

def originalIndex (e : OriginalEdge π) : WeightedGraph.EdgeIndex V :=
  ⟨e.val, fun h => e.property (congrArg π.map h)⟩

def quotientIndex (e : OriginalEdge π) : WeightedGraph.EdgeIndex Q :=
  ⟨(π.map e.val.1, π.map e.val.2), e.property⟩

def graph (e : OriginalEdge π) : WeightedGraph V :=
  WeightedGraph.edgeGraph e.originalIndex 1 zero_le_one

def quotientGraph (e : OriginalEdge π) : _root_.SimpleGraph Q :=
  _root_.SimpleGraph.edge (π.map e.val.1) (π.map e.val.2)

end OriginalEdge

private theorem weighted_ext_cut {A B : WeightedGraph V}
    (h : ∀ S, A.cut S = B.cut S) : A = B := by
  ext u v
  by_cases huv : u = v
  · subst v
    simp [A.diag, B.diag]
  · have hd : Disjoint ({u} : Finset V) {v} := by simpa using huv
    have ha := A.cross_eq_three_cuts hd
    have hb := B.cross_eq_three_cuts hd
    simp only [WeightedGraph.cross, Finset.sum_singleton] at ha hb
    rw [h {u}, h {v}, h ({u} ∪ {v})] at ha
    exact ha.trans hb.symm

private theorem unitEdge_eq (e : WeightedGraph.EdgeIndex V) :
    WeightedGraph.edgeGraph e 1 zero_le_one =
      SimpleGraph.toWeighted (_root_.SimpleGraph.edge e.val.1 e.val.2) := by
  rcases e with ⟨⟨a, b⟩, hab⟩
  change a ≠ b at hab
  ext u v
  by_cases hua : u = a <;> by_cases hub : u = b <;>
    by_cases hva : v = a <;> by_cases hvb : v = b <;>
    simp_all [WeightedGraph.edgeGraph, SimpleGraph.toWeighted_w,
      _root_.SimpleGraph.edge_adj]
  all_goals exact hab (by symm; assumption)

theorem OriginalEdge.integral {π : PublicQuotient V Q} (e : OriginalEdge π) :
    e.graph.IsIntegral := by
  rw [OriginalEdge.graph, unitEdge_eq]
  exact integral_toWeighted _

/-- One original edge becomes one quotient edge, even when other edges have
the same quotient endpoints. -/
theorem OriginalEdge.contract_graph {π : PublicQuotient V Q} (e : OriginalEdge π) :
    π.graph e.graph = SimpleGraph.toWeighted e.quotientGraph := by
  have he : WeightedGraph.edgeGraph e.quotientIndex 1 zero_le_one =
      SimpleGraph.toWeighted e.quotientGraph := by
    convert unitEdge_eq e.quotientIndex using 1
    ext u v
    simp only [SimpleGraph.toWeighted_w, OriginalEdge.quotientGraph,
      OriginalEdge.quotientIndex]
  rw [← he]
  apply weighted_ext_cut
  intro S
  rw [π.cut_graph, OriginalEdge.graph, WeightedGraph.cut_edgeGraph,
    WeightedGraph.cut_edgeGraph]
  simp only [OriginalEdge.originalIndex, OriginalEdge.quotientIndex,
    PublicQuotient.mem_lift]
  rfl

theorem OriginalEdge.self_weight {π : PublicQuotient V Q} (e : OriginalEdge π) :
    e.graph.w e.val.1 e.val.2 = 1 := by
  have hrev : (e.val.2, e.val.1) ≠ e.val := by
    intro hh
    exact e.originalIndex.property (congrArg Prod.fst hh).symm
  simp [OriginalEdge.graph, OriginalEdge.originalIndex, WeightedGraph.edgeGraph, hrev]

/-- Positive integral residual capacity licenses one original edge copy. -/
theorem OriginalEdge.subgraph_of_positive {π : PublicQuotient V Q}
    (e : OriginalEdge π) (G : WeightedGraph V) (hG : G.IsIntegral)
    (hp : 0 < G.w e.val.1 e.val.2) : e.graph.IsSubgraph G := by
  obtain ⟨k, hk⟩ := hG e.val.1 e.val.2
  have hkpos : 0 < k := by exact_mod_cast (hk ▸ hp)
  have hunit : 1 ≤ G.w e.val.1 e.val.2 := by
    rw [hk]
    exact_mod_cast (Nat.succ_le_of_lt hkpos)
  rw [OriginalEdge.graph, unitEdge_eq]
  intro u v
  rw [SimpleGraph.toWeighted_w]
  split_ifs with h
  · rcases (_root_.SimpleGraph.edge_adj ..).mp h with ⟨hh | hh, _⟩
    · rcases hh with ⟨rfl, rfl⟩; exact hunit
    · rcases hh with ⟨rfl, rfl⟩
      change 1 ≤ G.w e.val.2 e.val.1
      rw [G.symm]
      exact hunit
  · exact G.nonneg _ _

private theorem contract_add (π : PublicQuotient V Q) (A B : WeightedGraph V) :
    π.graph (A.add B) = (π.graph A).add (π.graph B) := by
  ext u v
  by_cases huv : u = v
  · subst v; simp [WeightedGraph.diag]
  · simp [PublicQuotient.graph, WeightedGraph.contract, huv,
      WeightedGraph.cross, Finset.sum_add_distrib]

private theorem contract_zero (π : PublicQuotient V Q) :
    π.graph (0 : WeightedGraph V) = 0 := by
  ext u v
  simp [PublicQuotient.graph, WeightedGraph.contract, WeightedGraph.cross]

private theorem contract_subgraph (π : PublicQuotient V Q) {A B : WeightedGraph V}
    (h : A.IsSubgraph B) : (π.graph A).IsSubgraph (π.graph B) := by
  intro u v
  by_cases huv : u = v
  · subst v; simp [WeightedGraph.diag]
  · change (if u = v then 0 else A.cross _ _) ≤ (if u = v then 0 else B.cross _ _)
    rw [if_neg huv, if_neg huv]
    exact Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => h a b))

private theorem cut_finiteSum {I : Type} (s : Finset I) (F : I → WeightedGraph V)
    (S : Finset V) :
    (WeightedGraph.finiteSum s F).cut S = ∑ i ∈ s, (F i).cut S := by
  simp only [WeightedGraph.cut, WeightedGraph.finiteSum]
  calc
    _ = ∑ u ∈ S, ∑ i ∈ s, ∑ v ∈ Sᶜ, (F i).w u v :=
      Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

private theorem edgeMass_finiteSum {I : Type} (s : Finset I) (F : I → WeightedGraph V) :
    (WeightedGraph.finiteSum s F).edgeMass = ∑ i ∈ s, (F i).edgeMass := by
  simp only [WeightedGraph.edgeMass, WeightedGraph.finiteSum]
  have he : (∑ u, ∑ v, ∑ i ∈ s, (F i).w u v) =
      ∑ i ∈ s, ∑ u, ∑ v, (F i).w u v := by
    calc
      _ = ∑ u, ∑ i ∈ s, ∑ v, (F i).w u v :=
        Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
      _ = _ := Finset.sum_comm
  rw [he, Finset.sum_div]

private theorem weighted_sup_edge (F : _root_.SimpleGraph Q) {a b : Q}
    (hn : ¬F.Adj a b) :
    SimpleGraph.toWeighted (F ⊔ _root_.SimpleGraph.edge a b) =
      (SimpleGraph.toWeighted F).add
        (SimpleGraph.toWeighted (_root_.SimpleGraph.edge a b)) := by
  ext u v
  have hd : ¬(F.Adj u v ∧ (_root_.SimpleGraph.edge a b).Adj u v) := by
    rintro ⟨hF, he⟩
    rcases (_root_.SimpleGraph.edge_adj ..).mp he with ⟨h | h, _⟩
    · rcases h with ⟨rfl, rfl⟩; exact hn hF
    · rcases h with ⟨rfl, rfl⟩; exact hn hF.symm
  by_cases hf : F.Adj u v <;> by_cases he : (_root_.SimpleGraph.edge a b).Adj u v <;>
    simp_all [SimpleGraph.toWeighted_w, _root_.SimpleGraph.sup_adj]

/-- The quotient forest support built by a list of original edge insertions. -/
def quotientSupport {π : PublicQuotient V Q} : List (OriginalEdge π) → _root_.SimpleGraph Q
  | [] => ⊥
  | e :: es => quotientSupport es ⊔ e.quotientGraph

/-- The original unit capacities; parallel quotient edges are never collapsed. -/
def originalSum {π : PublicQuotient V Q} : List (OriginalEdge π) → WeightedGraph V
  | [] => 0
  | e :: es => (originalSum es).add e.graph

/-- A finite trace of genuine component-joining operations on the quotient. -/
inductive ForestTrace {π : PublicQuotient V Q} : List (OriginalEdge π) → Prop
  | nil : ForestTrace []
  | cons {es : List (OriginalEdge π)} (e : OriginalEdge π) (h : ForestTrace es)
      (hn : ¬(quotientSupport es).Reachable (π.map e.val.1) (π.map e.val.2)) :
      ForestTrace (e :: es)

theorem originalSum_integral {π : PublicQuotient V Q} (es : List (OriginalEdge π)) :
    (originalSum es).IsIntegral := by
  induction es with
  | nil => exact WeightedGraph.integral_zero
  | cons e es ih => exact ih.add e.integral

theorem originalSum_contains {π : PublicQuotient V Q} (es : List (OriginalEdge π))
    {e : OriginalEdge π} (he : e ∈ es) : e.graph.IsSubgraph (originalSum es) := by
  induction es with
  | nil => simp at he
  | cons f es ih =>
      rcases List.mem_cons.mp he with rfl | he
      · intro u v
        change e.graph.w u v ≤ (originalSum es).w u v + e.graph.w u v
        linarith [(originalSum es).nonneg u v]
      · intro u v
        have hh := ih he u v
        change e.graph.w u v ≤ (originalSum es).w u v + f.graph.w u v
        linarith [f.graph.nonneg u v]

theorem ForestTrace.acyclic {π : PublicQuotient V Q} {es : List (OriginalEdge π)}
    (h : ForestTrace es) : (quotientSupport es).IsAcyclic := by
  induction h with
  | nil => exact _root_.SimpleGraph.isAcyclic_bot
  | cons e h hn ih => exact ih.sup_edge_of_not_reachable hn

theorem ForestTrace.contract_eq {π : PublicQuotient V Q} {es : List (OriginalEdge π)}
    (h : ForestTrace es) :
    π.graph (originalSum es) = SimpleGraph.toWeighted (quotientSupport es) := by
  induction h with
  | nil =>
      rw [originalSum, contract_zero]
      ext u v
      simp [quotientSupport, SimpleGraph.toWeighted_w]
  | cons e h hn ih =>
      rw [originalSum, contract_add, ih, e.contract_graph]
      exact (weighted_sup_edge _ (fun he => hn he.reachable)).symm

theorem ForestTrace.card_edges {π : PublicQuotient V Q} {es : List (OriginalEdge π)}
    (h : ForestTrace es) : (quotientSupport es).edgeFinset.card = es.length := by
  induction h with
  | nil =>
      apply Finset.card_eq_zero.mpr
      ext x
      simp only [_root_.SimpleGraph.mem_edgeFinset]
      simp [quotientSupport]
  | @cons es e h hn ih =>
      calc
        (quotientSupport (e :: es)).edgeFinset.card =
            (quotientSupport es).edgeFinset.card + 1 := by
          convert (quotientSupport es).card_edgeFinset_sup_edge
            (fun he => hn he.reachable) e.property using 1
          apply congrArg Finset.card
          ext x
          simp only [_root_.SimpleGraph.mem_edgeFinset]
          rfl
        _ = (e :: es).length := by rw [ih, List.length_cons]

/-- An explicit endpoint list with a checked public forest construction trace. -/
structure EndpointForest (π : PublicQuotient V Q) where
  edges : List (OriginalEdge π)
  trace : ForestTrace edges

namespace EndpointForest

variable {π : PublicQuotient V Q}

def empty : EndpointForest π := ⟨[], .nil⟩

def quotient (F : EndpointForest π) : _root_.SimpleGraph Q := quotientSupport F.edges

def original (F : EndpointForest π) : WeightedGraph V := originalSum F.edges

def extend (F : EndpointForest π) (e : OriginalEdge π)
    (hn : ¬F.quotient.Reachable (π.map e.val.1) (π.map e.val.2)) : EndpointForest π :=
  ⟨e :: F.edges, .cons e F.trace hn⟩

@[simp] theorem extend_quotient (F : EndpointForest π) (e : OriginalEdge π) (hn) :
    (F.extend e hn).quotient = F.quotient ⊔ e.quotientGraph := rfl

@[simp] theorem extend_original (F : EndpointForest π) (e : OriginalEdge π) (hn) :
    (F.extend e hn).original = F.original.add e.graph := rfl

theorem acyclic (F : EndpointForest π) : F.quotient.IsAcyclic := F.trace.acyclic

theorem integral (F : EndpointForest π) : F.original.IsIntegral := originalSum_integral _

theorem contract_eq (F : EndpointForest π) :
    π.graph F.original = SimpleGraph.toWeighted F.quotient := F.trace.contract_eq

theorem card_edges (F : EndpointForest π) : F.quotient.edgeFinset.card = F.edges.length :=
  F.trace.card_edges

theorem length_le (F : EndpointForest π) : F.edges.length ≤ Fintype.card Q - 1 := by
  rw [← F.card_edges]
  exact forest_card_le _ F.acyclic

end EndpointForest

/-- Public data only: a forest array, retired original vertices, and failure status. -/
structure ParallelState (π : PublicQuotient V Q) (r : ℕ) where
  forests : Fin r → EndpointForest π
  inactive : Finset V
  failed : Bool

namespace ParallelState

variable {π : PublicQuotient V Q} {r : ℕ}

def initial (π : PublicQuotient V Q) (r : ℕ) : ParallelState π r :=
  ⟨fun _ => EndpointForest.empty, ∅, false⟩

def usedGraph (s : ParallelState π r) : WeightedGraph V :=
  WeightedGraph.finiteSum Finset.univ (fun i => (s.forests i).original)

def edgeCount (s : ParallelState π r) : ℕ := ∑ i, (s.forests i).edges.length

/-- The output retains the sum of layer capacities, including parallel pairs. -/
def quotientGraph (s : ParallelState π r) : WeightedGraph Q :=
  WeightedGraph.finiteSum Finset.univ (fun i => SimpleGraph.toWeighted (s.forests i).quotient)

/-- Later layers refine earlier component partitions. -/
def Laminar (s : ParallelState π r) : Prop :=
  ∀ i j : Fin r, i ≤ j → ∀ u v,
    (s.forests j).quotient.Reachable u v → (s.forests i).quotient.Reachable u v

theorem initial_laminar : (initial π r).Laminar := by
  intro i j hij u v huv
  exact huv

theorem usedGraph_integral (s : ParallelState π r) : s.usedGraph.IsIntegral := by
  intro u v
  choose k hk using fun i : Fin r => (s.forests i).integral u v
  refine ⟨∑ i, k i, ?_⟩
  simp only [usedGraph, WeightedGraph.finiteSum]
  simp_rw [hk]
  simp

theorem usedGraph_contains (s : ParallelState π r) (i : Fin r)
    {e : OriginalEdge π} (he : e ∈ (s.forests i).edges) :
    e.graph.IsSubgraph s.usedGraph := by
  intro u v
  apply (originalSum_contains _ he u v).trans
  exact Finset.single_le_sum
    (fun j _ => (s.forests j).original.nonneg u v) (Finset.mem_univ i)

theorem usedGraph_contract (s : ParallelState π r) :
    π.graph s.usedGraph = s.quotientGraph := by
  apply weighted_ext_cut
  intro S
  rw [π.cut_graph, usedGraph, quotientGraph, cut_finiteSum, cut_finiteSum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← (s.forests i).contract_eq, π.cut_graph]

theorem quotientGraph_integral (s : ParallelState π r) : s.quotientGraph.IsIntegral := by
  rw [← s.usedGraph_contract]
  exact π.integral_graph _ s.usedGraph_integral

theorem quotientGraph_edgeMass (s : ParallelState π r) :
    s.quotientGraph.edgeMass = (s.edgeCount : ℝ) := by
  rw [quotientGraph, edgeMass_finiteSum]
  simp only [edgeMass_toWeighted, EndpointForest.card_edges, edgeCount, Nat.cast_sum]

theorem quotientGraph_subgraph (s : ParallelState π r) (G : WeightedGraph V)
    (hs : s.usedGraph.IsSubgraph G) : s.quotientGraph.IsSubgraph (π.graph G) := by
  rw [← s.usedGraph_contract]
  exact contract_subgraph π hs

private theorem forestSum_weights (Fs : List (_root_.SimpleGraph Q)) (u v : Q) :
    (forestSum Fs).w u v = (Fs.map fun F => (SimpleGraph.toWeighted F).w u v).sum := by
  induction Fs with
  | nil => rfl
  | cons F Fs ih => simp [forestSum, ih]

def layerList (s : ParallelState π r) : List (_root_.SimpleGraph Q) :=
  List.ofFn (fun i => (s.forests i).quotient)

theorem quotientGraph_eq_forestSum (s : ParallelState π r) :
    s.quotientGraph = forestSum s.layerList := by
  ext u v
  simp [quotientGraph, WeightedGraph.finiteSum, forestSum_weights, layerList,
    List.map_ofFn, List.sum_ofFn]

/-- Completeness is proved for the actual array of forests, in residual order. -/
def Complete (s : ParallelState π r) (G : WeightedGraph V) : Prop :=
  ResidualForestChain (π.graph G) s.layerList

theorem complete_certificate (s : ParallelState π r) (G : WeightedGraph V)
    (hG : G.IsIntegral) (hs : s.Complete G) :
    IsThresholdCertificate r (π.graph G) s.quotientGraph := by
  rw [s.quotientGraph_eq_forestSum]
  have h := residualForestChain_certificate (π.graph G) (π.integral_graph G hG) s.layerList hs
  simpa only [layerList, List.length_ofFn] using h

theorem edgeCount_le (s : ParallelState π r) :
    s.edgeCount ≤ r * (Fintype.card Q - 1) := by
  calc
    s.edgeCount ≤ ∑ _ : Fin r, (Fintype.card Q - 1) := by
      unfold edgeCount
      exact Finset.sum_le_sum (fun i _ => (s.forests i).length_le)
    _ = _ := by simp

/-- Insert into one publicly selected layer after testing actual connectivity. -/
def insertAt (s : ParallelState π r) (i : Fin r) (e : OriginalEdge π)
    (hn : ¬(s.forests i).quotient.Reachable (π.map e.val.1) (π.map e.val.2)) :
    ParallelState π r :=
  { s with forests := Function.update s.forests i ((s.forests i).extend e hn) }

@[simp] theorem insertAt_inactive (s : ParallelState π r) (i : Fin r)
    (e : OriginalEdge π) (hn) : (s.insertAt i e hn).inactive = s.inactive := rfl

theorem insertAt_usedGraph (s : ParallelState π r) (i : Fin r)
    (e : OriginalEdge π) (hn) :
    (s.insertAt i e hn).usedGraph = s.usedGraph.add e.graph := by
  ext u v
  have hf (j : Fin r) :
      ((s.insertAt i e hn).forests j).original.w u v =
        (s.forests j).original.w u v + if j = i then e.graph.w u v else 0 := by
    by_cases hji : j = i
    · subst j; simp [insertAt]
    · simp [insertAt, hji]
  simp only [usedGraph, WeightedGraph.finiteSum, WeightedGraph.add_w]
  simp_rw [hf]
  rw [Finset.sum_add_distrib]
  simp

theorem insertAt_edgeCount (s : ParallelState π r) (i : Fin r)
    (e : OriginalEdge π) (hn) :
    (s.insertAt i e hn).edgeCount = s.edgeCount + 1 := by
  have hf (j : Fin r) : ((s.insertAt i e hn).forests j).edges.length =
      (s.forests j).edges.length + if j = i then 1 else 0 := by
    by_cases hji : j = i
    · subst j; simp [insertAt, EndpointForest.extend]
    · simp [insertAt, hji]
  simp only [edgeCount]
  simp_rw [hf]
  rw [Finset.sum_add_distrib]
  simp

theorem insertAt_reachable (s : ParallelState π r) (i : Fin r)
    (e : OriginalEdge π) (hn) (j : Fin r) {u v : Q}
    (h : (s.forests j).quotient.Reachable u v) :
    ((s.insertAt i e hn).forests j).quotient.Reachable u v := by
  by_cases hji : j = i
  · subst j
    simpa [insertAt] using h.mono
      (show (s.forests i).quotient ≤ (s.forests i).quotient ⊔ e.quotientGraph from le_sup_left)
  · simpa [insertAt, hji] using h

private theorem reachable_sup_edge {F H : _root_.SimpleGraph Q} {a b : Q}
    (hFH : ∀ u v, F.Reachable u v → H.Reachable u v) (hab : H.Reachable a b)
    {u v : Q} (h : (F ⊔ _root_.SimpleGraph.edge a b).Reachable u v) :
    H.Reachable u v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact .rfl
  | @cons u w v huw p ih =>
      have hstep : H.Reachable u w := by
        rcases huw with hF | he
        · exact hFH _ _ hF.reachable
        · rcases (_root_.SimpleGraph.edge_adj ..).mp he with ⟨h | h, _⟩
          · rcases h with ⟨rfl, rfl⟩; exact hab
          · rcases h with ⟨rfl, rfl⟩; exact hab.symm
      exact hstep.trans ih

/-- Inserting into the first layer that admits an edge preserves laminarity. -/
theorem insertAt_laminar (s : ParallelState π r) (hs : s.Laminar) (i : Fin r)
    (e : OriginalEdge π) (hn)
    (hfirst : ∀ j : Fin r, j < i →
      (s.forests j).quotient.Reachable (π.map e.val.1) (π.map e.val.2)) :
    (s.insertAt i e hn).Laminar := by
  intro j k hjk u v hkv
  by_cases hki : k = i
  · subst k
    by_cases hji : j = i
    · subst j; exact hkv
    · have hji' : j < i := lt_of_le_of_ne hjk hji
      have hnew : ((s.forests i).quotient ⊔ e.quotientGraph).Reachable u v := by
        simpa [insertAt] using hkv
      have hold := reachable_sup_edge (fun a b h => hs j i hjk a b h)
        (hfirst j hji') hnew
      simpa [insertAt, hji] using hold
  · have hold : (s.forests k).quotient.Reachable u v := by
      simpa [insertAt, hki] using hkv
    exact s.insertAt_reachable i e hn j (hs j k hjk u v hold)

def available (s : ParallelState π r) (e : OriginalEdge π) : Finset (Fin r) :=
  Finset.univ.filter fun i =>
    ¬(s.forests i).quotient.Reachable (π.map e.val.1) (π.map e.val.2)

def firstIndex (s : ParallelState π r) (e : OriginalEdge π)
    (h : (s.available e).Nonempty) : Fin r := (s.available e).min' h

theorem firstIndex_available (s : ParallelState π r) (e : OriginalEdge π)
    (h : (s.available e).Nonempty) :
    ¬(s.forests (s.firstIndex e h)).quotient.Reachable (π.map e.val.1) (π.map e.val.2) := by
  have hm := (s.available e).min'_mem h
  simpa [available, firstIndex] using hm

theorem before_firstIndex (s : ParallelState π r) (e : OriginalEdge π)
    (h : (s.available e).Nonempty) (j : Fin r) (hj : j < s.firstIndex e h) :
    (s.forests j).quotient.Reachable (π.map e.val.1) (π.map e.val.2) := by
  by_contra hnot
  have hm : j ∈ s.available e := by simp [available, hnot]
  have hle : s.firstIndex e h ≤ j := (s.available e).min'_le j hm
  exact (not_le_of_gt hj) hle

def insertFirst (s : ParallelState π r) (e : OriginalEdge π) : Option (ParallelState π r) :=
  if h : (s.available e).Nonempty then
    some (s.insertAt (s.firstIndex e h) e (s.firstIndex_available e h))
  else none

theorem insertFirst_laminar (s : ParallelState π r) (hs : s.Laminar)
    (e : OriginalEdge π) {t : ParallelState π r} (ht : s.insertFirst e = some t) :
    t.Laminar := by
  unfold insertFirst at ht
  split at ht
  next h =>
    cases Option.some.inj ht
    exact s.insertAt_laminar hs _ e _ (s.before_firstIndex e h)
  next h => cases ht

theorem insertFirst_edgeCount (s : ParallelState π r) (e : OriginalEdge π)
    {t : ParallelState π r} (ht : s.insertFirst e = some t) :
    t.edgeCount = s.edgeCount + 1 := by
  unfold insertFirst at ht
  split at ht
  next h => cases Option.some.inj ht; exact s.insertAt_edgeCount _ e _
  next h => cases ht

/-- The original oracle is queried once; known original edges are subtracted locally. -/
def residualQuery (s : ParallelState π r) (S : Finset V) : DTree (Finset V) ℝ ℝ 1 :=
  deletionQuery s.usedGraph S

theorem residualQuery_eval (s : ParallelState π r) (G : WeightedGraph V)
    (hs : s.usedGraph.IsSubgraph G) (S : Finset V) :
    (s.residualQuery S).eval G.cut = (G.subtract s.usedGraph).cut S :=
  deletionQuery_eval G s.usedGraph hs S

theorem residualQuery_cost (s : ParallelState π r) (S : Finset V)
    (read : Finset V → ℝ) : (s.residualQuery S).cost read = 1 := rfl

def residualCrossQuery (s : ParallelState π r) (A B : Finset V) :
    DTree (Finset V) ℝ ℝ 3 := (crossQuery A B).substitute s.residualQuery

theorem residualCrossQuery_eval (s : ParallelState π r) (G : WeightedGraph V)
    (hs : s.usedGraph.IsSubgraph G) {A B : Finset V} (hAB : Disjoint A B) :
    (s.residualCrossQuery A B).eval G.cut = (G.subtract s.usedGraph).cross A B := by
  rw [residualCrossQuery, DTree.eval_substitute]
  have he : (fun S => (s.residualQuery S).eval G.cut) = (G.subtract s.usedGraph).cut :=
    funext (s.residualQuery_eval G hs)
  rw [he, crossQuery_eval _ hAB]

/-- A discovered original edge fits precisely in the undeleted capacity. -/
theorem insertAt_subgraph (s : ParallelState π r) (i : Fin r) (e : OriginalEdge π) (hn)
    (G : WeightedGraph V) (hs : s.usedGraph.IsSubgraph G)
    (he : e.graph.IsSubgraph (G.subtract s.usedGraph)) :
    (s.insertAt i e hn).usedGraph.IsSubgraph G := by
  rw [s.insertAt_usedGraph]
  intro u v
  have hh := he u v
  change e.graph.w u v ≤ max 0 (G.w u v - s.usedGraph.w u v) at hh
  rw [max_eq_right (sub_nonneg.mpr (hs u v))] at hh
  change s.usedGraph.w u v + e.graph.w u v ≤ G.w u v
  linarith

theorem residual_integral (s : ParallelState π r) (G : WeightedGraph V)
    (hG : G.IsIntegral) (hs : s.usedGraph.IsSubgraph G) :
    (G.subtract s.usedGraph).IsIntegral := hG.subtract s.usedGraph_integral hs

/-- The Boolean discovery matrix is justified by the original unit input,
not by Booleanizing the quotient. -/
theorem residual_unit (s : ParallelState π r) (G : SimpleInput V)
    (hs : s.usedGraph.IsSubgraph G.toWeighted) (u v : V) :
    (G.toWeighted.subtract s.usedGraph).w u v = 0 ∨
      (G.toWeighted.subtract s.usedGraph).w u v = 1 := by
  obtain ⟨k, hk⟩ := s.residual_integral G.toWeighted G.integral_toWeighted hs u v
  have hgle : G.toWeighted.w u v ≤ 1 := by
    change ((G.w u v : ℕ) : ℝ) ≤ 1
    exact_mod_cast Nat.le_of_lt_succ (G.w u v).isLt
  have hle : (G.toWeighted.subtract s.usedGraph).w u v ≤ 1 := by
    change max 0 (G.toWeighted.w u v - s.usedGraph.w u v) ≤ 1
    exact max_le zero_le_one (by linarith [s.usedGraph.nonneg u v])
  have hk1 : k ≤ 1 := by exact_mod_cast (hk ▸ hle)
  have hz : k = 0 ∨ k = 1 := by omega
  rcases hz with rfl | rfl <;> simp_all

/-- Once an original unit is used, neither its reverse name nor a later layer
can use it again: both orientations have zero honest residual capacity. -/
theorem exhausted_original_edge (s : ParallelState π r) (G : SimpleInput V)
    (hs : s.usedGraph.IsSubgraph G.toWeighted) {u v : V}
    (hused : 1 ≤ s.usedGraph.w u v) :
    (G.toWeighted.subtract s.usedGraph).w u v = 0 ∧
      (G.toWeighted.subtract s.usedGraph).w v u = 0 := by
  have hg : G.toWeighted.w u v ≤ 1 := by
    change ((G.w u v : ℕ) : ℝ) ≤ 1
    exact_mod_cast Nat.le_of_lt_succ (G.w u v).isLt
  have hz : (G.toWeighted.subtract s.usedGraph).w u v = 0 := by
    change max 0 (G.toWeighted.w u v - s.usedGraph.w u v) = 0
    exact max_eq_left (by linarith)
  exact ⟨hz, by rw [WeightedGraph.symm]; exact hz⟩

theorem listed_edge_exhausted (s : ParallelState π r) (G : SimpleInput V)
    (hs : s.usedGraph.IsSubgraph G.toWeighted) (i : Fin r) {e : OriginalEdge π}
    (he : e ∈ (s.forests i).edges) :
    (G.toWeighted.subtract s.usedGraph).w e.val.1 e.val.2 = 0 ∧
      (G.toWeighted.subtract s.usedGraph).w e.val.2 e.val.1 = 0 := by
  apply s.exhausted_original_edge G hs
  have hw := s.usedGraph_contains i he e.val.1 e.val.2
  rwa [e.self_weight] at hw

theorem insertAt_honest (s : ParallelState π r) (i : Fin r) (e : OriginalEdge π) (hn)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (hp : 0 < (G.toWeighted.subtract s.usedGraph).w e.val.1 e.val.2) :
    (s.insertAt i e hn).usedGraph.IsSubgraph G.toWeighted :=
  s.insertAt_subgraph i e hn G.toWeighted hs
    (e.subgraph_of_positive _ (s.residual_integral _ G.integral_toWeighted hs) hp)

def lastIndex (hr : 0 < r) : Fin r := ⟨r - 1, by omega⟩

def lastBlock (s : ParallelState π r) (hr : 0 < r) (v : V) : Finset V :=
  π.lift (forestBlock (s.forests (lastIndex hr)).quotient (π.map v))

@[simp] theorem mem_lastBlock (s : ParallelState π r) (hr : 0 < r) (u v : V) :
    v ∈ s.lastBlock hr u ↔
      (s.forests (lastIndex hr)).quotient.Reachable (π.map u) (π.map v) := by
  simp [lastBlock]

theorem self_mem_lastBlock (s : ParallelState π r) (hr : 0 < r) (v : V) :
    v ∈ s.lastBlock hr v := by simp

/-- Retired vertices have no unassigned edge leaving their finest component. -/
def InactiveSound (s : ParallelState π r) (hr : 0 < r) (G : WeightedGraph V) : Prop :=
  ∀ v ∈ s.inactive, ∀ w, w ∉ s.lastBlock hr v → (G.subtract s.usedGraph).w v w = 0

theorem inactive_closed_in_earlier (s : ParallelState π r) (hr : 0 < r)
    (G : WeightedGraph V) (hl : s.Laminar) (hi : s.InactiveSound hr G)
    {v : V} (hv : v ∈ s.inactive) (i : Fin r) {w : V}
    (hw : ¬(s.forests i).quotient.Reachable (π.map v) (π.map w)) :
    (G.subtract s.usedGraph).w v w = 0 := by
  apply hi v hv w
  intro hmem
  have hilast : i ≤ lastIndex hr := by
    change i.val ≤ r - 1
    omega
  exact hw (hl i (lastIndex hr) hilast _ _ ((s.mem_lastBlock hr v w).mp hmem))

def retire (s : ParallelState π r) (v : V) : ParallelState π r :=
  { s with inactive := insert v s.inactive }

/-- A real zero residual row proves that retiring this vertex is safe. -/
theorem retire_sound (s : ParallelState π r) (hr : 0 < r) (G : WeightedGraph V)
    (hi : s.InactiveSound hr G) (v : V)
    (hz : (G.subtract s.usedGraph).cross {v} (s.lastBlock hr v)ᶜ = 0) :
    (s.retire v).InactiveSound hr G := by
  intro u hu w hw
  change u ∈ insert v s.inactive at hu
  rcases Finset.mem_insert.mp hu with huv | hu
  · subst u
    have hw' : w ∈ (s.lastBlock hr v)ᶜ := Finset.mem_compl.mpr hw
    have hle : (G.subtract s.usedGraph).w v w ≤
        (G.subtract s.usedGraph).cross {v} (s.lastBlock hr v)ᶜ := by
      simp only [WeightedGraph.cross, Finset.sum_singleton]
      exact Finset.single_le_sum (fun x _ => (G.subtract s.usedGraph).nonneg v x) hw'
    exact le_antisymm (hz ▸ hle) ((G.subtract s.usedGraph).nonneg _ _)
  · exact hi u hu w hw

theorem retire_charge (s : ParallelState π r) {v : V} (hv : v ∉ s.inactive) :
    (s.retire v).inactive.card = s.inactive.card + 1 :=
  Finset.card_insert_of_notMem hv

theorem retire_mono (s : ParallelState π r) (v : V) :
    s.inactive ⊆ (s.retire v).inactive := Finset.subset_insert _ _

theorem inactive_card_le (s : ParallelState π r) : s.inactive.card ≤ Fintype.card V :=
  Finset.card_le_univ _

theorem insertAt_residual_le (s : ParallelState π r) (i : Fin r)
    (e : OriginalEdge π) (hn) (G : WeightedGraph V) :
    (G.subtract (s.insertAt i e hn).usedGraph).IsSubgraph (G.subtract s.usedGraph) := by
  rw [s.insertAt_usedGraph]
  intro u v
  change max 0 (G.w u v - (s.usedGraph.w u v + e.graph.w u v)) ≤
    max 0 (G.w u v - s.usedGraph.w u v)
  exact max_le_max le_rfl (by linarith [e.graph.nonneg u v])

/-- Retirement remains valid after any legal forest extension: components only
merge and the original residual capacities only decrease. -/
theorem insertAt_inactiveSound (s : ParallelState π r) (i : Fin r)
    (e : OriginalEdge π) (hn) (hr : 0 < r) (G : WeightedGraph V)
    (hi : s.InactiveSound hr G) : (s.insertAt i e hn).InactiveSound hr G := by
  intro v hv w hw
  have hold : w ∉ s.lastBlock hr v := by
    intro hm
    apply hw
    rw [mem_lastBlock] at hm ⊢
    exact s.insertAt_reachable i e hn _ hm
  have hz := hi v hv w hold
  have hle := s.insertAt_residual_le i e hn G v w
  rw [hz] at hle
  exact le_antisymm hle ((G.subtract (s.insertAt i e hn).usedGraph).nonneg _ _)

end ParallelState

#print axioms OriginalEdge.contract_graph
#print axioms ForestTrace.acyclic
#print axioms ForestTrace.contract_eq
#print axioms ForestTrace.card_edges
#print axioms ParallelState.usedGraph_integral
#print axioms ParallelState.usedGraph_contract
#print axioms ParallelState.quotientGraph_subgraph
#print axioms ParallelState.complete_certificate
#print axioms ParallelState.edgeCount_le
#print axioms ParallelState.insertAt_usedGraph
#print axioms ParallelState.insertFirst_laminar
#print axioms ParallelState.insertFirst_edgeCount
#print axioms ParallelState.residualCrossQuery_eval
#print axioms ParallelState.insertAt_subgraph
#print axioms ParallelState.quotientGraph_edgeMass
#print axioms ParallelState.residual_unit
#print axioms ParallelState.exhausted_original_edge
#print axioms ParallelState.listed_edge_exhausted
#print axioms ParallelState.insertAt_honest
#print axioms ParallelState.inactive_closed_in_earlier
#print axioms ParallelState.retire_sound
#print axioms ParallelState.retire_charge
#print axioms ParallelState.insertAt_inactiveSound

end
end CutQueryComplexity.StarContraction2022.Certificates
