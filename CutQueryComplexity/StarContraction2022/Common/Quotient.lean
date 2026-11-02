import CutQueryComplexity.StarContraction2022.Common.Basic
import CutQueryComplexity.Graph.RespectingCuts
import CutQueryComplexity.GHReduction.Contractions

/-! # Public quotients, exact queries, and surviving minimum shores -/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022

noncomputable section
open scoped Classical

/-- A public quotient has no empty labels and stores no hidden graph data. -/
structure PublicQuotient (V Q : Type) where
  map : V → Q
  onto : Function.Surjective map

variable {V Q : Type} [Fintype V] [DecidableEq V] [Fintype Q] [DecidableEq Q]

theorem cut_eq_mincut_of_isMinCut {G : WeightedGraph V} {S : Finset V}
    (h : IsMinCut G S) : G.cut S = mincutValue G := by
  obtain ⟨T, hT, he⟩ := exists_isMinCut G ⟨S, (mem_properShores S).mpr h.1⟩
  exact le_antisymm ((h.2 T hT.1).trans_eq he) (mincutValue_le G h.1)

namespace PublicQuotient

def identity : PublicQuotient V V := ⟨id, Function.surjective_id⟩

def lift (π : PublicQuotient V Q) (S : Finset Q) : Finset V :=
  WeightedGraph.pull π.map S

def graph (π : PublicQuotient V Q) (G : WeightedGraph V) : WeightedGraph Q :=
  G.contract π.map

theorem card_le (π : PublicQuotient V Q) : Fintype.card Q ≤ Fintype.card V :=
  Fintype.card_le_of_surjective π.map π.onto

@[simp] theorem mem_lift (π : PublicQuotient V Q) (S : Finset Q) (v : V) :
    v ∈ π.lift S ↔ π.map v ∈ S := WeightedGraph.mem_pull _ _ _

@[simp] theorem lift_univ (π : PublicQuotient V Q) :
    π.lift Finset.univ = Finset.univ := by ext; simp

theorem proper_lift (π : PublicQuotient V Q) {S : Finset Q}
    (hS : ProperShore S) : ProperShore (π.lift S) :=
  WeightedGraph.properShore_pull π.map π.onto hS

theorem proper_lift_iff (π : PublicQuotient V Q) (S : Finset Q) :
    ProperShore (π.lift S) ↔ ProperShore S := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · obtain ⟨v, hv⟩ := h.1
      exact ⟨π.map v, (π.mem_lift S v).mp hv⟩
    · intro he
      apply h.2
      rw [he, lift_univ]
  · exact π.proper_lift

theorem respects_lift (π : PublicQuotient V Q) (S : Finset Q) :
    RespectsBlocks π.map (π.lift S) := by
  intro u v huv
  simp only [mem_lift, huv]

theorem lift_image (π : PublicQuotient V Q) {S : Finset V}
    (hS : RespectsBlocks π.map S) : π.lift (S.image π.map) = S :=
  hS.pull_image

theorem proper_image (π : PublicQuotient V Q) {S : Finset V}
    (hS : RespectsBlocks π.map S) (hp : ProperShore S) :
    ProperShore (S.image π.map) := by
  apply (π.proper_lift_iff _).mp
  rwa [π.lift_image hS]

@[simp] theorem cut_graph (π : PublicQuotient V Q) (G : WeightedGraph V)
    (S : Finset Q) : (π.graph G).cut S = G.cut (π.lift S) :=
  WeightedGraph.cut_contract G π.map S

theorem integral_graph (π : PublicQuotient V Q) (G : WeightedGraph V)
    (hG : G.IsIntegral) : (π.graph G).IsIntegral :=
  GHReduction.integral_contract G hG π.map

/-- A surviving original minimum is a quotient minimum, with no value loss. -/
theorem project_minimum (π : PublicQuotient V Q) {G : WeightedGraph V}
    {S : Finset V} (hS : IsMinCut G S) (hs : RespectsBlocks π.map S) :
    IsMinCut (π.graph G) (S.image π.map) := by
  refine ⟨π.proper_image hs hS.1, fun T hT => ?_⟩
  rw [π.cut_graph, π.lift_image hs, π.cut_graph]
  exact hS.2 _ (π.proper_lift hT)

/-- Every quotient minimum lifts, once an actual original minimum survives. -/
theorem lift_minimum (π : PublicQuotient V Q) {G : WeightedGraph V}
    {S : Finset V} (hS : IsMinCut G S) (hs : RespectsBlocks π.map S)
    {T : Finset Q} (hT : IsMinCut (π.graph G) T) :
    IsMinCut G (π.lift T) := by
  refine ⟨π.proper_lift hT.1, fun U hU => ?_⟩
  calc
    G.cut (π.lift T) = (π.graph G).cut T := (π.cut_graph G T).symm
    _ ≤ (π.graph G).cut (S.image π.map) := hT.2 _ (π.proper_image hs hS.1)
    _ = G.cut S := by rw [π.cut_graph, π.lift_image hs]
    _ ≤ G.cut U := hS.2 U hU

theorem mincut_eq (π : PublicQuotient V Q) {G : WeightedGraph V}
    {S : Finset V} (hS : IsMinCut G S) (hs : RespectsBlocks π.map S) :
    mincutValue (π.graph G) = mincutValue G := by
  rw [← cut_eq_mincut_of_isMinCut (π.project_minimum hS hs),
    π.cut_graph, π.lift_image hs, cut_eq_mincut_of_isMinCut hS]

theorem two_le_card_of_survives (π : PublicQuotient V Q) {S : Finset V}
    (hS : RespectsBlocks π.map S) (hp : ProperShore S) : 2 ≤ Fintype.card Q := by
  have hT := π.proper_image hS hp
  obtain ⟨a, ha⟩ := hT.1
  obtain ⟨b, hb⟩ : ∃ b, b ∉ S.image π.map := by
    by_contra h
    push_neg at h
    exact hT.2 (Finset.eq_univ_of_forall h)
  have hab : a ≠ b := by intro he; subst b; exact hb ha
  have hc := Finset.card_le_univ ({a, b} : Finset Q)
  simpa [Finset.card_pair hab] using hc

/-- The quotient query is implemented by one query at a public lifted shore. -/
def query (π : PublicQuotient V Q) (S : Finset Q) : DTree (Finset V) ℝ ℝ 1 :=
  GHReduction.contractQuery π.map S

theorem query_eval (π : PublicQuotient V Q) (G : WeightedGraph V) (S : Finset Q) :
    (π.query S).eval G.cut = (π.graph G).cut S :=
  GHReduction.contractQuery_eval G π.map S

theorem query_cost (π : PublicQuotient V Q) (S : Finset Q) (read : Finset V → ℝ) :
    (π.query S).cost read = 1 := rfl

variable {O : Type} {budget : ℕ}

def compile (π : PublicQuotient V Q) (T : RTree (Finset Q) ℝ O budget) :
    RTree (Finset V) ℝ O budget := GHReduction.contractProgram π.map T

theorem compile_eval (π : PublicQuotient V Q) (G : WeightedGraph V)
    (T : RTree (Finset Q) ℝ O budget) :
    (π.compile T).eval G.cut = T.eval (π.graph G).cut :=
  GHReduction.contractProgram_eval G π.map T

theorem compile_cost (π : PublicQuotient V Q) (T : RTree (Finset Q) ℝ O budget)
    (read : Finset V → ℝ) {out : O × ℕ}
    (hout : out ∈ (RTree.run read (π.compile T)).support) : out.2 ≤ budget :=
  RTree.cost_le _ read hout

def compileDet (π : PublicQuotient V Q) (T : DTree (Finset Q) ℝ O budget) :
    DTree (Finset V) ℝ O budget := GHReduction.contractDetProgram π.map T

theorem compileDet_eval (π : PublicQuotient V Q) (G : WeightedGraph V)
    (T : DTree (Finset Q) ℝ O budget) :
    (π.compileDet T).eval G.cut = T.eval (π.graph G).cut :=
  GHReduction.contractDetProgram_eval G π.map T

end PublicQuotient

#print axioms PublicQuotient.proper_lift_iff
#print axioms PublicQuotient.integral_graph
#print axioms PublicQuotient.project_minimum
#print axioms PublicQuotient.lift_minimum
#print axioms PublicQuotient.mincut_eq
#print axioms PublicQuotient.two_le_card_of_survives
#print axioms PublicQuotient.compile_eval
#print axioms PublicQuotient.compile_cost

end
end CutQueryComplexity.StarContraction2022
