import CutQueryComplexity.Primitive.BinarySearch
import CutQueryComplexity.AllPairsAudit.CutAlgebra
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Tauto

/-!
# Cut queries on the actual vertex subtype of a public part

`PartVertex W` has exactly `W.card` vertices. The hidden graph occurs only in
semantic definitions and proofs. `subtypeQuery` takes a public part and a
subtype shore, and executes exactly three ambient cut queries, even for an
inconsistent real-valued oracle. Adaptive substitution preserves the output
and multiplies the realized query count by exactly three.

Instantiate downstream BFS/DFS on this subtype, with two additional terminal
vertices. Query each part directly through this adapter to the fixed ambient
oracle; nesting ambient induced graphs would retain the wrong cardinality.
The adapter alone does not implement scaled flow, pruning, or all-pairs cuts.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.Pruning

open Finset WeightedGraph
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The public part itself is the vertex type, with no isolated ambient vertices. -/
abbrev PartVertex (W : Finset V) := {v : V // v ∈ W}

def partEmbedding (W : Finset V) : PartVertex W ↪ V where
  toFun := Subtype.val
  inj' := Subtype.val_injective

def liftShore (W : Finset V) (S : Finset (PartVertex W)) : Finset V :=
  S.map (partEmbedding W)

def restrictShore (W : Finset V) (S : Finset V) : Finset (PartVertex W) :=
  univ.filter (fun v => (v : V) ∈ S)

@[simp] theorem partVertex_card (W : Finset V) :
    Fintype.card (PartVertex W) = W.card := Fintype.card_coe W

/-- The two-star solver has q+2 vertices when q=W.card. -/
@[simp] theorem partNetwork_card (W : Finset V) :
    Fintype.card (PartVertex W ⊕ Fin 2) = W.card + 2 := by simp

theorem partNetwork_searchDepth (W : Finset V) :
    searchDepth (PartVertex W ⊕ Fin 2) = Nat.clog 2 (W.card + 2) := by
  simp only [searchDepth, partNetwork_card]

@[simp] theorem liftShore_card (W : Finset V) (S : Finset (PartVertex W)) :
    (liftShore W S).card = S.card := by simp [liftShore]

@[simp] theorem mem_liftShore (W : Finset V) (S : Finset (PartVertex W))
    (v : PartVertex W) : (v : V) ∈ liftShore W S ↔ v ∈ S := by
  simp [liftShore, partEmbedding]

theorem liftShore_subset (W : Finset V) (S : Finset (PartVertex W)) :
    liftShore W S ⊆ W := by
  intro v hv
  obtain ⟨u, _, hu⟩ := mem_map.mp hv
  change (u : V) = v at hu
  exact hu ▸ u.property

@[simp] theorem mem_restrictShore (W S : Finset V) (v : PartVertex W) :
    v ∈ restrictShore W S ↔ (v : V) ∈ S := by simp [restrictShore]

@[simp] theorem restrictShore_liftShore (W : Finset V) (S : Finset (PartVertex W)) :
    restrictShore W (liftShore W S) = S := by
  ext v
  simp only [mem_restrictShore, mem_liftShore]

@[simp] theorem liftShore_restrictShore (W S : Finset V) :
    liftShore W (restrictShore W S) = W ∩ S := by
  ext v
  constructor
  · intro hv
    obtain ⟨u, hu, he⟩ := mem_map.mp hv
    change (u : V) = v at he
    exact mem_inter.mpr ⟨he ▸ u.property, he ▸ (mem_restrictShore W S u).mp hu⟩
  · intro hv
    let u : PartVertex W := ⟨v, (mem_inter.mp hv).1⟩
    exact mem_map.mpr ⟨u, (mem_restrictShore W S u).mpr (mem_inter.mp hv).2, rfl⟩

theorem liftShore_injective (W : Finset V) : Function.Injective (liftShore W) :=
  Finset.map_injective (partEmbedding W)

@[simp] theorem liftShore_nonempty (W : Finset V) (S : Finset (PartVertex W)) :
    (liftShore W S).Nonempty ↔ S.Nonempty := Finset.map_nonempty

@[simp] theorem liftShore_univ (W : Finset V) :
    liftShore W univ = W := by
  have h : restrictShore W (univ : Finset V) = univ := by ext v; simp
  simpa only [h, inter_univ] using liftShore_restrictShore W (univ : Finset V)

@[simp] theorem liftShore_compl (W : Finset V) (S : Finset (PartVertex W)) :
    liftShore W Sᶜ = W \ liftShore W S := by
  ext v
  by_cases hw : v ∈ W
  · let u : PartVertex W := ⟨v, hw⟩
    change (u : V) ∈ liftShore W Sᶜ ↔ (u : V) ∈ W \ liftShore W S
    simp only [mem_liftShore, mem_compl, mem_sdiff, u.property, true_and]
  · have hn : v ∉ liftShore W Sᶜ := fun hv => hw (liftShore_subset W Sᶜ hv)
    simp only [hn, mem_sdiff, hw, false_and]

/-- A proper subtype shore is proper relative to W, not necessarily a global cut. -/
theorem properShore_lift_iff (W : Finset V) (S : Finset (PartVertex W)) :
    ProperShore S ↔ (liftShore W S).Nonempty ∧ liftShore W S ≠ W := by
  have he : liftShore W S = W ↔ S = univ := by
    constructor
    · intro h
      apply liftShore_injective W
      exact h.trans (liftShore_univ W).symm
    · intro h
      subst S
      exact liftShore_univ W
  constructor
  · rintro ⟨hne, hproper⟩
    exact ⟨(liftShore_nonempty W S).mpr hne, fun h => hproper (he.mp h)⟩
  · rintro ⟨hne, hproper⟩
    exact ⟨(liftShore_nonempty W S).mp hne, fun h => hproper (he.mpr h)⟩

/-- Semantic restriction: programs never receive this hidden graph as data. -/
def partGraph (G : WeightedGraph V) (W : Finset V) : WeightedGraph (PartVertex W) where
  w u v := G.w u.val v.val
  symm u v := G.symm u.val v.val
  nonneg u v := G.nonneg u.val v.val
  diag u := G.diag u.val

@[simp] theorem partGraph_w (G : WeightedGraph V) (W : Finset V)
    (u v : PartVertex W) : (partGraph G W).w u v = G.w u.val v.val := rfl

theorem partGraph_unweighted {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G)
    (W : Finset V) : AllPairsAudit.Unweighted (partGraph G W) :=
  fun u v => hG u.val v.val

theorem partGraph_cross (G : WeightedGraph V) (W : Finset V)
    (S T : Finset (PartVertex W)) :
    (partGraph G W).cross S T = G.cross (liftShore W S) (liftShore W T) := by
  simp only [cross, partGraph, liftShore, sum_map, partEmbedding]
  rfl

theorem partGraph_cut (G : WeightedGraph V) (W : Finset V)
    (S : Finset (PartVertex W)) :
    (partGraph G W).cut S = G.cross (liftShore W S) (W \ liftShore W S) := by
  change (partGraph G W).cross S Sᶜ = _
  rw [partGraph_cross, liftShore_compl]

theorem partGraph_cut_induce (G : WeightedGraph V) (W : Finset V)
    (S : Finset (PartVertex W)) :
    (partGraph G W).cut S = (G.induce W).cut (liftShore W S) := by
  rw [partGraph_cut, cut_induce, inter_eq_left.mpr (liftShore_subset W S)]

theorem partGraph_cut_local (G : WeightedGraph V) (W : Finset V)
    (S : Finset (PartVertex W)) :
    (partGraph G W).cut S = G.localCut W (liftShore W S) := by
  rw [localCut_eq_cut_induce, partGraph_cut_induce]

/-- Restricting an arbitrary ambient shore ignores exactly the vertices outside W. -/
theorem partGraph_cut_restrict (G : WeightedGraph V) (W S : Finset V) :
    (partGraph G W).cut (restrictShore W S) = (G.induce W).cut S := by
  have he : W \ (W ∩ S) = W \ S := by
    ext v
    simp only [mem_sdiff, mem_inter]
    tauto
  rw [partGraph_cut, liftShore_restrictShore, cut_induce, he, inter_comm W S]

theorem partGraph_cut_three (G : WeightedGraph V) (W : Finset V)
    (S : Finset (PartVertex W)) :
    (partGraph G W).cut S =
      (G.cut (liftShore W S) + G.cut (W \ liftShore W S) - G.cut W) / 2 := by
  have hd : Disjoint (liftShore W S) (W \ liftShore W S) :=
    disjoint_left.mpr fun _ hv hw => (mem_sdiff.mp hw).2 hv
  rw [partGraph_cut, G.cross_eq_three_cuts hd,
    union_sdiff_of_subset (liftShore_subset W S)]

/-- Only an induced-graph optimum is transported; no global optimality is asserted. -/
theorem isSTMinCut_lift {G : WeightedGraph V} {W : Finset V}
    {s t : PartVertex W} {S : Finset (PartVertex W)}
    (hS : IsSTMinCut (partGraph G W) s t S) :
    IsSTMinCut (G.induce W) s.val t.val (liftShore W S) := by
  refine ⟨(mem_liftShore W S s).mpr hS.1,
    fun ht => hS.2.1 ((mem_liftShore W S t).mp ht), ?_⟩
  intro T hs ht
  have h := hS.2.2 (restrictShore W T)
    ((mem_restrictShore W T s).mpr hs)
    (fun hm => ht ((mem_restrictShore W T t).mp hm))
  calc
    (G.induce W).cut (liftShore W S) = (partGraph G W).cut S :=
      (partGraph_cut_induce G W S).symm
    _ ≤ (partGraph G W).cut (restrictShore W T) := h
    _ = (G.induce W).cut T := partGraph_cut_restrict G W T

theorem isSTMinCut_restrict {G : WeightedGraph V} {W S : Finset V}
    {s t : PartVertex W} (hS : IsSTMinCut (G.induce W) s.val t.val S) :
    IsSTMinCut (partGraph G W) s t (restrictShore W S) := by
  refine ⟨(mem_restrictShore W S s).mpr hS.1,
    fun ht => hS.2.1 ((mem_restrictShore W S t).mp ht), ?_⟩
  intro T hs ht
  have h := hS.2.2 (liftShore W T) ((mem_liftShore W T s).mpr hs)
    (fun hm => ht ((mem_liftShore W T t).mp hm))
  calc
    (partGraph G W).cut (restrictShore W S) = (G.induce W).cut S :=
      partGraph_cut_restrict G W S
    _ ≤ (G.induce W).cut (liftShore W T) := h
    _ = (partGraph G W).cut T := (partGraph_cut_induce G W T).symm

/-- The virtual answer induced by any ambient oracle, including inconsistent ones. -/
def subtypeOracle (W : Finset V) (oracle : Finset V → ℝ)
    (S : Finset (PartVertex W)) : ℝ :=
  (oracle (liftShore W S) + oracle (W \ liftShore W S) - oracle W) / 2

/-- Three queries go directly to the fixed ambient oracle. W is public data. -/
def subtypeQuery (W : Finset V) (S : Finset (PartVertex W)) :
    DTree (Finset V) ℝ ℝ 3 :=
  crossQuery (liftShore W S) (W \ liftShore W S)

theorem subtypeQuery_run (W : Finset V) (S : Finset (PartVertex W))
    (oracle : Finset V → ℝ) :
    DTree.run oracle (subtypeQuery W S) = (subtypeOracle W oracle S, 3) := by
  simp only [subtypeQuery, crossQuery, DTree.run_query, DTree.run_pure,
    union_sdiff_of_subset (liftShore_subset W S), subtypeOracle]

@[simp] theorem subtypeQuery_eval_public (W : Finset V) (S : Finset (PartVertex W))
    (oracle : Finset V → ℝ) :
    (subtypeQuery W S).eval oracle = subtypeOracle W oracle S :=
  congrArg Prod.fst (subtypeQuery_run W S oracle)

/-- Exact cost, not merely an indexed upper bound; no honesty premise occurs. -/
theorem subtypeQuery_cost (W : Finset V) (S : Finset (PartVertex W))
    (oracle : Finset V → ℝ) : (subtypeQuery W S).cost oracle = 3 :=
  congrArg Prod.snd (subtypeQuery_run W S oracle)

theorem subtypeQuery_eval (G : WeightedGraph V) (W : Finset V)
    (S : Finset (PartVertex W)) :
    (subtypeQuery W S).eval G.cut = (partGraph G W).cut S := by
  rw [subtypeQuery_eval_public]
  exact (partGraph_cut_three G W S).symm

theorem subtypeOracle_cut (G : WeightedGraph V) (W : Finset V) :
    subtypeOracle W G.cut = (partGraph G W).cut := by
  funext S
  exact (partGraph_cut_three G W S).symm

/-- Adaptive programs use the actual part vertex type; each virtual query costs three. -/
def subtypeProgram {O : Type} {q : ℕ} (W : Finset V)
    (T : DTree (Finset (PartVertex W)) ℝ O q) : DTree (Finset V) ℝ O (q * 3) :=
  T.substitute (subtypeQuery W)

theorem subtypeProgram_eval_public {O : Type} {q : ℕ} (W : Finset V)
    (T : DTree (Finset (PartVertex W)) ℝ O q) (oracle : Finset V → ℝ) :
    (subtypeProgram W T).eval oracle = T.eval (subtypeOracle W oracle) := by
  simp only [subtypeProgram, DTree.eval_substitute, subtypeQuery_eval_public]

theorem subtypeProgram_eval {O : Type} {q : ℕ} (G : WeightedGraph V) (W : Finset V)
    (T : DTree (Finset (PartVertex W)) ℝ O q) :
    (subtypeProgram W T).eval G.cut = T.eval (partGraph G W).cut := by
  rw [subtypeProgram_eval_public, subtypeOracle_cut]

/-- Realized costs also transport exactly on arbitrary real-answer transcripts. -/
theorem subtypeProgram_cost {O : Type} {q : ℕ} (W : Finset V)
    (T : DTree (Finset (PartVertex W)) ℝ O q) (oracle : Finset V → ℝ) :
    (subtypeProgram W T).cost oracle = T.cost (subtypeOracle W oracle) * 3 := by
  induction q with
  | zero => simp [subtypeProgram, DTree.substitute, DTree.cost, DTree.run]
  | succ q ih =>
      rcases T with out | ⟨S, next⟩
      · simp [subtypeProgram, DTree.substitute, DTree.cost, DTree.run]
      · unfold subtypeProgram DTree.cost
        rw [DTree.substitute, DTree.run_cast, DTree.run_bind]
        change (subtypeQuery W S).cost oracle +
          (subtypeProgram W (next ((subtypeQuery W S).eval oracle))).cost oracle =
            ((next (subtypeOracle W oracle S)).cost (subtypeOracle W oracle) + 1) * 3
        rw [subtypeQuery_cost, subtypeQuery_eval_public, ih, Nat.add_mul, Nat.one_mul]
        exact Nat.add_comm _ _

theorem subtypeProgram_cost_le {O : Type} {q : ℕ} (W : Finset V)
    (T : DTree (Finset (PartVertex W)) ℝ O q) (oracle : Finset V → ℝ) :
    (subtypeProgram W T).cost oracle ≤ q * 3 := DTree.cost_le _ _

end
end CutQueryComplexity.DeterministicAPMCExpansion.Pruning

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.partVertex_card
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.partNetwork_card
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.liftShore_compl
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.partGraph_unweighted
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.partGraph_cut_three
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.isSTMinCut_lift
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.isSTMinCut_restrict
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.subtypeQuery_run
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.subtypeQuery_eval
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.subtypeQuery_cost
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.subtypeProgram_eval
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.subtypeProgram_cost
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.subtypeProgram_cost_le
