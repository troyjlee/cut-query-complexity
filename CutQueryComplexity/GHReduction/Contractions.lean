import CutQueryComplexity.Graph.Operations
import CutQueryComplexity.Graph.Integral
import CutQueryComplexity.Model.RandomizedReduction

/-! # Exact contraction queries and capacity promises

The public map is the only graph-related argument of the compiled programs.
Every virtual query makes one original query, including after adaptive answers.
Integrality, total capacity, and approximation inheritance are semantic lemmas.
Surjectivity certifies that the label type has the actual supervertex count.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction

noncomputable section
open scoped Classical
open WeightedGraph

variable {V B C : Type} [Fintype V] [DecidableEq V]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

@[simp] theorem pull_comp (π : V → B) (ρ : B → C) (S : Finset C) :
    pull π (pull ρ S) = pull (ρ ∘ π) S := by
  ext v
  simp [Function.comp_def]

theorem cut_contract_comp (G : WeightedGraph V) (π : V → B) (ρ : B → C)
    (S : Finset C) : ((G.contract π).contract ρ).cut S = (G.contract (ρ ∘ π)).cut S := by
  rw [cut_contract, cut_contract, pull_comp, cut_contract]

theorem compact_card_le (π : V → B) (hπ : Function.Surjective π) :
    Fintype.card B ≤ Fintype.card V :=
  Fintype.card_le_of_surjective π hπ

/-- The exact one-query implementation, independent of the hidden graph. -/
def contractQuery (π : V → B) (S : Finset B) : DTree (Finset V) ℝ ℝ 1 :=
  DTree.query (pull π S) (fun a => DTree.pure a)

@[simp] theorem contractQuery_eval (G : WeightedGraph V) (π : V → B) (S : Finset B) :
    (contractQuery π S).eval G.cut = (G.contract π).cut S := by
  simp [contractQuery, cut_contract]

@[simp] theorem contractQuery_cost (π : V → B) (S : Finset B) (read : Finset V → ℝ) :
    (contractQuery π S).cost read = 1 := rfl

variable {O : Type} {q : ℕ}

/-- Compile an entire randomized virtual program with no budget expansion. -/
def contractProgram (π : V → B) (T : RTree (Finset B) ℝ O q) :
    RTree (Finset V) ℝ O q :=
  (T.substitute (contractQuery π)).cast (Nat.mul_one q)

theorem contractProgram_eval (G : WeightedGraph V) (π : V → B)
    (T : RTree (Finset B) ℝ O q) :
    (contractProgram π T).eval G.cut = T.eval (G.contract π).cut := by
  rw [contractProgram, RTree.eval_cast, RTree.eval_substitute]
  have hread : (fun S => (contractQuery π S).eval G.cut) = (G.contract π).cut :=
    funext (contractQuery_eval G π)
  rw [hread]

/-- The cap is valid even for inconsistent original-oracle answers. -/
theorem contractProgram_cost_le (π : V → B) (T : RTree (Finset B) ℝ O q)
    (read : Finset V → ℝ) {out : O × ℕ}
    (hout : out ∈ (RTree.run read (contractProgram π T)).support) : out.2 ≤ q :=
  RTree.cost_le _ read hout

/-- The corresponding deterministic compiler uses the same one-query adapter. -/
def contractDetProgram (π : V → B) (T : DTree (Finset B) ℝ O q) :
    DTree (Finset V) ℝ O q :=
  (T.substitute (contractQuery π)).cast (Nat.mul_one q)

theorem contractDetProgram_eval (G : WeightedGraph V) (π : V → B)
    (T : DTree (Finset B) ℝ O q) :
    (contractDetProgram π T).eval G.cut = T.eval (G.contract π).cut := by
  rw [contractDetProgram, DTree.eval_cast, DTree.eval_substitute]
  have hread : (fun S => (contractQuery π S).eval G.cut) = (G.contract π).cut :=
    funext (contractQuery_eval G π)
  rw [hread]

/-- Natural capacities may grow under contraction, but remain natural. -/
theorem integral_contract (G : WeightedGraph V) (hG : G.IsIntegral) (π : V → B) :
    (G.contract π).IsIntegral := by
  choose w hw using hG
  intro b c
  by_cases hbc : b = c
  · exact ⟨0, by simp [WeightedGraph.contract, hbc]⟩
  · refine ⟨∑ u ∈ fiber π b, ∑ v ∈ fiber π c, w u v, ?_⟩
    simp [WeightedGraph.contract, hbc, WeightedGraph.cross, hw]

/-- Deleting within-fiber loops cannot increase total edge capacity. -/
theorem edgeMass_contract_le (G : WeightedGraph V) (π : V → B) :
    (G.contract π).edgeMass ≤ G.edgeMass := by
  unfold WeightedGraph.edgeMass
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    _ ≤ ∑ b, ∑ c, G.cross (fiber π b) (fiber π c) := by
      apply Finset.sum_le_sum
      intro b _
      apply Finset.sum_le_sum
      intro c _
      by_cases hbc : b = c
      · simp [WeightedGraph.contract, hbc, G.cross_nonneg]
      · simp [WeightedGraph.contract, hbc]
    _ = G.cross (pull π Finset.univ) (pull π Finset.univ) :=
      G.cross_fibers π Finset.univ Finset.univ
    _ = _ := by
      have he : pull π Finset.univ = Finset.univ := by ext; simp
      rw [he]
      rfl

theorem cut_le_edgeMass (G : WeightedGraph V) (S : Finset V) :
    G.cut S ≤ G.edgeMass := by
  have h : G.cut S + G.cut Sᶜ ≤ ∑ u, ∑ v, G.w u v := by
    simp only [cut_eq_sum_ite, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro u _
    apply Finset.sum_le_sum
    intro v _
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp [hu, hv, G.nonneg]
  rw [cut_compl] at h
  unfold WeightedGraph.edgeMass
  linarith

theorem weight_le_edgeMass (G : WeightedGraph V) (u v : V) : G.w u v ≤ G.edgeMass := by
  calc
    _ ≤ ∑ t, G.w u t := Finset.single_le_sum (fun t _ => G.nonneg u t) (Finset.mem_univ v)
    _ = G.cut {u} := (G.cut_singleton u).symm
    _ ≤ G.edgeMass := cut_le_edgeMass G {u}

/-- The original total-capacity promise supplies both the primitive's per-edge
promise and the range for every exact contracted cut value. -/
theorem contract_capacity_bounds (G : WeightedGraph V) (π : V → B) {M : ℝ}
    (hM : G.edgeMass ≤ M) :
    (∀ b c, (G.contract π).w b c ≤ M) ∧ (∀ S, (G.contract π).cut S ≤ M) := by
  have hm := (edgeMass_contract_le G π).trans hM
  exact ⟨fun b c => (weight_le_edgeMass _ b c).trans hm,
    fun S => (cut_le_edgeMass _ S).trans hm⟩

/-- Simultaneous approximation passes to every public partition. No independence
between the map and the approximator is needed. -/
theorem approximation_contract (F K : WeightedGraph V) {eps : ℝ}
    (happrox : ∀ S, (1 - eps) * F.cut S ≤ K.cut S ∧
      K.cut S ≤ (1 + eps) * F.cut S) (π : V → B) (S : Finset B) :
    (1 - eps) * (F.contract π).cut S ≤ (K.contract π).cut S ∧
      (K.contract π).cut S ≤ (1 + eps) * (F.contract π).cut S := by
  simpa only [cut_contract] using happrox (pull π S)

end
end CutQueryComplexity.GHReduction
