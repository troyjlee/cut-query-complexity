import CutQueryComplexity.GHReduction.Specification
import Mathlib.Tactic.Linarith

/-! # Compact component queries and canonical shores

The public vertex type is the subtype of a nonempty set `U`, so its size is
exactly `U.card`. Vertices outside `U` are contracted to a specified vertex of
`U`; this gives one original query per virtual query with no extra labels.
When `G.cut U = 0`, dropping those outside vertices from a returned shore
preserves its value and canonical s-t property in the original graph.

The program receives only `U` and public terminals. The zero-boundary premise
belongs to its correctness proof and can later be supplied by the single
simultaneous approximation event. It is not an additional algorithmic oracle.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical
open WeightedGraph

variable {V : Type} [Fintype V] [DecidableEq V] {U : Finset V}

/-- Lift a compact shore without adding any vertices outside the component. -/
def componentLift (S : Finset U) : Finset V := S.image Subtype.val

@[simp] theorem mem_componentLift (S : Finset U) (v : U) :
    v.val ∈ componentLift S ↔ v ∈ S := by
  constructor
  · intro hv
    obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hv
    have he' : u = v := Subtype.ext he
    simpa only [he'] using hu
  · intro hv
    exact Finset.mem_image.mpr ⟨v, hv, rfl⟩

theorem componentLift_subset (S : Finset U) : componentLift S ⊆ U := by
  intro v hv
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hv
  exact u.property

/-- Restrict an arbitrary original shore to the actual compact vertex type. -/
def componentProject (U : Finset V) (S : Finset V) : Finset U :=
  pull Subtype.val S

@[simp] theorem mem_componentProject (S : Finset V) (v : U) :
    v ∈ componentProject U S ↔ v.val ∈ S := by
  simp only [componentProject, mem_pull]

theorem componentLift_project (S : Finset V) :
    componentLift (componentProject U S) = S ∩ U := by
  ext v
  constructor
  · intro hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_inter.mpr ⟨(mem_componentProject S u).mp hu, u.property⟩
  · intro hv
    obtain ⟨hvS, hvU⟩ := Finset.mem_inter.mp hv
    exact Finset.mem_image.mpr
      ⟨⟨v, hvU⟩, (mem_componentProject S ⟨v, hvU⟩).mpr hvS, rfl⟩

@[simp] theorem componentProject_lift (S : Finset U) :
    componentProject U (componentLift S) = S := by
  ext v
  simp only [mem_componentProject, mem_componentLift]

/-- A specified public root absorbs all vertices outside the component. -/
def componentMap (r : U) (v : V) : U :=
  if hv : v ∈ U then ⟨v, hv⟩ else r

@[simp] theorem componentMap_coe (r v : U) : componentMap r v.val = v := by
  simp [componentMap, v.property]

theorem componentMap_surjective (r : U) : Function.Surjective (componentMap r) := by
  intro v
  exact ⟨v.val, componentMap_coe r v⟩

@[simp] theorem componentVertex_card (U : Finset V) : Fintype.card U = U.card := by
  simp

theorem componentVertex_card_le (r : U) : Fintype.card U ≤ Fintype.card V :=
  Fintype.card_le_of_surjective _ (componentMap_surjective r)

theorem componentMap_pull (r : U) (S : Finset U) :
    pull (componentMap r) S =
      if r ∈ S then componentLift S ∪ Uᶜ else componentLift S := by
  by_cases hr : r ∈ S
  · rw [if_pos hr]
    ext v
    by_cases hv : v ∈ U
    · have hm : v ∈ componentLift S ↔ (⟨v, hv⟩ : U) ∈ S :=
        mem_componentLift S ⟨v, hv⟩
      simp [mem_pull, componentMap, hv, hm]
    · have hn : v ∉ componentLift S := fun h => hv (componentLift_subset S h)
      simp [mem_pull, componentMap, hv, hr, hn]
  · rw [if_neg hr]
    ext v
    by_cases hv : v ∈ U
    · have hm : v ∈ componentLift S ↔ (⟨v, hv⟩ : U) ∈ S :=
        mem_componentLift S ⟨v, hv⟩
      simp [mem_pull, componentMap, hv, hm]
    · have hn : v ∉ componentLift S := fun h => hv (componentLift_subset S h)
      simp [mem_pull, componentMap, hv, hr, hn]

/-- Intersecting with a zero-boundary component cannot increase cut value. -/
theorem component_cut_inter_le (G : WeightedGraph V) (hU : G.cut U = 0)
    (S : Finset V) : G.cut (S ∩ U) ≤ G.cut S := by
  have h := G.cut_submodular S U
  have hn := G.cut_nonneg (S ∪ U)
  rw [hU] at h
  linarith

theorem component_cut_union_le (G : WeightedGraph V) (hU : G.cut U = 0)
    (S : Finset V) : G.cut (S ∪ U) ≤ G.cut S := by
  have h := G.cut_submodular S U
  have hn := G.cut_nonneg (S ∩ U)
  rw [hU] at h
  linarith

/-- Adding every outside vertex to an internal shore changes no cut value. -/
theorem component_cut_add_outside (G : WeightedGraph V) (hU : G.cut U = 0)
    {S : Finset V} (hS : S ⊆ U) : G.cut (S ∪ Uᶜ) = G.cut S := by
  have hUc : G.cut Uᶜ = 0 := by rw [cut_compl, hU]
  apply le_antisymm (component_cut_union_le G hUc S)
  have he : (S ∪ Uᶜ) ∩ U = S := by
    ext v
    constructor
    · intro hv
      obtain ⟨hvSU, hvU⟩ := Finset.mem_inter.mp hv
      rcases Finset.mem_union.mp hvSU with hvS | hvUc
      · exact hvS
      · exact ((Finset.mem_compl.mp hvUc) hvU).elim
    · intro hv
      exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ hv, hS hv⟩
  have h := component_cut_inter_le G hU (S ∪ Uᶜ)
  simpa only [he] using h

/-- The contraction oracle is exactly the cut oracle on the compact component. -/
theorem component_contract_cut (G : WeightedGraph V) (r : U)
    (hU : G.cut U = 0) (S : Finset U) :
    (G.contract (componentMap r)).cut S = G.cut (componentLift S) := by
  rw [cut_contract, componentMap_pull]
  split_ifs
  · exact component_cut_add_outside G hU (componentLift_subset S)
  · rfl

theorem component_contraction_promise {M : ℕ} (G : WeightedGraph V)
    (hG : InputPromise M G) (r : U) :
    InputPromise M (G.contract (componentMap r)) :=
  ⟨integral_contract G hG.1 _, (edgeMass_contract_le G _).trans hG.2⟩

/-- Every original separating shore yields a no-more-expensive compact shore. -/
theorem component_project_cut_le (G : WeightedGraph V) (r : U)
    (hU : G.cut U = 0) (S : Finset V) :
    (G.contract (componentMap r)).cut (componentProject U S) ≤ G.cut S := by
  rw [component_contract_cut G r hU, componentLift_project]
  exact component_cut_inter_le G hU S

theorem component_minCut_lift (G : WeightedGraph V) (r : U) (hU : G.cut U = 0)
    {s t : U} {S : Finset U}
    (hS : IsSTMinCut (G.contract (componentMap r)) s t S) :
    IsSTMinCut G s.val t.val (componentLift S) := by
  refine ⟨(mem_componentLift S s).mpr hS.1,
    fun ht => hS.2.1 ((mem_componentLift S t).mp ht), fun A hsA htA => ?_⟩
  calc
    _ = (G.contract (componentMap r)).cut S := (component_contract_cut G r hU S).symm
    _ ≤ (G.contract (componentMap r)).cut (componentProject U A) := hS.2.2 _
      ((mem_componentProject A s).mpr hsA)
      (fun ht => htA ((mem_componentProject A t).mp ht))
    _ ≤ G.cut A := component_project_cut_le G r hU A

theorem component_minCut_project (G : WeightedGraph V) (r : U) (hU : G.cut U = 0)
    {s t : U} {S : Finset V} (hS : IsSTMinCut G s.val t.val S) :
    IsSTMinCut (G.contract (componentMap r)) s t (componentProject U S) := by
  refine ⟨(mem_componentProject S s).mpr hS.1,
    fun ht => hS.2.1 ((mem_componentProject S t).mp ht), fun A hsA htA => ?_⟩
  calc
    _ ≤ G.cut S := component_project_cut_le G r hU S
    _ ≤ G.cut (componentLift A) := hS.2.2 _
      ((mem_componentLift A s).mpr hsA)
      (fun ht => htA ((mem_componentLift A t).mp ht))
    _ = _ := (component_contract_cut G r hU A).symm

/-- Canonicality is preserved after outside vertices are dropped, including
zero cuts and ties. No connectedness or positivity premise is needed. -/
theorem component_canonical_lift (G : WeightedGraph V) (r : U) (hU : G.cut U = 0)
    {s t : U} {S : Finset U}
    (hS : IsCanonicalSTCut (G.contract (componentMap r)) s t S) :
    IsCanonicalSTCut G s.val t.val (componentLift S) := by
  refine ⟨component_minCut_lift G r hU hS.1, fun A hA => ?_⟩
  have hsub := hS.2 (componentProject U A) (component_minCut_project G r hU hA)
  intro v hv
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
  exact (mem_componentProject A u).mp (hsub hu)

/-- A public compact-component call. The hidden graph and the zero-boundary
proof are absent from the program arguments. -/
def componentSTProgram {M : ℕ} {Q : ℕ → ℕ} (A : CanonicalSTFamily M Q)
    (r s t : U) : DTree (Finset V) ℝ (Finset V) (Q (Fintype.card U)) :=
  (contractDetProgram (componentMap r) (canonicalSTProgram A s t)).map componentLift

theorem componentSTProgram_correct {M : ℕ} {Q : ℕ → ℕ} (A : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (hG : InputPromise M G) (r s t : U)
    (hU : G.cut U = 0) (hst : s ≠ t) :
    IsCanonicalSTCut G s.val t.val ((componentSTProgram A r s t).eval G.cut) := by
  rw [componentSTProgram, DTree.eval_map, contractDetProgram_eval]
  exact component_canonical_lift G r hU
    (canonicalSTProgram_correct A _ (component_contraction_promise G hG r) hst)

/-- Cost uses the real component size and holds on every read history. -/
theorem componentSTProgram_cost {M : ℕ} {Q : ℕ → ℕ} (A : CanonicalSTFamily M Q)
    (r s t : U) (read : Finset V → ℝ) :
    (componentSTProgram A r s t).cost read ≤ Q U.card := by
  simpa only [componentVertex_card] using DTree.cost_le (componentSTProgram A r s t) read

end
end CutQueryComplexity.GHReduction
