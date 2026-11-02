import CutQueryComplexity.GHReduction.Specification
import CutQueryComplexity.GHReduction.Programs

/-! # One-proxy contractions of isolating shores

The vertex type contains the individual vertices of the shore and one proxy for
its complement. Its cardinality is exactly `|S| + 1`; it is at most the parent
cardinality when the shore is proper. Every virtual query costs one parent query.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical
open WeightedGraph

variable {V : Type} [Fintype V] [DecidableEq V]

abbrev ShoreVertex (S : Finset V) := Option {v : V // v ∈ S}

def shoreMap (S : Finset V) (v : V) : ShoreVertex S :=
  if h : v ∈ S then some ⟨v, h⟩ else none

@[simp] theorem shoreVertex_card (S : Finset V) :
    Fintype.card (ShoreVertex S) = S.card + 1 := by simp [ShoreVertex]

theorem shoreMap_surjective {S : Finset V} (hS : S ≠ Finset.univ) :
    Function.Surjective (shoreMap S) := by
  intro x
  cases x with
  | none =>
    have hex : ∃ v, v ∉ S := by
      by_contra h
      push_neg at h
      exact hS (by ext v; simp [h v])
    obtain ⟨v, hv⟩ := hex
    exact ⟨v, by simp [shoreMap, hv]⟩
  | some v => exact ⟨v.val, by simp [shoreMap, v.property]⟩

theorem shoreVertex_card_le {S : Finset V} (hS : S ≠ Finset.univ) :
    Fintype.card (ShoreVertex S) ≤ Fintype.card V :=
  Fintype.card_le_of_surjective _ (shoreMap_surjective hS)

def shorePush (S X : Finset V) : Finset (ShoreVertex S) :=
  Finset.univ.filter (fun w => match w with | none => False | some v => v.val ∈ X)

@[simp] theorem none_not_mem_shorePush (S X : Finset V) : none ∉ shorePush S X := by
  simp [shorePush]

@[simp] theorem some_mem_shorePush (S X : Finset V) (v : {v : V // v ∈ S}) :
    some v ∈ shorePush S X ↔ v.val ∈ X := by simp [shorePush]

theorem pull_shorePush {S X : Finset V} (hX : X ⊆ S) :
    pull (shoreMap S) (shorePush S X) = X := by
  ext v
  by_cases hv : v ∈ S
  · simp [shoreMap, shorePush, hv]
  · have hx : v ∉ X := fun hx => hv (hX hx)
    simp [shoreMap, shorePush, hv, hx]

theorem pull_shore_subset {S : Finset V} {X : Finset (ShoreVertex S)}
    (hp : none ∉ X) : pull (shoreMap S) X ⊆ S := by
  intro v hv
  by_contra hs
  have := (mem_pull _ _ _).mp hv
  exact hp (by simpa [shoreMap, hs] using this)

theorem shore_contraction_promise {M : ℕ} (G : WeightedGraph V)
    (hG : InputPromise M G) (S : Finset V) :
    InputPromise M (G.contract (shoreMap S)) :=
  ⟨integral_contract G hG.1 _, (edgeMass_contract_le G _).trans hG.2⟩

/-- If a canonical isolating shore fits inside the cell, the canonical local
source–proxy solve returns that same shore after pullback. -/
theorem canonical_shorePull (G : WeightedGraph V) {R P C : Finset V}
    {v : V} (hv : v ∈ P) (hPR : P ∩ R = {v})
    (hC : IsCanonicalTraceCut G R {v} C) (hCP : C ⊆ P)
    {X : Finset (ShoreVertex P)}
    (hX : IsCanonicalSTCut (G.contract (shoreMap P)) (some ⟨v, hv⟩) none X) :
    pull (shoreMap P) X = C := by
  have hXP := pull_shore_subset hX.1.2.1
  have hvX : v ∈ pull (shoreMap P) X := by
    simpa [shoreMap, hv] using hX.1.1
  have hvC : v ∈ C := by
    have : v ∈ C ∩ R := by rw [hC.1.1]; simp
    exact (Finset.mem_inter.mp this).1
  have htrace : pull (shoreMap P) X ∩ R = {v} := by
    apply Finset.Subset.antisymm
    · exact (Finset.inter_subset_inter hXP (le_refl R)).trans (le_of_eq hPR)
    · apply Finset.singleton_subset_iff.mpr
      have hvR : v ∈ R := by
        have : v ∈ P ∩ R := by rw [hPR]; simp
        exact (Finset.mem_inter.mp this).2
      exact Finset.mem_inter.mpr ⟨hvX, hvR⟩
  have hle : G.cut (pull (shoreMap P) X) ≤ G.cut C := by
    have h := hX.1.2.2 (shorePush P C) (by simpa using hvC) (none_not_mem_shorePush _ _)
    simpa only [cut_contract, pull_shorePush hCP] using h
  have heq : G.cut (pull (shoreMap P) X) = G.cut C :=
    le_antisymm hle (hC.1.2 _ htrace)
  have hmin : IsMinTraceCut G R {v} (pull (shoreMap P) X) :=
    ⟨htrace, fun Y hY => heq ▸ hC.1.2 Y hY⟩
  have hCmin : IsSTMinCut (G.contract (shoreMap P)) (some ⟨v, hv⟩) none
      (shorePush P C) := by
    refine ⟨by simpa using hvC, none_not_mem_shorePush _ _, fun Y hvY hpY => ?_⟩
    have hYP := pull_shore_subset hpY
    have hvY' : v ∈ pull (shoreMap P) Y := by simpa [shoreMap, hv] using hvY
    have hYR : pull (shoreMap P) Y ∩ R = {v} := by
      apply Finset.Subset.antisymm
      · exact (Finset.inter_subset_inter hYP (le_refl R)).trans (le_of_eq hPR)
      · have hvR : v ∈ R := by
          have : v ∈ P ∩ R := by rw [hPR]; simp
          exact (Finset.mem_inter.mp this).2
        exact Finset.singleton_subset_iff.mpr (Finset.mem_inter.mpr ⟨hvY', hvR⟩)
    simpa only [cut_contract, pull_shorePush hCP] using hC.1.2 _ hYR
  apply Finset.Subset.antisymm
  · have hs := hX.2 (shorePush P C) hCmin
    have hpull : pull (shoreMap P) X ⊆ pull (shoreMap P) (shorePush P C) := by
      intro u hu
      exact (mem_pull _ _ _).mpr (hs ((mem_pull _ _ _).mp hu))
    rwa [pull_shorePush hCP] at hpull
  · exact hC.2 _ hmin

/-- The source–proxy call used after the cells have been computed. -/
def shoreCutProgram {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (P : Finset V) (v : {v : V // v ∈ P}) :
    DTree (Finset V) ℝ (Finset V) (Q (Fintype.card (ShoreVertex P))) :=
  (contractDetProgram (shoreMap P) (canonicalSTProgram family (some v) none)).map
    (pull (shoreMap P))

theorem shoreCutProgram_correct {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (hG : InputPromise M G) {R P C : Finset V}
    (v : {v : V // v ∈ P}) (hPR : P ∩ R = {v.val})
    (hC : IsCanonicalTraceCut G R {v.val} C) (hCP : C ⊆ P) :
    (shoreCutProgram family P v).eval G.cut = C := by
  rw [shoreCutProgram, DTree.eval_map, contractDetProgram_eval]
  apply canonical_shorePull G v.property hPR hC hCP
  exact canonicalSTProgram_correct family _ (shore_contraction_promise G hG P) (by simp)

end
end CutQueryComplexity.GHReduction
