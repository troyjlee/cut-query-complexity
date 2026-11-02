import CutQueryComplexity.Hierarchy.Refine
import CutQueryComplexity.Discovery.Auxiliary
import CutQueryComplexity.Discovery.TreeCompression

/-! # The initial hierarchy of a phase (Lemma 32) and hierarchy rounding (eq. (H-rounding))

**Rounding.** For an explicit graph `H` with a hierarchy of distortion `α` and a terminal set
`C`, terminal compression (Lemma 26) gives a fixed partition `π` of the vertices with at most
`max 1 (2|C| − 2)` parts, such that every shore `S` has a union of parts `Ŝ` agreeing with `S`
on `C` with `c_H(Ŝ) ≤ α c_H(S)` (`exists_rounding`).

**Certification.** For the auxiliary graph `J = auxGraph G K π` on `V ⊕ ι`, any hierarchy of
`J` with distortion `β`, read on the leaves of `V` only (`restrictInl`), satisfies
`R_G(S) ≤ β Ψ(S)` with canonical capacities of `G` (`rep_restrictInl_le`). The leaves of the
added vertices become free nodes, so no compression is needed. If `Ψ ≥ 4Nt` on every proper
shore and `Ψ ≤ A c_G + 2Nt`, then every minimum cut has `R_G(S*) ≤ 2βA λ`
(`restrictInl_promise`).
-/

namespace CutQueryComplexity
namespace Hierarchy

open TwoRespecting WeightedGraph Discovery Finset

variable {V : Type} [Fintype V] [DecidableEq V]

namespace Hier

variable {N : Type} [Fintype N] [DecidableEq N]

omit [Fintype V] [DecidableEq V] in
/-- The label cost of a binary labelling is the tree-compression cost. -/
theorem labelCost_toReal_eq_cost (H : Hier V N) (cap : N → ℝ) (f : N → Bool) :
    H.labelCost cap (toReal f) = Discovery.cost H.T cap f := by
  unfold labelCost Discovery.cost edges
  refine sum_congr rfl fun x _ => ?_
  cases hx : f x <;> cases hp : f (H.T.parent x) <;> simp [toReal, hx, hp]

omit [Fintype V] [DecidableEq V] in
theorem labelCost_mono (H : Hier V N) {cap cap' : N → ℝ} (h : ∀ x ∈ H.edges, cap x ≤ cap' x)
    (ℓ : N → ℝ) : H.labelCost cap ℓ ≤ H.labelCost cap' ℓ :=
  sum_le_sum fun x hx => mul_le_mul_of_nonneg_right (h x hx) (abs_nonneg _)

/-! ## Rounding to a partition -/

/-- The kept nodes of terminal compression for the terminals `C`, chosen offline. -/
noncomputable def keep (H : Hier V N) (cap : N → ℝ) (hcap : ∀ x, 0 ≤ cap x) (C : Finset V) :
    Finset N :=
  Classical.choose (tree_compression (T := H.T) hcap (C.image H.leaf))

/-- The partition map: each vertex goes to the kept representative of its leaf. -/
noncomputable def part (H : Hier V N) (cap : N → ℝ) (hcap : ∀ x, 0 ≤ cap x) (C : Finset V)
    (v : V) : N :=
  Discovery.rep H.T (H.keep cap hcap C) (H.leaf v)

omit [Fintype V] [DecidableEq V] in
theorem keep_spec (H : Hier V N) (cap : N → ℝ) (hcap : ∀ x, 0 ≤ cap x) (C : Finset V) :
    H.T.root ∈ H.keep cap hcap C ∧ (∀ v, Discovery.rep H.T (H.keep cap hcap C) v ∈
        H.keep cap hcap C) ∧
      (H.keep cap hcap C).card ≤ max 1 (2 * (C.image H.leaf).card - 2) ∧
      ∀ ℓ : N → Bool, ∃ f : N → Bool, (∀ t ∈ C.image H.leaf, f t = ℓ t) ∧
        (∀ v, f v = f (Discovery.rep H.T (H.keep cap hcap C) v)) ∧
        ∀ g : N → Bool, (∀ t ∈ C.image H.leaf, g t = ℓ t) →
          Discovery.cost H.T cap f ≤ Discovery.cost H.T cap g := by
  obtain ⟨h1, h2, h3, -, h5⟩ :=
    Classical.choose_spec (tree_compression (T := H.T) hcap (C.image H.leaf))
  exact ⟨h1, h2, h3, h5⟩

omit [DecidableEq V] in
/-- The partition has at most `max 1 (2|C| − 2)` parts. -/
theorem card_image_part_le (H : Hier V N) (cap : N → ℝ) (hcap : ∀ x, 0 ≤ cap x)
    (C : Finset V) : (univ.image (H.part cap hcap C)).card ≤ max 1 (2 * C.card - 2) := by
  obtain ⟨-, hmem, hcard, -⟩ := H.keep_spec cap hcap C
  have hsub : univ.image (H.part cap hcap C) ⊆ H.keep cap hcap C := by
    intro x hx
    obtain ⟨v, -, rfl⟩ := mem_image.mp hx
    exact hmem _
  refine (card_le_card hsub).trans (hcard.trans ?_)
  have := card_image_le (s := C) (f := H.leaf)
  omega

/-- **Rounding (eq. (H-rounding)).** If the hierarchy approximates the cuts of `H` within
`α`, every shore has a union of parts agreeing with it on `C` whose `H`-cut is at most
`α c_H(S)`. -/
theorem exists_rounding (H : Hier V N) (Hg : WeightedGraph V) {α : ℝ}
    (hdist : ∀ S, H.rep (H.canon Hg) S ≤ α * Hg.cut S) (C S : Finset V) :
    ∃ T : Finset N,
      pull (H.part (H.canon Hg) (fun _ => Hg.cut_nonneg _) C) T ∩ C = S ∩ C ∧
        Hg.cut (pull (H.part (H.canon Hg) (fun _ => Hg.cut_nonneg _) C) T) ≤ α * Hg.cut S := by
  set cap := H.canon Hg
  have hcap : ∀ x, 0 ≤ cap x := fun _ => Hg.cut_nonneg _
  set π := H.part cap hcap C
  obtain ⟨-, -, -, hgood⟩ := H.keep_spec cap hcap C
  obtain ⟨ℓ, hℓ, hRℓ⟩ := H.exists_rep_eq cap S
  obtain ⟨f, hfC, hfrep, hfmin⟩ := hgood ℓ
  refine ⟨univ.filter fun i => f i = true, ?_, ?_⟩
  · ext v
    simp only [mem_inter, mem_pull, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hv, hvC⟩
      refine ⟨?_, hvC⟩
      have h1 : f (H.leaf v) = true := by rw [hfrep]; exact hv
      rw [hfC _ (mem_image_of_mem _ hvC), hℓ] at h1
      simpa using h1
    · rintro ⟨hvS, hvC⟩
      refine ⟨?_, hvC⟩
      have h1 : f (H.leaf v) = true := by
        rw [hfC _ (mem_image_of_mem _ hvC), hℓ]; simpa using hvS
      simp only [π, part]
      rw [← hfrep]; exact h1
  · have hext : H.Extends (pull π (univ.filter fun i => f i = true)) f := by
      intro v
      simp only [mem_pull, mem_filter, mem_univ, true_and, π, part]
      rw [← hfrep]
      cases f (H.leaf v) <;> simp
    calc Hg.cut (pull π (univ.filter fun i => f i = true))
        ≤ H.labelCost cap (toReal f) := cut_le_labelCost Hg hext
      _ = Discovery.cost H.T cap f := H.labelCost_toReal_eq_cost cap f
      _ ≤ Discovery.cost H.T cap ℓ := hfmin ℓ fun _ _ => rfl
      _ = H.rep cap S := by rw [hRℓ, H.labelCost_toReal_eq_cost]
      _ ≤ α * Hg.cut S := hdist S

/-! ## Reading a hierarchy of the auxiliary graph on the original vertices -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Keep the tree and use only the leaves of `V`; the leaves of `ι` become free nodes. -/
def restrictInl (H : Hier (V ⊕ ι) N) : Hier V N :=
  ⟨H.T, fun v => H.leaf (.inl v), H.leaf_inj.comp Sum.inl_injective⟩

omit [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N] [Fintype ι] [DecidableEq ι] in
@[simp] theorem restrictInl_T (H : Hier (V ⊕ ι) N) : H.restrictInl.T = H.T := rfl

omit [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι] in
theorem restrictInl_leafChildless {H : Hier (V ⊕ ι) N} (h : H.LeafChildless) :
    H.restrictInl.LeafChildless := fun v => h (.inl v)

omit [Fintype V] [DecidableEq V] [DecidableEq N] [Fintype ι] [DecidableEq ι] in
@[simp] theorem restrictInl_height (H : Hier (V ⊕ ι) N) : H.restrictInl.height = H.height := rfl

omit [DecidableEq V] [Fintype N] [DecidableEq ι] in
theorem cluster_eq_disjSum (H : Hier (V ⊕ ι) N) (x : N) :
    H.cluster x = (H.restrictInl.cluster x).disjSum
      (univ.filter fun i => H.T.IsAnc x (H.leaf (.inr i))) := by
  ext y
  rcases y with v | i
  · rw [mem_cluster, Finset.inl_mem_disjSum, mem_cluster]; rfl
  · rw [mem_cluster, Finset.inr_mem_disjSum]; simp

/-- `R_G(S) ≤ β Ψ(S)` for the restriction of a hierarchy of `J` with distortion `β`. -/
theorem rep_restrictInl_le (G K : WeightedGraph V) (hKG : ∀ u v, K.w u v ≤ G.w u v)
    (π : V → ι) (H : Hier (V ⊕ ι) N) {β : ℝ}
    (hdist : ∀ S, H.rep (H.canon (auxGraph G K π)) S ≤ β * (auxGraph G K π).cut S)
    (S : Finset V) :
    H.restrictInl.rep (H.restrictInl.canon G) S ≤ β * psi G K π S := by
  set J := auxGraph G K π
  obtain ⟨T, -, hT⟩ := exists_mem_eq_inf' (univ_nonempty (α := Finset ι))
    (fun T : Finset ι => J.cut (S.disjSum T))
  have hpsi : psi G K π S = J.cut (S.disjSum T) := by rw [psi_eq_auxGraph, hT]
  obtain ⟨ℓ, hℓ, hRℓ⟩ := H.exists_rep_eq (H.canon J) (S.disjSum T)
  have hext : H.restrictInl.Extends S ℓ := by
    intro v
    have := hℓ (.inl v)
    simpa [restrictInl] using this
  have hcap : ∀ x ∈ H.restrictInl.edges, H.restrictInl.canon G x ≤ H.canon J x := by
    intro x _
    simp only [canon]
    rw [cluster_eq_disjSum H x]
    set A := H.restrictInl.cluster x
    calc G.cut A ≤ psi G K π A := psi_lower G K hKG π A
      _ ≤ J.cut (A.disjSum (univ.filter fun i => H.T.IsAnc x (H.leaf (.inr i)))) := by
          rw [psi_eq_auxGraph]
          exact inf'_le _ (mem_univ _)
  calc H.restrictInl.rep (H.restrictInl.canon G) S
      ≤ H.restrictInl.labelCost (H.restrictInl.canon G) (toReal ℓ) := rep_le _ hext
    _ ≤ H.restrictInl.labelCost (H.canon J) (toReal ℓ) := labelCost_mono _ hcap _
    _ = H.rep (H.canon J) (S.disjSum T) := by rw [hRℓ]; rfl
    _ ≤ β * J.cut (S.disjSum T) := hdist _
    _ = β * psi G K π S := by rw [hpsi]

/-- **Lemma 32, certification branch.** If `Ψ ≤ A c_G + 2Nt` everywhere and `Ψ ≥ 4Nt` on
every proper shore, the restricted hierarchy has promise `2βA` at every minimum cut. -/
theorem restrictInl_promise (G K : WeightedGraph V) (hKG : ∀ u v, K.w u v ≤ G.w u v)
    (π : V → ι) (H : Hier (V ⊕ ι) N) {β A e : ℝ} (hβ : 0 ≤ β)
    (hdist : ∀ S, H.rep (H.canon (auxGraph G K π)) S ≤ β * (auxGraph G K π).cut S)
    (hup : ∀ S, psi G K π S ≤ A * G.cut S + e)
    (hμ : ∀ S, ProperShore S → 2 * e ≤ psi G K π S) {S : Finset V} (hS : IsMinCut G S) :
    H.restrictInl.rep (H.restrictInl.canon G) S ≤ 2 * β * A * mincutValue G := by
  have hSval : G.cut S = mincutValue G := by
    obtain ⟨S0, hS0⟩ : (properShores V).Nonempty := ⟨S, (mem_properShores S).mpr hS.1⟩
    exact le_antisymm (by
      rw [mincutValue, dite_eq_left ⟨S0, hS0⟩]
      exact le_inf' _ _ fun T hT => hS.2 T ((mem_properShores T).mp hT)) (mincutValue_le G hS.1)
  have h1 := hup S
  have h2 := hμ S hS.1
  have hpsi : psi G K π S ≤ 2 * A * mincutValue G := by
    rw [hSval] at h1; linarith
  calc _ ≤ β * psi G K π S := rep_restrictInl_le G K hKG π H hdist S
    _ ≤ β * (2 * A * mincutValue G) := mul_le_mul_of_nonneg_left hpsi hβ
    _ = 2 * β * A * mincutValue G := by ring

end Hier

end Hierarchy
end CutQueryComplexity
