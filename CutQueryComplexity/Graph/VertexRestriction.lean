import CutQueryComplexity.Graph.InducedCut

/-! # Restriction to the actual vertex subtype

This differs from `induce`, which retains isolated outside vertices. Shores
of the subtype correspond to subsets of `U`, and its cuts are local cuts.
-/

namespace CutQueryComplexity.WeightedGraph
noncomputable section
open scoped Classical
variable {V : Type} [Fintype V] [DecidableEq V]

def onVertices (G : WeightedGraph V) (U : Finset V) : WeightedGraph U where
  w u v := G.w u.val v.val
  symm u v := G.symm _ _
  nonneg u v := G.nonneg _ _
  diag u := G.diag _

def projectShore (U S : Finset V) : Finset U := Finset.univ.filter (fun u => u.val ∈ S)

def liftShore (U : Finset V) (T : Finset U) : Finset V := T.image Subtype.val

@[simp] theorem mem_projectShore (U S : Finset V) (u : U) :
    u ∈ projectShore U S ↔ u.val ∈ S := by simp [projectShore]

@[simp] theorem mem_liftShore (U : Finset V) (T : Finset U) (u : U) :
    u.val ∈ liftShore U T ↔ u ∈ T := by
  constructor
  · intro hu
    obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hu
    have hvu : v = u := Subtype.ext he
    simpa only [hvu] using hv
  · intro hu
    exact Finset.mem_image.mpr ⟨u, hu, rfl⟩

theorem liftShore_subset (U : Finset V) (T : Finset U) : liftShore U T ⊆ U := by
  intro u hu
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hu
  exact v.property

theorem lift_projectShore {U S : Finset V} (hS : S ⊆ U) :
    liftShore U (projectShore U S) = S := by
  ext v
  constructor
  · intro hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    exact (mem_projectShore _ _ _).mp hu
  · intro hv
    exact Finset.mem_image.mpr ⟨⟨v, hS hv⟩, (mem_projectShore _ _ _).mpr hv, rfl⟩

@[simp] theorem project_liftShore (U : Finset V) (T : Finset U) :
    projectShore U (liftShore U T) = T := by ext; simp

theorem LocalShore.project {U S : Finset V} (h : LocalShore U S) :
    ProperShore (projectShore U S) := by
  obtain ⟨u, hu⟩ := h.2.1
  obtain ⟨v, hv⟩ := h.2.2
  obtain ⟨hvU, hvS⟩ := Finset.mem_sdiff.mp hv
  refine ⟨⟨⟨u, h.1 hu⟩, (mem_projectShore _ _ _).mpr hu⟩, ?_⟩
  intro he
  have hv : (⟨v, hvU⟩ : U) ∈ projectShore U S := by rw [he]; simp
  exact hvS ((mem_projectShore _ _ _).mp hv)

theorem localShore_lift {U : Finset V} {T : Finset U} (h : ProperShore T) :
    LocalShore U (liftShore U T) := by
  obtain ⟨u, hu⟩ := h.1
  have hn : ∃ v : U, v ∉ T := by
    by_contra hn
    push Not at hn
    exact h.2 (Finset.eq_univ_of_forall hn)
  obtain ⟨v, hv⟩ := hn
  exact ⟨liftShore_subset U T, ⟨u.val, (mem_liftShore _ _ _).mpr hu⟩,
    ⟨v.val, Finset.mem_sdiff.mpr ⟨v.property, fun he => hv ((mem_liftShore _ _ _).mp he)⟩⟩⟩

theorem onVertices_cut_project (G : WeightedGraph V) (U S : Finset V) :
    (G.onVertices U).cut (projectShore U S) = G.localCut U S := by
  rw [cut_eq_sum_ite]
  simp only [mem_projectShore]
  change (∑ u : U, ∑ v : U, if u.val ∈ S ∧ v.val ∉ S then G.w u.val v.val else 0) = _
  rw [Finset.sum_coe_sort U (fun u =>
    ∑ v : U, if u ∈ S ∧ v.val ∉ S then G.w u v.val else 0)]
  have hinner (u : V) :
      (∑ v : U, if u ∈ S ∧ v.val ∉ S then G.w u v.val else 0) =
        ∑ v ∈ U, if u ∈ S ∧ v ∉ S then G.w u v else 0 :=
    Finset.sum_coe_sort U (fun v => if u ∈ S ∧ v ∉ S then G.w u v else 0)
  simp_rw [hinner]
  have hL : U.filter (fun u => u ∈ S) = S ∩ U := by ext; simp [and_comm]
  have hR : U.filter (fun v => v ∉ S) = U \ S := by ext; simp
  simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp_rw [← Finset.sum_filter]
  rw [hL, hR]
  rfl

theorem onVertices_cut_lift (G : WeightedGraph V) (U : Finset V) (T : Finset U) :
    (G.onVertices U).cut T = G.localCut U (liftShore U T) := by
  rw [← G.onVertices_cut_project, project_liftShore]

end
end CutQueryComplexity.WeightedGraph
