import CutQueryComplexity.StarContraction2022.Quantum.UniformStars.Survival

/-! # Public quotients formed from the actual star-choice transcript -/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Quantum.UniformStars

open Finset
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

/-- An unassigned vertex remains its own label; this is total on every transcript. -/
def starTarget (f : V → Option V) (v : V) : V := (f v).getD v

def starLabels (f : V → Option V) : Finset V := univ.image (starTarget f)

def starLabel (f : V → Option V) (v : V) : starLabels f :=
  ⟨starTarget f v, mem_image.mpr ⟨v, mem_univ v, rfl⟩⟩

theorem starLabel_surjective (f : V → Option V) : Function.Surjective (starLabel f) := by
  intro w
  obtain ⟨v, _, hv⟩ := mem_image.mp w.property
  exact ⟨v, Subtype.ext hv⟩

/-- Finite labels are computed entirely from the public choices, with no empty blocks. -/
def starQuotient (f : V → Option V) : PublicQuotient V (Fin (starLabels f).card) where
  map v := (starLabels f).equivFin (starLabel f v)
  onto := (starLabels f).equivFin.surjective.comp (starLabel_surjective f)

theorem starQuotient_map_eq_iff (f : V → Option V) (u v : V) :
    (starQuotient f).map u = (starQuotient f).map v ↔ starTarget f u = starTarget f v := by
  change (starLabels f).equivFin (starLabel f u) =
    (starLabels f).equivFin (starLabel f v) ↔ _
  rw [(starLabels f).equivFin.injective.eq_iff]
  exact Subtype.ext_iff

/-- Coverage makes the public labels exactly the centers, including the p=1 case. -/
theorem starLabels_eq_centers (R : Finset V) (N : V → Finset V) (f : V → Option V)
    (hf : f ∈ (starChoiceLaw R N).support) (hc : Covered N R) : starLabels f = R := by
  apply Subset.antisymm
  · intro w hw
    obtain ⟨v, _, rfl⟩ := mem_image.mp hw
    cases he : f v with
    | none =>
        have hv : v ∈ R := by
          by_contra hv
          have hempty := (starChoiceLaw_support R N f).mp hf v
          simp only [he, starRows, hv, ite_false] at hempty
          exact (hc v hv).ne_empty hempty
        simpa only [starTarget, he, Option.getD_none] using hv
    | some w =>
        simpa only [starTarget, he, Option.getD_some] using
          (starChoiceLaw_some R N f hf v w he).2.2
  · intro r hr
    apply mem_image.mpr
    refine ⟨r, mem_univ r, ?_⟩
    simp only [starTarget, starChoiceLaw_center R N f hf r hr, Option.getD_none]

theorem starQuotient_card (R : Finset V) (N : V → Finset V) (f : V → Option V)
    (hf : f ∈ (starChoiceLaw R N).support) (hc : Covered N R) :
    Fintype.card (Fin (starLabels f).card) = R.card := by
  rw [Fintype.card_fin, starLabels_eq_centers R N f hf hc]

theorem inputRows_noncrossing (G : SimpleInput V) (S : Finset V) (v w : V)
    (hN : w ∈ Contraction.SparseCenters.inputRows G v)
    (hC : w ∉ Contraction.SparseCenters.inputCrossRows G S v) :
    v ∈ S ↔ w ∈ S := by
  have hpos : 0 < G.toWeighted.w v w := (mem_filter.mp hN).2
  by_cases hv : v ∈ S <;> by_cases hw : w ∈ S <;>
    simp_all [Contraction.SparseCenters.inputCrossRows, AllPairs.rowSupport]

/-- Every fiber of the computed map lies on one side of the surviving original shore. -/
theorem starQuotient_respects (G : SimpleInput V) (S R : Finset V) (f : V → Option V)
    (hf : f ∈ (starChoiceLaw R (Contraction.SparseCenters.inputRows G)).support)
    (ha : Avoids (Contraction.SparseCenters.inputCrossRows G S) f) :
    RespectsBlocks (starQuotient f).map S := by
  have hs (v : V) : v ∈ S ↔ starTarget f v ∈ S := by
    cases he : f v with
    | none => simp only [starTarget, he, Option.getD_none]
    | some w =>
        have hw := (starChoiceLaw_some R _ f hf v w he).2.1
        have hno : w ∉ Contraction.SparseCenters.inputCrossRows G S v := by
          simpa only [he, Option.elim_some] using ha v
        simpa only [starTarget, he, Option.getD_some] using inputRows_noncrossing G S v w hw hno
  intro u v huv
  have ht := (starQuotient_map_eq_iff f u v).mp huv
  exact (hs u).trans (ht ▸ (hs v).symm)

theorem starQuotient_surviving_minimum (G : SimpleInput V) (S R : Finset V)
    (f : V → Option V) (hS : IsMinCut G.toWeighted S)
    (hf : f ∈ (starChoiceLaw R (Contraction.SparseCenters.inputRows G)).support)
    (ha : Avoids (Contraction.SparseCenters.inputCrossRows G S) f) :
    2 ≤ (starLabels f).card ∧
      mincutValue ((starQuotient f).graph G.toWeighted) = mincutValue G.toWeighted := by
  have hs := starQuotient_respects G S R f hf ha
  exact ⟨by simpa only [Fintype.card_fin] using
    (starQuotient f).two_le_card_of_survives hs hS.1,
    (starQuotient f).mincut_eq hS hs⟩

#print axioms starQuotient
#print axioms starQuotient_map_eq_iff
#print axioms starLabels_eq_centers
#print axioms starQuotient_card
#print axioms starQuotient_respects
#print axioms starQuotient_surviving_minimum

end
end CutQueryComplexity.StarContraction2022.Quantum.UniformStars
