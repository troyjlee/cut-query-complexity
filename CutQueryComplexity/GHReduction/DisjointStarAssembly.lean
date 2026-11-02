import CutQueryComplexity.GHReduction.SteinerJoinInterfaces

/-! # Successful assembly across disjoint child shores

The public list fold is the implemented checked assembly. Its guards follow
from the recursive trees' terminal placement and attachment behavior on these
specific shores. Guard success is proved by induction; it is not a premise.
The same induction proves exact terminal coverage and preserves the full
minimum-shore contract, including zero bridge values.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical
open WeightedGraph

variable {V : Type} [Fintype V] [DecidableEq V]

def starAssemblySteps (r : V) (child : V → PackedSteinerTree V)
    (S : V → Finset V) (value : V → ℝ) (L : List V) : List (SteinerAssemblyStep V) :=
  L.map (fun i => ⟨child i, (S i)ᶜ, r, i, value i⟩)

def assembleDisjointStar (base : PackedSteinerTree V) (r : V)
    (child : V → PackedSteinerTree V) (S : V → Finset V) (value : V → ℝ) (L : List V) :
    Option (PackedSteinerTree V) := assembleSteinerSteps base (starAssemblySteps r child S value L)

/-- The recursive premises describe actual supplied child trees and concrete
separating cuts. No reduction, query bound, or successful-join field is assumed. -/
theorem assembleDisjointStar_success (G : WeightedGraph V) (r : V)
    (child : V → PackedSteinerTree V) (S : V → Finset V) (value : V → ℝ) (L : List V) :
    ∀ base : PackedSteinerTree V,
      IsSteinerCutTree G base.value → Represents base r →
      L.Pairwise (fun i j => Disjoint (S i) (S j)) →
      (∀ i ∈ L, Represents (child i) i) →
      (∀ i ∈ L, ∀ u, (child i).value.terminal u ∈ S i) →
      (∀ i ∈ L, ∀ x, x ∉ S i → (child i).value.attach x = (child i).value.attach r) →
      (∀ i ∈ L, IsSteinerCutTree G (child i).value) →
      (∀ i ∈ L, IsSTMinCut G i r (S i)) →
      (∀ i ∈ L, value i = G.cut (S i)) →
      (∀ i ∈ L, ∀ u, base.value.terminal u ∉ S i) →
      (∀ i ∈ L, ∀ x ∈ S i, ∀ y ∈ S i, base.value.attach x = base.value.attach y) →
      ∃ out, assembleDisjointStar base r child S value L = some out ∧
        IsSteinerCutTree G out.value ∧ Represents out r ∧
        ∀ x, Represents out x ↔ Represents base x ∨ ∃ i ∈ L, Represents (child i) x := by
  induction L with
  | nil =>
      intro base hbase hr _ _ _ _ _ _ _ _ _
      refine ⟨base, rfl, hbase, hr, ?_⟩
      intro x
      simp
  | cons i L ih =>
      intro base hbase hr hdisj hrep hin hout hcorrect hcut hvalue havoid hconstant
      have hi : i ∈ i :: L := List.mem_cons_self
      obtain ⟨hheadDisjoint, htailDisjoint⟩ := List.pairwise_cons.mp hdisj
      obtain ⟨u, hu⟩ := hrep i hi
      have hiS : i ∈ S i := by simpa only [hu] using hin i hi u
      have hguard : SteinerJoinGuard base (child i) (S i)ᶜ r i := by
        refine ⟨hr, hrep i hi, ?_, ?_, ?_, ?_⟩
        · intro v
          exact Finset.mem_compl.mpr (havoid i hi v)
        · intro v
          simpa only [Finset.mem_compl, not_not] using hin i hi v
        · intro x hx
          exact hconstant i hi x (by simpa only [Finset.mem_compl, not_not] using hx) i hiS
        · intro x hx
          exact hout i hi x (Finset.mem_compl.mp hx)
      obtain ⟨middle, hmiddle⟩ := checkedSteinerJoin_exists base (child i) (S i)ᶜ r i (value i) hguard
      have hmcorrect : IsSteinerCutTree G middle.value :=
        checkedSteinerJoin_correct G base (child i) hbase (hcorrect i hi) (S i)ᶜ r i (value i)
          (stMinCut_compl G (hcut i hi)) (by rw [cut_compl]; exact hvalue i hi) middle hmiddle
      have hmrep (x : V) : Represents middle x ↔ Represents base x ∨ Represents (child i) x :=
        checkedSteinerJoin_represents base (child i) (S i)ᶜ r i (value i) hmiddle x
      have hmr : Represents middle r := (hmrep r).mpr (Or.inl hr)
      have hmavoid : ∀ j ∈ L, ∀ v, middle.value.terminal v ∉ S j := by
        intro j hj v hvj
        have hv : Represents middle (middle.value.terminal v) := ⟨v, rfl⟩
        rcases (hmrep _).mp hv with ⟨w, hw⟩ | ⟨w, hw⟩
        · exact havoid j (List.mem_cons_of_mem _ hj) w (hw.symm ▸ hvj)
        · exact Finset.disjoint_left.mp (hheadDisjoint j hj) (hin i hi w) (hw.symm ▸ hvj)
      have hmconstant : ∀ j ∈ L, ∀ x ∈ S j, ∀ y ∈ S j,
          middle.value.attach x = middle.value.attach y := by
        intro j hj x hx y hy
        have hxnot : x ∉ S i := fun hxi => Finset.disjoint_left.mp (hheadDisjoint j hj) hxi hx
        have hynot : y ∉ S i := fun hyi => Finset.disjoint_left.mp (hheadDisjoint j hj) hyi hy
        exact checkedSteinerJoin_attach_left base (child i) (S i)ᶜ r i (value i) hmiddle
          (Finset.mem_compl.mpr hxnot) (Finset.mem_compl.mpr hynot)
          (hconstant j (List.mem_cons_of_mem _ hj) x hx y hy)
      obtain ⟨out, hfinish, hfinal, hroot, hcoverage⟩ := ih middle hmcorrect hmr htailDisjoint
        (fun j hj => hrep j (List.mem_cons_of_mem _ hj))
        (fun j hj => hin j (List.mem_cons_of_mem _ hj))
        (fun j hj => hout j (List.mem_cons_of_mem _ hj))
        (fun j hj => hcorrect j (List.mem_cons_of_mem _ hj))
        (fun j hj => hcut j (List.mem_cons_of_mem _ hj))
        (fun j hj => hvalue j (List.mem_cons_of_mem _ hj)) hmavoid hmconstant
      refine ⟨out, ?_, hfinal, hroot, ?_⟩
      · simpa only [assembleDisjointStar, starAssemblySteps, List.map_cons, assembleSteinerSteps,
          hmiddle, Option.bind_some] using hfinish
      · intro x
        rw [hcoverage x, hmrep x]
        constructor
        · rintro ((hb | hc) | ⟨j, hj, hc⟩)
          · exact Or.inl hb
          · exact Or.inr ⟨i, hi, hc⟩
          · exact Or.inr ⟨j, List.mem_cons_of_mem _ hj, hc⟩
        · rintro (hb | ⟨j, hj, hc⟩)
          · exact Or.inl (Or.inl hb)
          · rcases List.mem_cons.mp hj with he | hj
            · subst j
              exact Or.inl (Or.inr hc)
            · exact Or.inr ⟨j, hj, hc⟩

end
end CutQueryComplexity.GHReduction
