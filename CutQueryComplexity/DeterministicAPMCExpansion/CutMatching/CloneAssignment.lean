import CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.Basic
import CutQueryComplexity.DeterministicAPMCExpansion.Flow.RouteEndpoints
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Basic

/-!
# Assigning actual routes to unused clone slots

Route multiplicities at each original endpoint are embedded into the public
source and sink clone fibers. The resulting partial bijection is extended to
the entire bisection. Unused source slots identify fake pairs. All choices use
only the explicit routes and the public bisection; no graph is an input.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.CutMatching

open Finset Flow
open scoped Classical
noncomputable section

variable {V C I : Type} [Fintype V] [DecidableEq V]
  [Fintype C] [DecidableEq C] [Fintype I] [DecidableEq I]

def labelFiberEmbedding (f : I → V) (g : C → V)
    (h : ∀ v, Fintype.card {i // f i = v} ≤ Fintype.card {c // g c = v}) (v : V) :
    {i // f i = v} ↪ {c // g c = v} :=
  Classical.choice (Function.Embedding.nonempty_of_card_le (h v))

def labelEmbedding (f : I → V) (g : C → V)
    (h : ∀ v, Fintype.card {i // f i = v} ≤ Fintype.card {c // g c = v}) : I ↪ C :=
  (Equiv.sigmaFiberEquiv f).symm.toEmbedding.trans
    ((Function.Embedding.sigmaMap (Function.Embedding.refl V) (labelFiberEmbedding f g h)).trans
      (Equiv.sigmaFiberEquiv g).toEmbedding)

theorem labelEmbedding_label (f : I → V) (g : C → V)
    (h : ∀ v, Fintype.card {i // f i = v} ≤ Fintype.card {c // g c = v}) (i : I) :
    g (labelEmbedding f g h i) = f i :=
  (labelFiberEmbedding f g h (f i) ⟨i, rfl⟩).property

def bipartiteMate (S : Finset C) (e : S ≃ ↥(Sᶜ)) (c : C) : C :=
  if hc : c ∈ S then (e ⟨c, hc⟩).val else (e.symm ⟨c, mem_compl.mpr hc⟩).val

theorem bipartiteMate_out (S : Finset C) (e : S ≃ ↥(Sᶜ)) {c : C} (hc : c ∈ S) :
    bipartiteMate S e c ∉ S := by
  rw [bipartiteMate, dif_pos hc]
  exact mem_compl.mp (e ⟨c, hc⟩).property

theorem bipartiteMate_in (S : Finset C) (e : S ≃ ↥(Sᶜ)) {c : C} (hc : c ∉ S) :
    bipartiteMate S e c ∈ S := by
  rw [bipartiteMate, dif_neg hc]
  exact (e.symm ⟨c, mem_compl.mpr hc⟩).property

theorem bipartiteMate_involutive (S : Finset C) (e : S ≃ ↥(Sᶜ)) :
    Function.Involutive (bipartiteMate S e) := by
  intro c
  by_cases hc : c ∈ S
  · have he : bipartiteMate S e c = (e ⟨c, hc⟩).val := by
      simp only [bipartiteMate, dite_eq_left hc]
    rw [he]
    rw [bipartiteMate, dite_eq_right (mem_compl.mp (e ⟨c, hc⟩).property)]
    exact congrArg Subtype.val (e.symm_apply_apply ⟨c, hc⟩)
  · have he : bipartiteMate S e c = (e.symm ⟨c, mem_compl.mpr hc⟩).val := by
      simp only [bipartiteMate, dite_eq_right hc]
    rw [he]
    rw [bipartiteMate, dite_eq_left (e.symm ⟨c, mem_compl.mpr hc⟩).property]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨c, mem_compl.mpr hc⟩)

def matchingOfEquiv (S : Finset C) (e : S ≃ ↥(Sᶜ)) : Matching C where
  mate :=
    { toFun := bipartiteMate S e
      invFun := bipartiteMate S e
      left_inv := bipartiteMate_involutive S e
      right_inv := bipartiteMate_involutive S e }
  involutive := bipartiteMate_involutive S e
  no_fixed c := by
    intro he
    change bipartiteMate S e c = c at he
    by_cases hc : c ∈ S
    · have hm := bipartiteMate_out S e hc
      rw [he] at hm
      exact hm hc
    · have hm := bipartiteMate_in S e hc
      rw [he] at hm
      exact hc hm

theorem matchingOfEquiv_crosses (S : Finset C) (e : S ≃ ↥(Sᶜ)) :
    (matchingOfEquiv S e).Crosses S := by
  intro c
  constructor
  · exact bipartiteMate_out S e
  · intro hm
    by_contra hc
    exact hm (bipartiteMate_in S e hc)

/-- Extend the routed pairs, preserving each one literally. -/
theorem exists_matching_extends (cut : Bisection C) (left right : I ↪ C)
    (hleft : ∀ i, left i ∈ cut.shore) (hright : ∀ i, right i ∈ cut.shoreᶜ) :
    ∃ M : Matching C, M.Crosses cut.shore ∧ ∀ i, M.mate (left i) = right i := by
  let L : I ↪ cut.shore :=
    ⟨fun i => ⟨left i, hleft i⟩, fun i j h => left.injective (congrArg Subtype.val h)⟩
  let selected : Finset cut.shore := univ.image L
  let partner : cut.shore → C := fun x =>
    if h : ∃ i, L i = x then right (Classical.choose h) else x.val
  have hpartner (i : I) : partner (L i) = right i := by
    have hex : ∃ j, L j = L i := ⟨i, rfl⟩
    have he : Classical.choose hex = i := L.injective (Classical.choose_spec hex)
    simp only [partner, dif_pos hex, he]
  have hinto : selected.image partner ⊆ cut.shoreᶜ := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hc
    obtain ⟨i, _, rfl⟩ := mem_image.mp hx
    rw [hpartner]
    exact hright i
  have hinj : Set.InjOn partner selected := by
    intro x hx y hy he
    obtain ⟨i, _, rfl⟩ := mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := mem_image.mp hy
    rw [hpartner, hpartner] at he
    exact congrArg L (right.injective he)
  have hcard : Fintype.card cut.shore = cut.shoreᶜ.card := by
    simpa only [Fintype.card_coe] using cut.balanced
  obtain ⟨e, he⟩ := Finset.exists_equiv_extend_of_card_eq hcard hinto hinj
  refine ⟨matchingOfEquiv cut.shore e, matchingOfEquiv_crosses _ _, ?_⟩
  intro i
  change bipartiteMate cut.shore e (left i) = right i
  rw [bipartiteMate, dif_pos (hleft i)]
  exact (he (L i) (mem_image_of_mem L (mem_univ i))).trans (hpartner i)

def completeMatching (cut : Bisection C) (left right : I ↪ C)
    (hleft : ∀ i, left i ∈ cut.shore) (hright : ∀ i, right i ∈ cut.shoreᶜ) : Matching C :=
  Classical.choose (exists_matching_extends cut left right hleft hright)

theorem completeMatching_spec (cut : Bisection C) (left right : I ↪ C)
    (hleft : ∀ i, left i ∈ cut.shore) (hright : ∀ i, right i ∈ cut.shoreᶜ) :
    (completeMatching cut left right hleft hright).Crosses cut.shore ∧
      ∀ i, (completeMatching cut left right hleft hright).mate (left i) = right i :=
  Classical.choose_spec (exists_matching_extends cut left right hleft hright)

abbrev Clone (V : Type) (b : ℕ) := V × Fin b

def slotCount {b : ℕ} (S : Finset (Clone V b)) (v : V) : ℕ :=
  Fintype.card {c : S // c.val.1 = v}

theorem list_label_fiber_card {A : Type} (items : List A) (label : A → V) (v : V) :
    Fintype.card {i : Fin items.length // label (items.get i) = v} =
      (items.map (fun x => if label x = v then 1 else 0)).sum := by
  rw [Fintype.card_subtype, card_filter]
  have he : List.ofFn (fun i : Fin items.length => if label (items.get i) = v then 1 else 0) =
      items.map (fun x => if label x = v then 1 else 0) := by
    change List.ofFn ((fun x => if label x = v then 1 else 0) ∘ items.get) = _
    rw [← List.map_ofFn, List.ofFn_get]
  rw [← he, List.sum_ofFn]

def SlotsFit {b : ℕ} (cut : Bisection (Clone V b)) (routes : List (LocatedRoute V)) : Prop :=
  ∀ v, startCount routes v ≤ slotCount cut.shore v ∧
    finishCount routes v ≤ slotCount cut.shoreᶜ v

/-- Every proof field concerns public finite data. Hidden-graph routing and
congestion remain separate theorems about the returned routes. -/
structure ClonePairing {b : ℕ} (cut : Bisection (Clone V b)) (routes : List (LocatedRoute V)) where
  left : Fin routes.length ↪ cut.shore
  right : Fin routes.length ↪ ↥(cut.shoreᶜ)
  matching : Matching (Clone V b)
  crosses : matching.Crosses cut.shore
  paired : ∀ i, matching.mate (left i).val = (right i).val
  source_label : ∀ i, (left i).val.1 = (routes.get i).start
  sink_label : ∀ i, (right i).val.1 = (routes.get i).finish

def buildClonePairing {b : ℕ} (cut : Bisection (Clone V b)) (routes : List (LocatedRoute V))
    (hfit : SlotsFit cut routes) : ClonePairing cut routes := by
  let start := fun i : Fin routes.length => (routes.get i).start
  let finish := fun i : Fin routes.length => (routes.get i).finish
  have hs : ∀ v, Fintype.card {i : Fin routes.length // start i = v} ≤
      Fintype.card {c : cut.shore // c.val.1 = v} := by
    intro v
    have h := (hfit v).1
    change Fintype.card {i : Fin routes.length // LocatedRoute.start (routes.get i) = v} ≤ _
    rw [list_label_fiber_card routes LocatedRoute.start v]
    simpa only [startCount, slotCount, eq_comm] using h
  have ht : ∀ v, Fintype.card {i : Fin routes.length // finish i = v} ≤
      Fintype.card {c : ↥(cut.shoreᶜ) // c.val.1 = v} := by
    intro v
    have h := (hfit v).2
    change Fintype.card {i : Fin routes.length // LocatedRoute.finish (routes.get i) = v} ≤ _
    rw [list_label_fiber_card routes LocatedRoute.finish v]
    simpa only [finishCount, slotCount, eq_comm] using h
  let left := labelEmbedding start (fun c : cut.shore => c.val.1) hs
  let right := labelEmbedding finish (fun c : ↥(cut.shoreᶜ) => c.val.1) ht
  let L := left.trans (Function.Embedding.subtype (fun c => c ∈ cut.shore))
  let R := right.trans (Function.Embedding.subtype (fun c => c ∈ cut.shoreᶜ))
  let hL : ∀ i, L i ∈ cut.shore := fun i => (left i).property
  let hR : ∀ i, R i ∈ cut.shoreᶜ := fun i => (right i).property
  let M := completeMatching cut L R hL hR
  have hM := completeMatching_spec cut L R hL hR
  exact ⟨left, right, M, hM.1, hM.2,
    labelEmbedding_label start _ hs, labelEmbedding_label finish _ ht⟩

/-- A checked public guard makes malformed transcripts harmless. Honest
executions satisfy it by `located_terminal_bounds`. -/
def assignClones {b : ℕ} (cut : Bisection (Clone V b)) (routes : List (LocatedRoute V)) :
    Option (ClonePairing cut routes) :=
  if h : SlotsFit cut routes then some (buildClonePairing cut routes h) else none

theorem assignClones_success {b : ℕ} (cut : Bisection (Clone V b)) (routes : List (LocatedRoute V))
    (h : SlotsFit cut routes) : assignClones cut routes = some (buildClonePairing cut routes h) := by
  simp only [assignClones, dif_pos h]

def ClonePairing.fakeLeft {b : ℕ} {cut : Bisection (Clone V b)} {routes : List (LocatedRoute V)}
    (pairs : ClonePairing cut routes) : Finset (Clone V b) :=
  cut.shore \ univ.image (fun i => (pairs.left i).val)

theorem ClonePairing.fakeLeft_card {b : ℕ} {cut : Bisection (Clone V b)}
    {routes : List (LocatedRoute V)} (pairs : ClonePairing cut routes) :
    pairs.fakeLeft.card = cut.shore.card - routes.length := by
  have hsub : univ.image (fun i => (pairs.left i).val) ⊆ cut.shore := by
    intro c hc
    obtain ⟨i, _, rfl⟩ := mem_image.mp hc
    exact (pairs.left i).property
  have hinj : Function.Injective (fun i => (pairs.left i).val) := by
    intro i j h
    exact pairs.left.injective (Subtype.ext h)
  rw [ClonePairing.fakeLeft, card_sdiff_of_subset hsub, card_image_of_injective _ hinj, card_univ,
    Fintype.card_fin]

/-- Mark both endpoints of every unrouted pair. This public marker is the
input to the separate fake-multigraph construction. -/
def ClonePairing.fakeEndpoints {b : ℕ} {cut : Bisection (Clone V b)}
    {routes : List (LocatedRoute V)} (pairs : ClonePairing cut routes) : Finset (Clone V b) :=
  univ.filter fun c => c ∈ pairs.fakeLeft ∨ pairs.matching.mate c ∈ pairs.fakeLeft

theorem ClonePairing.fakeEndpoints_mate {b : ℕ} {cut : Bisection (Clone V b)}
    {routes : List (LocatedRoute V)} (pairs : ClonePairing cut routes) (c : Clone V b) :
    pairs.matching.mate c ∈ pairs.fakeEndpoints ↔ c ∈ pairs.fakeEndpoints := by
  simp only [ClonePairing.fakeEndpoints, mem_filter, mem_univ, true_and,
    pairs.matching.involutive c, or_comm]

theorem ClonePairing.fakeEndpoints_on_shore {b : ℕ} {cut : Bisection (Clone V b)}
    {routes : List (LocatedRoute V)} (pairs : ClonePairing cut routes)
    {c : Clone V b} (hc : c ∈ cut.shore) :
    c ∈ pairs.fakeEndpoints ↔ c ∈ pairs.fakeLeft := by
  have hm : pairs.matching.mate c ∉ cut.shore := (pairs.crosses c).mp hc
  have hmf : pairs.matching.mate c ∉ pairs.fakeLeft :=
    fun h => hm (mem_sdiff.mp h).1
  simp only [ClonePairing.fakeEndpoints, mem_filter, mem_univ, true_and, hmf, or_false]

theorem ClonePairing.fakeLeft_eq_filter {b : ℕ} {cut : Bisection (Clone V b)}
    {routes : List (LocatedRoute V)} (pairs : ClonePairing cut routes) :
    pairs.fakeLeft = cut.shore.filter (fun c => c ∈ pairs.fakeEndpoints) := by
  ext c
  constructor
  · intro h
    have hc : c ∈ cut.shore := (mem_sdiff.mp h).1
    exact mem_filter.mpr ⟨hc, (pairs.fakeEndpoints_on_shore hc).mpr h⟩
  · intro h
    obtain ⟨hc, hm⟩ := mem_filter.mp h
    exact (pairs.fakeEndpoints_on_shore hc).mp hm

theorem ClonePairing.fakeEndpoints_eq_union {b : ℕ} {cut : Bisection (Clone V b)}
    {routes : List (LocatedRoute V)} (pairs : ClonePairing cut routes) :
    pairs.fakeEndpoints = pairs.fakeLeft ∪ pairs.fakeLeft.image pairs.matching.mate := by
  ext c
  have himage : c ∈ pairs.fakeLeft.image pairs.matching.mate ↔
      pairs.matching.mate c ∈ pairs.fakeLeft := by
    constructor
    · rintro hc
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hc
      simpa only [pairs.matching.involutive x] using hx
    · intro hc
      exact mem_image.mpr ⟨pairs.matching.mate c, hc, pairs.matching.involutive c⟩
  simp only [ClonePairing.fakeEndpoints, mem_filter, mem_univ, true_and, mem_union, himage]

theorem ClonePairing.fakeEndpoints_card {b : ℕ} {cut : Bisection (Clone V b)}
    {routes : List (LocatedRoute V)} (pairs : ClonePairing cut routes) :
    pairs.fakeEndpoints.card = 2 * pairs.fakeLeft.card := by
  have hd : Disjoint pairs.fakeLeft (pairs.fakeLeft.image pairs.matching.mate) := by
    apply disjoint_left.mpr
    intro c hc hm
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hm
    have hxS : x ∈ cut.shore := (mem_sdiff.mp hx).1
    have hcS : pairs.matching.mate x ∈ cut.shore := (mem_sdiff.mp hc).1
    exact ((pairs.crosses x).mp hxS) hcS
  rw [pairs.fakeEndpoints_eq_union, card_union_of_disjoint hd,
    card_image_of_injective _ pairs.matching.mate.injective, two_mul]

theorem ClonePairing.routed_left_notFake {b : ℕ} {cut : Bisection (Clone V b)}
    {routes : List (LocatedRoute V)} (pairs : ClonePairing cut routes) (i : Fin routes.length) :
    (pairs.left i).val ∉ pairs.fakeEndpoints := by
  rw [pairs.fakeEndpoints_on_shore (pairs.left i).property]
  intro h
  exact (mem_sdiff.mp h).2 (mem_image_of_mem _ (mem_univ i))

theorem ClonePairing.real_left_iff {b : ℕ} {cut : Bisection (Clone V b)}
    {routes : List (LocatedRoute V)} (pairs : ClonePairing cut routes)
    {c : Clone V b} (hc : c ∈ cut.shore) :
    c ∉ pairs.fakeEndpoints ↔ ∃ i, (pairs.left i).val = c := by
  rw [pairs.fakeEndpoints_on_shore hc]
  simp only [ClonePairing.fakeLeft, mem_sdiff, hc, true_and, not_not,
    mem_image, mem_univ, true_and]

end
end CutQueryComplexity.DeterministicAPMCExpansion.CutMatching

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.exists_matching_extends
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.assignClones_success
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.ClonePairing.fakeLeft_card
