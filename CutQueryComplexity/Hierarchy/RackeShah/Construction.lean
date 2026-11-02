import CutQueryComplexity.Hierarchy.RackeShah.WeightedMajority
import CutQueryComplexity.Hierarchy.RackeShah.Partition
import CutQueryComplexity.Hierarchy.RackeShah.Refinement
import CutQueryComplexity.Hierarchy.RackeShah.Decomposition

/-! # The recursive construction and the global load bound (Räcke–Shah, M5, part B)

`Certified G n p X` says that `X` has a decomposition `Dec G Q X F` whose total load
`∑_{S ∈ F} Q S` is pointwise at most `loadBound n p |X| = 2 κ K(n) log₂ p + 4 log₂ |X| + 2`
times the capacity on pairs inside `X`, and zero elsewhere.

`certified_or_bottleneck` is the strong induction on `|X|` that drives the construction: a
cluster in context `p` either exhibits a bottleneck (M3) or is certified; and a piece in context
`p` has a refinement (M4) whose final parts are certified, obtained by splitting bottlenecks
(M2) until the pieces accept a partition. In the certified case the initial partition passes
the expansion test with factor `expFactor n p |X|`, every initial part is refined in context
`|X|` with the M4 flow, the transfer lemma (M1) gives the local contract of the final children
with load `2 f G[X] + ∑_C q_C`, and the load sum telescopes:
`2 κ K (log₂ p − log₂ |X|) + 4 (log₂ |X| − log₂ |D|)` at `X` plus `loadBound n |X| |D|` below
`D` is `loadBound n p |X|`.

At the root `univ` in context `2n` no bottleneck exists, since the boundary of `univ` is zero
(`exists_certified_univ`).
-/

namespace CutQueryComplexity
namespace Hierarchy
namespace RackeShah

open WeightedGraph Finset Certificate DetMinCut

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## Sums of load graphs -/

/-- The pointwise sum of load graphs over a finite family. -/
def sumGraph (Ps : Finset (Finset V)) (q : Finset V → WeightedGraph V) : WeightedGraph V where
  w u v := ∑ C ∈ Ps, (q C).w u v
  symm u v := sum_congr rfl fun C _ => (q C).symm u v
  nonneg u v := sum_nonneg fun C _ => (q C).nonneg u v
  diag v := sum_eq_zero fun C _ => (q C).diag v

omit [Fintype V] [DecidableEq V] in
theorem sumGraph_w (Ps : Finset (Finset V)) (q : Finset V → WeightedGraph V) (u v : V) :
    (sumGraph Ps q).w u v = ∑ C ∈ Ps, (q C).w u v := rfl

omit [Fintype V] [DecidableEq V] in
theorem sumGraph_supported {Ps : Finset (Finset V)} {q : Finset V → WeightedGraph V}
    {X : Finset V} (h : ∀ C ∈ Ps, Supported (q C) X) : Supported (sumGraph Ps q) X := by
  intro u v huv
  rw [sumGraph_w]
  exact sum_eq_zero fun C hC => h C hC u v huv

/-- The load bound `2 κ K(n) log₂ p + 4 log₂ m + 2`. -/
noncomputable def loadBound (n p m : ℕ) : ℝ := 2 * kappa * KK n * lg p + 4 * lg m + 2

/-- A certified decomposition of `X` in context `p`. -/
def Certified (G : WeightedGraph V) (n p : ℕ) (X : Finset V) : Prop :=
  ∃ (Q : Finset V → WeightedGraph V) (F : Finset (Finset V)),
    Dec G Q X F ∧
    (∀ u v, u ∈ X → v ∈ X → ∑ S ∈ F, (Q S).w u v ≤ loadBound n p X.card * G.w u v) ∧
    (∀ u v, ¬ (u ∈ X ∧ v ∈ X) → ∑ S ∈ F, (Q S).w u v = 0)

theorem loadBound_nonneg {n p m : ℕ} (hp : 1 ≤ p) (hm : 1 ≤ m) : 0 ≤ loadBound n p m := by
  unfold loadBound
  have := lg_nonneg hp
  have := lg_nonneg hm
  have := kappa_pos
  have : (0 : ℝ) ≤ KK n := Nat.cast_nonneg _
  positivity

/-- Singletons are certified with zero load. -/
theorem certified_singleton (G : WeightedGraph V) (n : ℕ) {p : ℕ} (hp : 1 ≤ p) (v : V) :
    Certified G n p {v} := by
  refine ⟨fun _ => 0, {{v}}, Dec.leaf v, fun u w _ _ => ?_, fun u w _ => ?_⟩
  · simp only [sum_singleton]
    show (0 : ℝ) ≤ _
    rw [card_singleton]
    exact mul_nonneg (loadBound_nonneg hp le_rfl) (G.nonneg u w)
  · simp only [sum_singleton]; rfl

/-! ## Choosing functions from families of existentials -/

theorem choose_mem {α β : Type} [Inhabited β] (s : Finset α) {P : α → β → Prop}
    (h : ∀ a ∈ s, ∃ b, P a b) : ∃ f : α → β, ∀ a ∈ s, P a (f a) := by
  classical
  have h' : ∀ a, ∃ b, a ∈ s → P a b := by
    intro a
    by_cases ha : a ∈ s
    · obtain ⟨b, hb⟩ := h a ha; exact ⟨b, fun _ => hb⟩
    · exact ⟨default, fun h => absurd h ha⟩
  choose f hf using h'
  exact ⟨f, fun a ha => hf a ha⟩

instance : Inhabited (WeightedGraph V) := ⟨0⟩

/-! ## Assembling a certified cluster from a partition -/

/-- **The node step.** A balanced expanding partition whose parts are refined with certified
final parts yields a certified cluster. -/
theorem certified_of_partition (G : WeightedGraph V) (n : ℕ) {p : ℕ} {X : Finset V}
    (h2 : 2 ≤ X.card) (hpX : 2 * X.card ≤ p) (hpn : p ≤ 2 * n) {Ps : Finset (Finset V)}
    (hPs : Balanced X Ps) (hexp : Expands G X Ps (expFactor n p X.card))
    (href : ∀ C ∈ Ps, ∃ Cs, Ref G n X.card C Cs ∧ ∀ D ∈ Cs, Certified G n X.card D) :
    Certified G n p X := by
  classical
  have hX1 : 1 ≤ X.card := by omega
  have hXn : X.card ≤ 2 * n := by omega
  have hp1 : 1 ≤ p := by omega
  -- the refinements of the initial parts
  obtain ⟨CsF, hCsF⟩ := choose_mem Ps href
  set Cs := Ps.biUnion CsF with hCsdef
  have hCsFpart : ∀ C ∈ Ps, IsPart C (CsF C) := fun C hC => (hCsF C hC).1.isPart
  have hCsFsub : ∀ C ∈ Ps, ∀ D ∈ CsF C, D ⊆ C := fun C hC D hD => (hCsFpart C hC).subset hD
  have hCsFne : ∀ C ∈ Ps, ∀ D ∈ CsF C, D.Nonempty := fun C hC D hD => (hCsFpart C hC).nonempty D hD
  -- a final part lies in a unique initial part
  have hinit_unique : ∀ C ∈ Ps, ∀ C' ∈ Ps, ∀ D, D ∈ CsF C → D ⊆ C' → C = C' := by
    intro C hC C' hC' D hD hDC'
    obtain ⟨v, hv⟩ := hCsFne C hC D hD
    exact IsPart.eq_of_mem_of_inter (h := hPs.part) hC hC' (hCsFsub C hC D hD hv) (hDC' hv)
  have hCsFdisj : (Ps : Set (Finset V)).PairwiseDisjoint CsF := by
    intro C hC C' hC' hne
    rw [Function.onFun, disjoint_left]
    intro D hD hD'
    exact hne (hinit_unique C hC C' hC' D hD (hCsFsub C' hC' D hD'))
  -- the final children form a balanced partition
  have hbal : Balanced X Cs := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro D hD
      obtain ⟨C, hC, hDC⟩ := mem_biUnion.mp hD
      exact hCsFne C hC D hDC
    · intro D hD D' hD' hne
      obtain ⟨C, hC, hDC⟩ := mem_biUnion.mp hD
      obtain ⟨C', hC', hDC'⟩ := mem_biUnion.mp hD'
      by_cases hCC : C = C'
      · subst hCC; exact (hCsFpart C hC).disj hDC hDC' hne
      · exact (hPs.part.disj hC hC' hCC).mono (hCsFsub C hC D hDC) (hCsFsub C' hC' D' hDC')
    · ext v
      rw [mem_biUnion]
      constructor
      · rintro ⟨D, hD, hv⟩
        obtain ⟨C, hC, hDC⟩ := mem_biUnion.mp hD
        exact hPs.part.subset hC (hCsFsub C hC D hDC hv)
      · intro hv
        have : v ∈ Ps.biUnion id := hPs.part.union ▸ hv
        obtain ⟨C, hC, hvC⟩ := mem_biUnion.mp this
        simp only [id] at hvC
        rw [← (hCsFpart C hC).union] at hvC
        obtain ⟨D, hD, hvD⟩ := mem_biUnion.mp hvC
        exact ⟨D, mem_biUnion.mpr ⟨C, hC, hD⟩, hvD⟩
    · intro D hD
      obtain ⟨C, hC, hDC⟩ := mem_biUnion.mp hD
      have := card_le_card (hCsFsub C hC D hDC)
      have := hPs.half C hC
      omega
  -- the certified decompositions of the final children
  have hcert : ∀ D ∈ Cs, ∃ QF : Finset V → WeightedGraph V, ∃ FF : Finset (Finset V),
      Dec G QF D FF ∧
      (∀ u v, u ∈ D → v ∈ D → ∑ S ∈ FF, (QF S).w u v ≤ loadBound n X.card D.card * G.w u v) ∧
      (∀ u v, ¬ (u ∈ D ∧ v ∈ D) → ∑ S ∈ FF, (QF S).w u v = 0) := by
    intro D hD
    obtain ⟨C, hC, hDC⟩ := mem_biUnion.mp hD
    exact (hCsF C hC).2 D hDC
  obtain ⟨QF, hQF⟩ := choose_mem (β := Finset V → WeightedGraph V) Cs hcert
  obtain ⟨FF, hFF⟩ := choose_mem Cs hQF
  have hDecD : ∀ D ∈ Cs, Dec G (QF D) D (FF D) := fun D hD => (hFF D hD).1
  have hloadD : ∀ D ∈ Cs, ∀ u v, u ∈ D → v ∈ D →
      ∑ S ∈ FF D, (QF D S).w u v ≤ loadBound n X.card D.card * G.w u v :=
    fun D hD => (hFF D hD).2.1
  have houtD : ∀ D ∈ Cs, ∀ u v, ¬ (u ∈ D ∧ v ∈ D) → ∑ S ∈ FF D, (QF D S).w u v = 0 :=
    fun D hD => (hFF D hD).2.2
  -- the refinement flows of the initial parts (index 1)
  have hflow : ∀ C ∈ Ps, RefFlow G C (CsF C) (Bprod n 1) := by
    intro C hC
    exact ref_flow G n (hCsF C hC).1 hXn 1 le_rfl (by simpa using hPs.half C hC)
  obtain ⟨qf, hqf⟩ := choose_mem (β := WeightedGraph V) Ps fun C hC =>
    (hflow C hC : ∃ q : WeightedGraph V, ∃ F : V → V → ℝ, ∃ r : V → ℝ, _)
  obtain ⟨Ff, hFf⟩ := choose_mem (β := V → V → ℝ) Ps hqf
  obtain ⟨rf, hrf⟩ := choose_mem (β := V → ℝ) Ps hFf
  have hqsupp : ∀ C ∈ Ps, Supported (qf C) C := fun C hC => (hrf C hC).1
  have hFfeas : ∀ C ∈ Ps, Feasible (qf C) (Ff C) := fun C hC => (hrf C hC).2.1
  have hFdiv : ∀ C ∈ Ps, ∀ v ∈ C, netOut (Ff C) v = pd G (CsF C) v - rf C v :=
    fun C hC => (hrf C hC).2.2.1
  have hrbound : ∀ C ∈ Ps, ∀ v ∈ C, 0 ≤ rf C v ∧ rf C v ≤ Bprod n 1 * bd G C v :=
    fun C hC => (hrf C hC).2.2.2.1
  have hsame : ∀ C ∈ Ps, ∀ u v D, D ∈ CsF C → u ∈ D → v ∈ D →
      (qf C).w u v ≤ 4 * (lg C.card - lg D.card) * G.w u v :=
    fun C hC => (hrf C hC).2.2.2.2.1
  have hdiff : ∀ C ∈ Ps, ∀ u v, u ∈ C → v ∈ C → (∀ D ∈ CsF C, ¬ (u ∈ D ∧ v ∈ D)) →
      (qf C).w u v ≤ (4 * lg C.card + 2) * G.w u v :=
    fun C hC => (hrf C hC).2.2.2.2.2
  have hB1 : Bprod n 1 ≤ 2 := Bprod_le_two n le_rfl
  -- the aggregated flow, receiving function and load of `X`
  set f := expFactor n p X.card with hfdef
  have hf0 : 0 ≤ f := expFactor_nonneg hX1 (by omega)
  set qtot := sumGraph Ps qf with hqtotdef
  set Ftot : V → V → ℝ := fun u v => ∑ C ∈ Ps, Ff C u v with hFtotdef
  set rtot : V → ℝ := fun v => ∑ C ∈ Ps, if v ∈ C then rf C v else 0 with hrtotdef
  have hqtot : Supported qtot X := sumGraph_supported fun C hC =>
    (hqsupp C hC).mono (hPs.part.subset hC)
  have hFtot : Feasible qtot Ftot := by
    refine ⟨fun u v => ?_, fun u v => ?_⟩
    · simp only [hFtotdef]
      rw [← sum_neg_distrib]
      exact sum_congr rfl fun C hC => (hFfeas C hC).1 u v
    · simp only [hFtotdef, hqtotdef, sumGraph_w]
      exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun C hC => (hFfeas C hC).2 u v)
  -- the unique initial part of a vertex of `X`
  have hpart_of_mem : ∀ v ∈ X, ∃ C ∈ Ps, v ∈ C := by
    intro v hv
    have : v ∈ Ps.biUnion id := hPs.part.union ▸ hv
    obtain ⟨C, hC, hvC⟩ := mem_biUnion.mp this
    exact ⟨C, hC, hvC⟩
  have hdiv : ∀ v ∈ X, netOut Ftot v = pd G Cs v - rtot v := by
    intro v hv
    obtain ⟨C₀, hC₀, hvC₀⟩ := hpart_of_mem v hv
    have hnet : netOut Ftot v = ∑ C ∈ Ps, netOut (Ff C) v := by
      simp only [netOut, hFtotdef]; rw [sum_comm]
    have hother : ∀ C ∈ Ps, C ≠ C₀ → v ∉ C := fun C hC hne hvC =>
      hne (IsPart.eq_of_mem_of_inter (h := hPs.part) hC hC₀ hvC hvC₀)
    rw [hnet, sum_eq_single C₀ (fun C hC hne => (hqsupp C hC).netOut_eq_zero (hFfeas C hC)
      (hother C hC hne)) (fun h => absurd hC₀ h), hFdiv C₀ hC₀ v hvC₀]
    have hpd : pd G Cs v = pd G (CsF C₀) v := by
      unfold pd
      rw [hCsdef, sum_biUnion hCsFdisj]
      rw [sum_eq_single C₀ (fun C hC hne => sum_eq_zero fun D hD =>
        bd_of_notMem G fun hvD => hother C hC hne (hCsFsub C hC D hD hvD))
        (fun h => absurd hC₀ h)]
    have hr : rtot v = rf C₀ v := by
      simp only [hrtotdef]
      rw [sum_eq_single C₀ (fun C hC hne => by rw [ite_eq_right (hother C hC hne)])
        (fun h => absurd hC₀ h), ite_eq_left hvC₀]
    rw [hpd, hr]
  have hr2 : ∀ v ∈ X, rtot v ≤ 2 * pd G Ps v := by
    intro v hv
    obtain ⟨C₀, hC₀, hvC₀⟩ := hpart_of_mem v hv
    have hother : ∀ C ∈ Ps, C ≠ C₀ → v ∉ C := fun C hC hne hvC =>
      hne (IsPart.eq_of_mem_of_inter (h := hPs.part) hC hC₀ hvC hvC₀)
    have hr : rtot v = rf C₀ v := by
      simp only [hrtotdef]
      rw [sum_eq_single C₀ (fun C hC hne => by rw [ite_eq_right (hother C hC hne)])
        (fun h => absurd hC₀ h), ite_eq_left hvC₀]
    rw [hr, pd_eq_of_mem G hPs.part hC₀ hvC₀]
    have := (hrbound C₀ hC₀ v hvC₀).2
    have := bd_nonneg G C₀ v
    nlinarith
  -- the local contract of `X` with the final children
  set QX := ((G.induce X).scale (2 * f) (mul_nonneg (by norm_num) hf0)).add qtot with hQXdef
  have hloc : Local G X Cs QX :=
    local_of_flow G X Ps Cs hf0 (by norm_num) qtot hqtot Ftot hFtot rtot hdiv hr2 hexp
  -- the glued load function and the family
  set Q' : Finset V → WeightedGraph V := fun S =>
    if S = X then QX else sumGraph Cs fun D => if S ∈ FF D then QF D S else 0 with hQ'def
  have hQ'X : Q' X = QX := by simp [hQ'def]
  have hmem_unique : ∀ D ∈ Cs, ∀ D' ∈ Cs, ∀ S, S ∈ FF D → S ∈ FF D' → D = D' := by
    intro D hD D' hD' S hS hS'
    obtain ⟨v, hv⟩ := (hDecD D hD).nonempty_mem S hS
    exact IsPart.eq_of_mem_of_inter (h := hbal.part) hD hD' ((hDecD D hD).subset S hS hv)
      ((hDecD D' hD').subset S hS' hv)
  have hQ'D : ∀ D ∈ Cs, ∀ S ∈ FF D, Q' S = QF D S := by
    intro D hD S hS
    have hSX : S ≠ X := by
      intro h
      have := (hDecD D hD).subset S hS
      rw [h] at this
      exact (Finset.ssubset_iff_subset_ne.mp (Dec.ssubset_of_balanced h2 hbal hD)).2
        (subset_antisymm (hbal.part.subset hD) this)
    simp only [hQ'def, hSX, ite_false]
    ext u v
    rw [sumGraph_w]
    rw [sum_eq_single D (fun D' hD' hne => by
      have : S ∉ FF D' := fun h => hne (hmem_unique D' hD' D hD S h hS)
      simp [this]) (fun h => absurd hD h)]
    simp [hS]
  have hsub : ∀ D ∈ Cs, Dec G Q' D (FF D) :=
    fun D hD => (hDecD D hD).congr fun S hS => hQ'D D hD S hS
  have hDec : Dec G Q' X (insert X (Cs.biUnion FF)) :=
    Dec.node X Cs FF h2 hbal hsub (hQ'X ▸ hloc)
  refine ⟨Q', insert X (Cs.biUnion FF), hDec, ?_, ?_⟩
  · -- the load bound inside `X`
    intro u v hu hv
    have hw := G.nonneg u v
    rw [sum_insert (Dec.top_notMem_biUnion h2 hbal hsub), sum_biUnion
      (Dec.pairwiseDisjoint_families hbal hsub), hQ'X]
    have hsubsum : ∀ D ∈ Cs, ∑ S ∈ FF D, (Q' S).w u v = ∑ S ∈ FF D, (QF D S).w u v :=
      fun D hD => sum_congr rfl fun S hS => by rw [hQ'D D hD S hS]
    rw [sum_congr rfl hsubsum]
    rw [hQXdef, add_w, scale_w, induce_w, ite_eq_left ⟨hu, hv⟩, sumGraph_w]
    have hfeq : f = kappa * KK n * (lg p - lg X.card) := expFactor_eq_sub hX1 hp1
    have hlgX := lg_nonneg hX1
    have hκK : 0 ≤ kappa * KK n := mul_nonneg kappa_pos.le (Nat.cast_nonneg _)
    by_cases hD : ∃ D ∈ Cs, u ∈ D ∧ v ∈ D
    · obtain ⟨D₀, hD₀, huD, hvD⟩ := hD
      obtain ⟨C₀, hC₀, hD₀C⟩ := mem_biUnion.mp hD₀
      have hD1 : 1 ≤ D₀.card := (hbal.part.nonempty D₀ hD₀).card_pos
      have hsum1 : ∑ D ∈ Cs, ∑ S ∈ FF D, (QF D S).w u v = ∑ S ∈ FF D₀, (QF D₀ S).w u v := by
        rw [sum_eq_single D₀ (fun D hD hne => houtD D hD u v fun h =>
          hne (IsPart.eq_of_mem_of_inter (h := hbal.part) hD hD₀ h.1 huD)) (fun h => absurd hD₀ h)]
      have hsum2 : ∑ C ∈ Ps, (qf C).w u v = (qf C₀).w u v := by
        rw [sum_eq_single C₀ (fun C hC hne => (hqsupp C hC).w_eq_zero fun h =>
          hne (IsPart.eq_of_mem_of_inter (h := hPs.part) hC hC₀ h.1 (hCsFsub C₀ hC₀ D₀ hD₀C huD)))
          (fun h => absurd hC₀ h)]
      rw [hsum1, hsum2]
      have h1 := hloadD D₀ hD₀ u v huD hvD
      have h2 := hsame C₀ hC₀ u v D₀ hD₀C huD hvD
      have h3 : lg C₀.card ≤ lg X.card := lg_mono (hD1.trans (card_le_card (hCsFsub C₀ hC₀ D₀ hD₀C)))
        (card_le_card (hPs.part.subset hC₀))
      unfold loadBound at h1 ⊢
      rw [hfeq]
      have := mul_nonneg (mul_nonneg hκK hlgX) hw
      nlinarith
    · push Not at hD
      have hsum1 : ∑ D ∈ Cs, ∑ S ∈ FF D, (QF D S).w u v = 0 :=
        sum_eq_zero fun D hD' => houtD D hD' u v fun h => hD D hD' h.1 h.2
      rw [hsum1, _root_.add_zero]
      have hq : ∑ C ∈ Ps, (qf C).w u v ≤ (4 * lg X.card + 2) * G.w u v := by
        by_cases hC : ∃ C ∈ Ps, u ∈ C ∧ v ∈ C
        · obtain ⟨C₀, hC₀, huC, hvC⟩ := hC
          rw [sum_eq_single C₀ (fun C hC hne => (hqsupp C hC).w_eq_zero fun h =>
            hne (IsPart.eq_of_mem_of_inter (h := hPs.part) hC hC₀ h.1 huC)) (fun h => absurd hC₀ h)]
          have := hdiff C₀ hC₀ u v huC hvC fun D hDC h =>
            hD D (mem_biUnion.mpr ⟨C₀, hC₀, hDC⟩) h.1 h.2
          have h3 : lg C₀.card ≤ lg X.card :=
            lg_mono ((hPs.part.nonempty C₀ hC₀).card_pos) (card_le_card (hPs.part.subset hC₀))
          nlinarith
        · push Not at hC
          rw [sum_eq_zero fun C hC' => (hqsupp C hC').w_eq_zero fun h => hC C hC' h.1 h.2]
          positivity
      unfold loadBound
      rw [hfeq]
      have := mul_nonneg (mul_nonneg hκK hlgX) hw
      nlinarith
  · -- zero load outside `X`
    intro u v huv
    rw [sum_insert (Dec.top_notMem_biUnion h2 hbal hsub), sum_biUnion
      (Dec.pairwiseDisjoint_families hbal hsub), hQ'X]
    have hsubsum : ∀ D ∈ Cs, ∑ S ∈ FF D, (Q' S).w u v = ∑ S ∈ FF D, (QF D S).w u v :=
      fun D hD => sum_congr rfl fun S hS => by rw [hQ'D D hD S hS]
    rw [sum_congr rfl hsubsum]
    rw [hloc.supp.w_eq_zero huv, sum_eq_zero fun D hD => houtD D hD u v fun h =>
      huv ⟨hbal.part.subset hD h.1, hbal.part.subset hD h.2⟩]
    simp

/-! ## The strong induction -/

/-- **Certified or bottleneck**, and refinements with certified final parts, for every cluster. -/
theorem certified_or_bottleneck (G : WeightedGraph V) (n : ℕ) :
    ∀ m, ∀ X : Finset V, X.card = m → X.Nonempty →
      (∀ p, 2 * X.card ≤ p → p ≤ 2 * n →
        (∃ U, Bottleneck G (expFactor n p X.card) X U) ∨ Certified G n p X) ∧
      (∀ p, 2 * X.card ≤ p → p ≤ 2 * n →
        ∃ Cs, Ref G n p X Cs ∧ ∀ D ∈ Cs, Certified G n p D) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro X hXm hX0
    have hX1 : 1 ≤ X.card := hX0.card_pos
    -- part one: certified or bottleneck
    have hP : ∀ p, 2 * X.card ≤ p → p ≤ 2 * n →
        (∃ U, Bottleneck G (expFactor n p X.card) X U) ∨ Certified G n p X := by
      intro p hpX hpn
      rcases Nat.lt_or_ge X.card 2 with hlt | h2
      · obtain ⟨v, rfl⟩ := card_eq_one.mp (show X.card = 1 by omega)
        rw [card_singleton] at hpX
        exact Or.inr (certified_singleton G n (p := p) (le_trans (by norm_num : 1 ≤ 2 * 1) hpX) v)
      · rcases exists_balanced_or_bottleneck G h2 (four_le_expFactor hX1 hpX) with
          ⟨Ps, hPs, hexp⟩ | ⟨U, hU⟩
        · right
          refine certified_of_partition G n h2 hpX hpn hPs hexp fun C hC => ?_
          have hC0 := hPs.part.nonempty C hC
          have hClt : C.card < m := by have := hPs.half C hC; omega
          exact (ih C.card hClt C rfl hC0).2 X.card (hPs.half C hC) (by omega)
        · exact Or.inl ⟨U, hU⟩
    refine ⟨hP, fun p hpX hpn => ?_⟩
    -- part two: refine until certified
    rcases hP p hpX hpn with ⟨U, hU⟩ | hcert
    · obtain ⟨W, ρ, -, hcert⟩ := exists_splitCert (expFactor_nonneg hX1 (by omega)) hU
      have hWX := hcert.subset
      have hW0 := hcert.nonempty
      have hhalf := hcert.half
      have hWlt : W.card < m := by have := hW0.card_pos; omega
      have hY0 : (X \ W).Nonempty := by
        rw [← card_pos, card_sdiff_of_subset hWX]
        have := hW0.card_pos
        omega
      have hYlt : (X \ W).card < m := by
        rw [card_sdiff_of_subset hWX]; have := hW0.card_pos; omega
      obtain ⟨CsW, hRW, hCW⟩ := (ih W.card hWlt W rfl hW0).2 p (by omega) hpn
      obtain ⟨CsY, hRY, hCY⟩ := (ih (X \ W).card hYlt (X \ W) rfl hY0).2 p
        (by rw [card_sdiff_of_subset hWX]; omega) hpn
      refine ⟨CsW ∪ CsY, Ref.split X W ρ CsW CsY hcert hRW hRY, fun D hD => ?_⟩
      rcases mem_union.mp hD with hD | hD
      · exact hCW D hD
      · exact hCY D hD
    · exact ⟨{X}, Ref.final X hX0, fun D hD => by rw [mem_singleton.mp hD]; exact hcert⟩

/-- **The root is certified.** No bottleneck of `univ` exists, since its boundary is zero. -/
theorem exists_certified_univ [Nonempty V] (G : WeightedGraph V) :
    Certified G (Fintype.card V) (2 * Fintype.card V) univ := by
  have h := (certified_or_bottleneck G (Fintype.card V) (Fintype.card V) univ card_univ
    univ_nonempty).1 (2 * Fintype.card V) (by rw [card_univ]) le_rfl
  rcases h with ⟨U, hU⟩ | hcert
  · exfalso
    have := hU.pos
    have hz : ∑ v ∈ U, bd G univ v = 0 :=
      sum_eq_zero fun v _ => by rw [bd_of_mem G (mem_univ v), compl_univ, cross_empty_right]
    rw [hz] at this
    exact lt_irrefl _ this
  · exact hcert

end RackeShah
end Hierarchy
end CutQueryComplexity
