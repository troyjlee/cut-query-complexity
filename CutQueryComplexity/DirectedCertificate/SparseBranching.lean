import CutQueryComplexity.Graph.ArborescencePacking
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Sparse optimal arborescence packings (W3)

Source: Lemma 9 of paper P3 (`papers/P3/directed-cut-certificates.pdf`).

A *feasible root-cut vector* for `(G, r, lam)` is `y : V → V → ℝ` with `0 ≤ y ≤ G.c` and
`lam ≤ y(δ⁺(S))` for every nonempty `S ∌ r` (arcs `u → v`, `u ∈ S`, `v ∉ S`; this is the
in-arborescence orientation toward `r` of `ArborescencePacking`).

* `isLeast_total` : the minimum total of a feasible root-cut vector is `lam * (|V| - 1)`.
* `eq_load_of_total_eq` : every minimum-total feasible vector is the load of a packing of value
  `lam`.
* `exists_sparse_min_feasible` / `exists_sparse_inArb_packing` : some minimum-total feasible
  vector (an extreme point of the minimum-total face) has at most `2 (|V| - 1)` free arcs
  `0 < y u v < G.c u v`.
-/

namespace CutQueryComplexity.DirectedCertificate

open Finset Filter Topology

section Laminar

variable {V : Type*} [DecidableEq V]

/-! ## Laminar families -/

/-- `A` and `B` cross: they meet and neither contains the other. -/
def Crosses (A B : Finset V) : Prop := (A ∩ B).Nonempty ∧ ¬ A ⊆ B ∧ ¬ B ⊆ A

/-- No two members cross. -/
def IsLaminar (L : Finset (Finset V)) : Prop := ∀ A ∈ L, ∀ B ∈ L, ¬ Crosses A B

theorem Crosses.symm {A B : Finset V} (h : Crosses A B) : Crosses B A :=
  ⟨by rw [inter_comm]; exact h.1, h.2.2, h.2.1⟩

theorem not_crosses_self (A : Finset V) : ¬ Crosses A A := fun h => h.2.1 subset_rfl

theorem Crosses.of_erase {A B : Finset V} (x : V) (h : Crosses (A.erase x) (B.erase x)) :
    Crosses A B := by
  obtain ⟨⟨z, hz⟩, h1, h2⟩ := h
  refine ⟨⟨z, ?_⟩, fun hAB => h1 fun y hy => ?_, fun hBA => h2 fun y hy => ?_⟩
  · simp only [mem_inter, mem_erase] at hz ⊢; exact ⟨hz.1.2, hz.2.2⟩
  · rw [mem_erase] at hy ⊢; exact ⟨hy.1, hAB hy.2⟩
  · rw [mem_erase] at hy ⊢; exact ⟨hy.1, hBA hy.2⟩

/-- In a laminar family, at most one member `C ∋ x` has `C.erase x` also a member. -/
theorem laminar_collision_le {L : Finset (Finset V)} (hL : IsLaminar L)
    (hne : ∀ B ∈ L, B.Nonempty) {x : V} {C₁ C₂ : Finset V} (h₁ : C₁ ∈ L)
    (hx₁ : x ∈ C₁) (hb₁ : C₁.erase x ∈ L) (hb₂ : C₂.erase x ∈ L) (hsub : C₁ ⊆ C₂) :
    C₂ ⊆ C₁ := by
  by_contra hns
  obtain ⟨z, hz⟩ := hne _ hb₁
  refine hL _ hb₂ _ h₁ ⟨⟨z, ?_⟩, fun h => hns ?_, fun h => ?_⟩
  · rw [mem_inter, mem_erase] at *
    exact ⟨⟨hz.1, hsub hz.2⟩, hz.2⟩
  · intro y hy
    by_cases hyx : y = x
    · exact hyx ▸ hx₁
    · exact h (mem_erase.2 ⟨hyx, hy⟩)
  · exact (mem_erase.1 (h hx₁)).1 rfl

/-- **Laminar bound.** A laminar family of nonempty subsets of `U` has at most `2 |U|`
members. -/
theorem laminar_card_le (U : Finset V) :
    ∀ L : Finset (Finset V), IsLaminar L → (∀ B ∈ L, B.Nonempty ∧ B ⊆ U) →
      L.card ≤ 2 * U.card := by
  induction U using Finset.induction_on with
  | empty =>
    intro L _ hL
    have : L = ∅ := by
      refine eq_empty_of_forall_notMem fun B hB => ?_
      obtain ⟨z, hz⟩ := (hL B hB).1
      exact notMem_empty z ((hL B hB).2 hz)
    simp [this]
  | @insert x U hxU ih =>
    intro L hlam hL
    classical
    let L' : Finset (Finset V) := (L.image fun B => B.erase x).filter Finset.Nonempty
    have hL' : ∀ B ∈ L', B.Nonempty ∧ B ⊆ U := by
      intro B hB
      obtain ⟨hB, hBne⟩ := mem_filter.1 hB
      obtain ⟨C, hC, rfl⟩ := mem_image.1 hB
      refine ⟨hBne, fun y hy => ?_⟩
      obtain ⟨hyx, hyC⟩ := mem_erase.1 hy
      exact (mem_insert.1 ((hL C hC).2 hyC)).resolve_left hyx
    have hlam' : IsLaminar L' := by
      intro A hA B hB hcr
      obtain ⟨C, hC, rfl⟩ := mem_image.1 (mem_filter.1 hA).1
      obtain ⟨D, hD, rfl⟩ := mem_image.1 (mem_filter.1 hB).1
      exact hlam C hC D hD (hcr.of_erase x)
    have hIH := ih L' hlam' hL'
    let bad1 := L.filter fun C => C.erase x = ∅ ∧ x ∈ C
    let bad2 := L.filter fun C => x ∈ C ∧ C.erase x ∈ L
    have hb1 : bad1.card ≤ 1 := by
      refine card_le_one.2 fun C hC D hD => ?_
      obtain ⟨-, hCe, hCx⟩ := mem_filter.1 hC
      obtain ⟨-, hDe, hDx⟩ := mem_filter.1 hD
      rw [← insert_erase hCx, ← insert_erase hDx, hCe, hDe]
    have hne : ∀ B ∈ L, B.Nonempty := fun B hB => (hL B hB).1
    have hb2 : bad2.card ≤ 1 := by
      refine card_le_one.2 fun C hC D hD => ?_
      obtain ⟨hCL, hCx, hCe⟩ := mem_filter.1 hC
      obtain ⟨hDL, hDx, hDe⟩ := mem_filter.1 hD
      by_cases hCD : C ⊆ D
      · exact le_antisymm hCD (laminar_collision_le hlam hne hCL hCx hCe hDe hCD)
      · have hDC : D ⊆ C := by
          by_contra hDC
          exact hlam C hCL D hDL ⟨⟨x, mem_inter.2 ⟨hCx, hDx⟩⟩, hCD, hDC⟩
        exact (le_antisymm hDC (laminar_collision_le hlam hne hDL hDx hDe hCe hDC)).symm
    have hgood : (L \ (bad1 ∪ bad2)).card ≤ L'.card := by
      refine card_le_card_of_injOn (fun B => B.erase x) ?_ ?_
      · intro C hC
        obtain ⟨hCL, hCb⟩ := mem_sdiff.1 hC
        refine mem_filter.2 ⟨mem_image.2 ⟨C, hCL, rfl⟩, ?_⟩
        by_cases hCx : x ∈ C
        · refine nonempty_iff_ne_empty.2 fun he => hCb ?_
          exact mem_union_left _ (mem_filter.2 ⟨hCL, he, hCx⟩)
        · show (C.erase x).Nonempty
          rw [erase_eq_of_notMem hCx]; exact hne C hCL
      · intro C hC D hD hCD
        simp only at hCD
        obtain ⟨hCL, hCb⟩ := mem_sdiff.1 (mem_coe.1 hC)
        obtain ⟨hDL, hDb⟩ := mem_sdiff.1 (mem_coe.1 hD)
        by_cases hCx : x ∈ C <;> by_cases hDx : x ∈ D
        · rw [← insert_erase hCx, ← insert_erase hDx, hCD]
        · exfalso; refine hCb (mem_union_right _ (mem_filter.2 ⟨hCL, hCx, ?_⟩))
          rw [hCD, erase_eq_of_notMem hDx]; exact hDL
        · exfalso; refine hDb (mem_union_right _ (mem_filter.2 ⟨hDL, hDx, ?_⟩))
          rw [← hCD, erase_eq_of_notMem hCx]; exact hCL
        · rwa [erase_eq_of_notMem hCx, erase_eq_of_notMem hDx] at hCD
    have hsplit := card_le_card_sdiff_add_card (s := L) (t := bad1 ∪ bad2)
    have hbu := card_union_le bad1 bad2
    rw [card_insert_of_notMem hxU]
    omega

end Laminar

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Root-cut vectors -/

/-- Outgoing cut value `Σ_{u ∈ S, v ∉ S} y u v` of a raw arc vector. -/
def cutVal (y : V → V → ℝ) (S : Finset V) : ℝ := ∑ u ∈ S, ∑ v ∈ Sᶜ, y u v

/-- Total mass `Σ_{u,v} y u v`. -/
def total (y : V → V → ℝ) : ℝ := ∑ u, ∑ v, y u v

/-- Feasible root-cut vector for `(G, r, lam)`. -/
structure RootCutFeasible (G : WeightedDiGraph V) (r : V) (lam : ℝ) (y : V → V → ℝ) : Prop where
  nonneg : ∀ u v, 0 ≤ y u v
  le_cap : ∀ u v, y u v ≤ G.c u v
  cut : ∀ S : Finset V, S.Nonempty → r ∉ S → lam ≤ cutVal y S

/-- Free (partial) arcs: `0 < y u v < G.c u v`. -/
noncomputable def freeArcs (G : WeightedDiGraph V) (y : V → V → ℝ) : Finset (V × V) := by
  classical exact univ.filter fun e => 0 < y e.1 e.2 ∧ y e.1 e.2 < G.c e.1 e.2

omit [DecidableEq V] in
theorem mem_freeArcs {G : WeightedDiGraph V} {y : V → V → ℝ} {e : V × V} :
    e ∈ freeArcs G y ↔ 0 < y e.1 e.2 ∧ y e.1 e.2 < G.c e.1 e.2 := by
  unfold freeArcs; simp

namespace RootCutFeasible
variable {G : WeightedDiGraph V} {r : V} {lam : ℝ} {y : V → V → ℝ}

theorem diag (hy : RootCutFeasible G r lam y) (v : V) : y v v = 0 :=
  le_antisymm (G.diag v ▸ hy.le_cap v v) (hy.nonneg v v)

/-- `y` as a weighted digraph; its outgoing cut is `cutVal y`. -/
def toGraph (hy : RootCutFeasible G r lam y) : WeightedDiGraph V :=
  ⟨y, hy.nonneg, hy.diag⟩

theorem toGraph_out (hy : RootCutFeasible G r lam y) (S : Finset V) :
    hy.toGraph.out S = cutVal y S := rfl

/-- Lower bound from the singleton constraints `S = {v}`, `v ≠ r`. -/
theorem total_ge (hy : RootCutFeasible G r lam y) :
    lam * ((Fintype.card V : ℝ) - 1) ≤ total y := by
  have hn : ((univ.erase r).card : ℝ) = (Fintype.card V : ℝ) - 1 := by
    rw [card_erase_of_mem (mem_univ r), card_univ,
      Nat.cast_sub (Fintype.card_pos_iff.2 ⟨r⟩)]
    simp
  calc lam * ((Fintype.card V : ℝ) - 1) = ∑ _v ∈ univ.erase r, lam := by
        rw [sum_const, nsmul_eq_mul, hn, mul_comm]
    _ ≤ ∑ v ∈ univ.erase r, cutVal y {v} := by
        refine sum_le_sum fun v hv => hy.cut {v} (singleton_nonempty v) ?_
        simpa [eq_comm] using ne_of_mem_erase hv
    _ ≤ ∑ v ∈ univ.erase r, ∑ w, y v w := by
        refine sum_le_sum fun v _ => ?_
        simp only [cutVal, sum_singleton]
        exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun w _ _ => hy.nonneg v w
    _ ≤ total y :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun v _ _ =>
          sum_nonneg fun w _ => hy.nonneg v w

end RootCutFeasible

/-! ## Loads of packings -/

/-- An in-arborescence has exactly `|V| - 1` arcs. -/
theorem IsInArb.card_arcs {r : V} {p : V → Option V} (hp : IsInArb r p) :
    ∑ u, ∑ v, (if p u = some v then (1 : ℝ) else 0) = (Fintype.card V : ℝ) - 1 := by
  classical
  have h1 : ∀ u, ∑ v, (if p u = some v then (1 : ℝ) else 0) = if u = r then 0 else 1 := by
    intro u
    cases h : p u with
    | none =>
      have : u = r := by by_contra hu; exact hp.nonroot u hu h
      simp [this]
    | some w =>
      have : u ≠ r := by rintro rfl; rw [hp.root] at h; simp at h
      simp [this]
  rw [sum_congr rfl fun u _ => h1 u, sum_ite, sum_const_zero, zero_add, sum_const,
    nsmul_eq_mul, mul_one, filter_ne' univ r, card_erase_of_mem (mem_univ r), card_univ,
    Nat.cast_sub (Fintype.card_pos_iff.2 ⟨r⟩)]
  simp

theorem total_load {r : V} (a : InArb r → ℝ) :
    total (load a) = (∑ T, a T) * ((Fintype.card V : ℝ) - 1) := by
  unfold total load
  calc ∑ u, ∑ v, ∑ T : InArb r, a T * (if T.1 u = some v then (1 : ℝ) else 0)
      = ∑ T : InArb r, a T * ∑ u, ∑ v, (if T.1 u = some v then (1 : ℝ) else 0) := by
        simp only [mul_sum]
        exact (sum_congr rfl fun u _ => sum_comm).trans sum_comm
    _ = _ := by
        rw [sum_mul]
        exact sum_congr rfl fun T _ => by rw [(mem_inArbs.1 T.2).card_arcs]

/-- The load of a packing of value `lam` under `G` is a feasible root-cut vector. -/
theorem load_feasible (G : WeightedDiGraph V) (r : V) (lam : ℝ) (a : InArb r → ℝ)
    (ha : ∀ T, 0 ≤ a T) (hsum : ∑ T, a T = lam) (hload : ∀ u v, load a u v ≤ G.c u v) :
    RootCutFeasible G r lam (load a) := by
  have hnn : ∀ u v, 0 ≤ load a u v := fun u v =>
    sum_nonneg fun T _ => mul_nonneg (ha T) (by split_ifs <;> norm_num)
  have hdiag : ∀ v, load a v v = 0 := fun v =>
    sum_eq_zero fun T _ => by simp [(mem_inArbs.1 T.2).irrefl v]
  let H : WeightedDiGraph V := ⟨load a, hnn, hdiag⟩
  exact ⟨hnn, hload, fun S hS hr => cut_of_inArb_packing H r lam a ha hsum (fun _ _ => le_rfl) S hS hr⟩

/-! ## Item 1: the minimum total -/

theorem exists_feasible_total_eq (G : WeightedDiGraph V) (r : V) (lam : ℝ) (hlam : 0 ≤ lam)
    (hcut : ∀ S : Finset V, S.Nonempty → r ∉ S → lam ≤ G.out S) :
    ∃ y, RootCutFeasible G r lam y ∧ total y = lam * ((Fintype.card V : ℝ) - 1) := by
  obtain ⟨a, ha, hsum, hload⟩ := exists_inArb_packing G r lam hlam hcut
  exact ⟨load a, load_feasible G r lam a ha hsum hload, by rw [total_load, hsum]⟩

/-- **Minimum total.** Under the cut condition, the least total of a feasible root-cut vector
`y ≤ G.c` is `lam (|V| - 1)`. -/
theorem isLeast_total (G : WeightedDiGraph V) (r : V) (lam : ℝ) (hlam : 0 ≤ lam)
    (hcut : ∀ S : Finset V, S.Nonempty → r ∉ S → lam ≤ G.out S) :
    IsLeast {t | ∃ y, RootCutFeasible G r lam y ∧ total y = t}
      (lam * ((Fintype.card V : ℝ) - 1)) :=
  ⟨exists_feasible_total_eq G r lam hlam hcut, fun _ ⟨_, hy, ht⟩ => ht ▸ hy.total_ge⟩

/-! ## Item 2: minimum-total vectors are packings -/

/-- **Every minimum-total feasible vector is a packing load.** -/
theorem eq_load_of_total_eq {G : WeightedDiGraph V} {r : V} {lam : ℝ} (hlam : 0 ≤ lam)
    {y : V → V → ℝ} (hy : RootCutFeasible G r lam y)
    (htot : total y = lam * ((Fintype.card V : ℝ) - 1)) :
    ∃ a : InArb r → ℝ, (∀ T, 0 ≤ a T) ∧ (∑ T, a T = lam) ∧ ∀ u v, load a u v = y u v := by
  obtain ⟨a, ha, hsum, hload⟩ := exists_inArb_packing hy.toGraph r lam hlam hy.cut
  refine ⟨a, ha, hsum, ?_⟩
  have hle : ∀ u v, load a u v ≤ y u v := hload
  have h0 : ∑ u, ∑ v, (y u v - load a u v) = 0 := by
    simp only [sum_sub_distrib]
    have := total_load a
    rw [hsum] at this
    unfold total at this htot
    linarith
  rw [sum_eq_zero_iff_of_nonneg fun u _ => sum_nonneg fun v _ => sub_nonneg.2 (hle u v)] at h0
  intro u v
  have h1 := h0 u (mem_univ u)
  rw [sum_eq_zero_iff_of_nonneg fun v _ => sub_nonneg.2 (hle u v)] at h1
  linarith [h1 v (mem_univ v)]

/-! ## Item 3: sparse optimal packings -/

/-! ### Cut algebra -/

theorem sum2_univ (y : V → V → ℝ) (X Y : Finset V) :
    ∑ u ∈ X, ∑ v ∈ Y, y u v = ∑ u, ∑ v, if u ∈ X ∧ v ∈ Y then y u v else 0 := by
  have hu : ∀ (T : Finset V) (f : V → ℝ), ∑ x ∈ T, f x = ∑ x, if x ∈ T then f x else 0 := by
    intro T f; rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [hu X]
  refine sum_congr rfl fun u _ => ?_
  by_cases h : u ∈ X
  · simp only [h, true_and, ite_true]; exact hu Y _
  · simp [h]

theorem cutVal_add (a b : V → V → ℝ) (S : Finset V) :
    cutVal (a + b) S = cutVal a S + cutVal b S := by
  simp only [cutVal, Pi.add_apply, sum_add_distrib]

theorem cutVal_smul (t : ℝ) (a : V → V → ℝ) (S : Finset V) :
    cutVal (t • a) S = t * cutVal a S := by
  simp only [cutVal, Pi.smul_apply, smul_eq_mul, mul_sum]

theorem cutVal_add_smul (x d : V → V → ℝ) (t : ℝ) (S : Finset V) :
    cutVal (x + t • d) S = cutVal x S + t * cutVal d S := by
  rw [cutVal_add, cutVal_smul]

omit [DecidableEq V] in
theorem total_add_smul (x d : V → V → ℝ) (t : ℝ) :
    total (x + t • d) = total x + t * total d := by
  simp only [total, Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, mul_sum]

/-- The uncrossing identity for outgoing cuts:
`F(S) + F(A) = F(S ∩ A) + F(S ∪ A) + y(S∖A, A∖S) + y(A∖S, S∖A)`. -/
theorem cutVal_uncross (y : V → V → ℝ) (S A : Finset V) :
    cutVal y S + cutVal y A = cutVal y (S ∩ A) + cutVal y (S ∪ A) +
      ((∑ u ∈ S \ A, ∑ v ∈ A \ S, y u v) + ∑ u ∈ A \ S, ∑ v ∈ S \ A, y u v) := by
  unfold cutVal
  rw [sum2_univ y S Sᶜ, sum2_univ y A Aᶜ, sum2_univ y (S ∩ A) (S ∩ A)ᶜ,
    sum2_univ y (S ∪ A) (S ∪ A)ᶜ, sum2_univ y (S \ A) (A \ S), sum2_univ y (A \ S) (S \ A)]
  simp only [← sum_add_distrib]
  refine sum_congr rfl fun u _ => sum_congr rfl fun v _ => ?_
  by_cases h1 : u ∈ S <;> by_cases h2 : u ∈ A <;> by_cases h3 : v ∈ S <;> by_cases h4 : v ∈ A <;>
    simp [h1, h2, h3, h4]

/-! ### Tight sets and uncrossing -/

/-- A tight constraint of `x`: a nonempty `S ∌ r` with `x(δ⁺(S)) = lam`. -/
def Tight (r : V) (lam : ℝ) (x : V → V → ℝ) (S : Finset V) : Prop :=
  S.Nonempty ∧ r ∉ S ∧ cutVal x S = lam

/-- Uncrossing two intersecting tight sets: `S ∩ A` and `S ∪ A` are tight and the crossing
arcs carry no `x`-mass. -/
theorem uncross {G : WeightedDiGraph V} {r : V} {lam : ℝ} {x : V → V → ℝ}
    (hx : RootCutFeasible G r lam x) {S A : Finset V} (hS : Tight r lam x S)
    (hA : Tight r lam x A) (hSA : (S ∩ A).Nonempty) :
    Tight r lam x (S ∩ A) ∧ Tight r lam x (S ∪ A) ∧
      ∀ u v, (u ∈ S \ A ∧ v ∈ A \ S) ∨ (u ∈ A \ S ∧ v ∈ S \ A) → x u v = 0 := by
  have hI := hx.cut (S ∩ A) hSA fun h => hS.2.1 (mem_inter.1 h).1
  have hU := hx.cut (S ∪ A) (hS.1.mono subset_union_left)
    fun h => (mem_union.1 h).elim hS.2.1 hA.2.1
  have hid := cutVal_uncross x S A
  have hc1 : 0 ≤ ∑ u ∈ S \ A, ∑ v ∈ A \ S, x u v :=
    sum_nonneg fun u _ => sum_nonneg fun v _ => hx.nonneg u v
  have hc2 : 0 ≤ ∑ u ∈ A \ S, ∑ v ∈ S \ A, x u v :=
    sum_nonneg fun u _ => sum_nonneg fun v _ => hx.nonneg u v
  rw [hS.2.2, hA.2.2] at hid
  refine ⟨⟨hSA, fun h => hS.2.1 (mem_inter.1 h).1, by linarith⟩,
    ⟨hS.1.mono subset_union_left, fun h => (mem_union.1 h).elim hS.2.1 hA.2.1, by linarith⟩, ?_⟩
  have z1 : ∑ u ∈ S \ A, ∑ v ∈ A \ S, x u v = 0 := by linarith
  have z2 : ∑ u ∈ A \ S, ∑ v ∈ S \ A, x u v = 0 := by linarith
  rw [sum_eq_zero_iff_of_nonneg fun u _ => sum_nonneg fun v _ => hx.nonneg u v] at z1 z2
  rintro u v (⟨hu, hv⟩ | ⟨hu, hv⟩)
  · exact (sum_eq_zero_iff_of_nonneg fun v _ => hx.nonneg u v).1 (z1 u hu) v hv
  · exact (sum_eq_zero_iff_of_nonneg fun v _ => hx.nonneg u v).1 (z2 u hu) v hv

/-- The cut-row identity on directions supported on the positive support of `x`. -/
theorem cutVal_uncross_supp {G : WeightedDiGraph V} {r : V} {lam : ℝ} {x : V → V → ℝ}
    (hx : RootCutFeasible G r lam x) {S A : Finset V} (hS : Tight r lam x S)
    (hA : Tight r lam x A) (hSA : (S ∩ A).Nonempty) (d : V → V → ℝ)
    (hd : ∀ u v, d u v ≠ 0 → 0 < x u v) :
    cutVal d S + cutVal d A = cutVal d (S ∩ A) + cutVal d (S ∪ A) := by
  obtain ⟨-, -, hz⟩ := uncross hx hS hA hSA
  have hd0 : ∀ u v, x u v = 0 → d u v = 0 := fun u v h => by
    by_contra hne; exact (hd u v hne).ne' h
  rw [cutVal_uncross d S A]
  have h1 : ∑ u ∈ S \ A, ∑ v ∈ A \ S, d u v = 0 :=
    sum_eq_zero fun u hu => sum_eq_zero fun v hv => hd0 u v (hz u v (Or.inl ⟨hu, hv⟩))
  have h2 : ∑ u ∈ A \ S, ∑ v ∈ S \ A, d u v = 0 :=
    sum_eq_zero fun u hu => sum_eq_zero fun v hv => hd0 u v (hz u v (Or.inr ⟨hu, hv⟩))
  rw [h1, h2]; ring

omit [Fintype V] in
/-- A member `B` laminar with `A` that crosses `S ∩ A` crosses `S`. -/
theorem crosses_of_crosses_inter {S A B : Finset V} (hBA : ¬ Crosses B A)
    (h : Crosses B (S ∩ A)) : Crosses B S := by
  obtain ⟨⟨z, hz⟩, h1, h2⟩ := h
  have hzB : z ∈ B := (mem_inter.1 hz).1
  have hzS : z ∈ S := (mem_inter.1 (mem_inter.1 hz).2).1
  have hzA : z ∈ A := (mem_inter.1 (mem_inter.1 hz).2).2
  have hBA' : B ⊆ A := by
    by_contra hB
    by_cases hAB : A ⊆ B
    · exact h2 (inter_subset_right.trans hAB)
    · exact hBA ⟨⟨z, mem_inter.2 ⟨hzB, hzA⟩⟩, hB, hAB⟩
  refine ⟨⟨z, mem_inter.2 ⟨hzB, hzS⟩⟩, fun hBS => h1 (subset_inter hBS hBA'), fun hSB => ?_⟩
  exact h2 (inter_subset_left.trans hSB)

omit [Fintype V] in
/-- A member `B` laminar with `A` that crosses `S ∪ A` crosses `S`, when `S` crosses `A`. -/
theorem crosses_of_crosses_union {S A B : Finset V} (hSA : Crosses S A) (hBA : ¬ Crosses B A)
    (h : Crosses B (S ∪ A)) : Crosses B S := by
  obtain ⟨⟨z, hz⟩, h1, h2⟩ := h
  obtain ⟨⟨w, hw⟩, -, -⟩ := hSA
  have hzB : z ∈ B := (mem_inter.1 hz).1
  have hBS : ¬ B ⊆ S := fun hBS => h1 (hBS.trans subset_union_left)
  by_cases hBA' : B ⊆ A
  · exact absurd (hBA'.trans subset_union_right) h1
  by_cases hAB : A ⊆ B
  · exact ⟨⟨w, mem_inter.2 ⟨hAB (mem_inter.1 hw).2, (mem_inter.1 hw).1⟩⟩, hBS,
      fun hSB => h2 (union_subset hSB hAB)⟩
  · have hdisj : ∀ y ∈ B, y ∉ A := fun y hyB hyA => hBA ⟨⟨y, mem_inter.2 ⟨hyB, hyA⟩⟩, hBA', hAB⟩
    have hzS : z ∈ S := by
      rcases mem_union.1 (mem_inter.1 hz).2 with h | h
      · exact h
      · exact absurd h (hdisj z hzB)
    exact ⟨⟨z, mem_inter.2 ⟨hzB, hzS⟩⟩, hBS,
      fun hSB => hdisj w (hSB (mem_inter.1 hw).1) (mem_inter.1 hw).2⟩

/-- **Laminar spanning.** If `L` is an inclusion-maximal laminar family of tight sets, then a
direction supported on the positive support of `x` that vanishes on every `L`-row vanishes on
every tight row. -/
theorem tight_rows_zero {G : WeightedDiGraph V} {r : V} {lam : ℝ} {x : V → V → ℝ}
    (hx : RootCutFeasible G r lam x) (L : Finset (Finset V)) (hLt : ∀ A ∈ L, Tight r lam x A)
    (hL : IsLaminar L) (hmax : ∀ S, Tight r lam x S → IsLaminar (insert S L) → S ∈ L)
    (d : V → V → ℝ) (hd : ∀ u v, d u v ≠ 0 → 0 < x u v) (hL0 : ∀ A ∈ L, cutVal d A = 0) :
    ∀ S, Tight r lam x S → cutVal d S = 0 := by
  classical
  suffices h : ∀ n, ∀ S, Tight r lam x S → (L.filter fun B => Crosses B S).card = n →
      cutVal d S = 0 from fun S hS => h _ S hS rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S hS hn
  by_cases hc : ∃ A ∈ L, Crosses S A
  · obtain ⟨A, hA, hSA⟩ := hc
    obtain ⟨hI, hU, -⟩ := uncross hx hS (hLt A hA) hSA.1
    have hAS : A ∈ L.filter fun B => Crosses B S := mem_filter.2 ⟨hA, hSA.symm⟩
    have hlt : ∀ T, (∀ B ∈ L, Crosses B T → Crosses B S) → ¬ Crosses A T →
        (L.filter fun B => Crosses B T).card < n := by
      intro T hT hAT
      rw [← hn]
      refine card_lt_card ⟨fun B hB => ?_, fun hsub => ?_⟩
      · obtain ⟨hBL, hBT⟩ := mem_filter.1 hB
        exact mem_filter.2 ⟨hBL, hT B hBL hBT⟩
      · exact hAT (mem_filter.1 (hsub hAS)).2
    have e1 := ih _ (hlt (S ∩ A) (fun B hB h => crosses_of_crosses_inter (hL B hB A hA) h)
      (fun h => h.2.2 inter_subset_right)) _ hI rfl
    have e2 := ih _ (hlt (S ∪ A) (fun B hB h => crosses_of_crosses_union hSA (hL B hB A hA) h)
      (fun h => h.2.1 subset_union_right)) _ hU rfl
    have e3 := cutVal_uncross_supp hx hS (hLt A hA) hSA.1 d hd
    rw [e1, e2, hL0 A hA] at e3
    linarith
  · push Not at hc
    refine hL0 S (hmax S hS fun B hB C hC => ?_)
    rcases mem_insert.1 hB with hB' | hB' <;> rcases mem_insert.1 hC with hC' | hC'
    · rw [hB', hC']; exact not_crosses_self _
    · rw [hB']; exact hc C hC'
    · rw [hC']; exact fun h => hc B hB' h.symm
    · exact hL B hB' C hC'

/-! ### Extreme points of the minimum-total face -/

/-- The minimum-total face: feasible root-cut vectors of total `lam (|V| - 1)`. -/
def minFace (G : WeightedDiGraph V) (r : V) (lam : ℝ) : Set (V → V → ℝ) :=
  {y | RootCutFeasible G r lam y ∧ total y = lam * ((Fintype.card V : ℝ) - 1)}

theorem isCompact_minFace (G : WeightedDiGraph V) (r : V) (lam : ℝ) :
    IsCompact (minFace G r lam) := by
  have heq : minFace G r lam =
      ((⋂ u, ⋂ v, {y : V → V → ℝ | 0 ≤ y u v}) ∩ (⋂ u, ⋂ v, {y : V → V → ℝ | y u v ≤ G.c u v}) ∩
        (⋂ S : Finset V, ⋂ (_ : S.Nonempty), ⋂ (_ : r ∉ S), {y | lam ≤ cutVal y S})) ∩
        {y | total y = lam * ((Fintype.card V : ℝ) - 1)} := by
    ext y
    simp only [minFace, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    exact ⟨fun ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩,
      fun ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ => ⟨⟨h1, h2, h3⟩, h4⟩⟩
  have hev : ∀ u v, Continuous fun y : V → V → ℝ => y u v := fun u v =>
    (continuous_apply v).comp (continuous_apply u)
  have hclosed : IsClosed (minFace G r lam) := by
    rw [heq]
    refine (((isClosed_iInter fun u => isClosed_iInter fun v =>
        isClosed_le continuous_const (hev u v)).inter
      (isClosed_iInter fun u => isClosed_iInter fun v =>
        isClosed_le (hev u v) continuous_const)).inter
      (isClosed_iInter fun S => isClosed_iInter fun _ => isClosed_iInter fun _ =>
        isClosed_le continuous_const ?_)).inter (isClosed_eq ?_ continuous_const)
    · exact continuous_finsetSum _ fun u _ => continuous_finsetSum _ fun v _ => hev u v
    · exact continuous_finsetSum _ fun u _ => continuous_finsetSum _ fun v _ => hev u v
  refine (isCompact_Icc (a := (0 : V → V → ℝ)) (b := G.c)).of_isClosed_subset hclosed ?_
  intro y hy
  exact ⟨fun u v => hy.1.nonneg u v, fun u v => hy.1.le_cap u v⟩

/-- **Perturbation lemma.** At an extreme point `x` of the minimum-total face, a direction
supported on the free arcs of `x` and vanishing on every tight row is zero. -/
theorem perturb_eq_zero {G : WeightedDiGraph V} {r : V} {lam : ℝ} {x : V → V → ℝ}
    (hxE : x ∈ (minFace G r lam).extremePoints ℝ) (d : V → V → ℝ)
    (hd : ∀ u v, d u v ≠ 0 → 0 < x u v ∧ x u v < G.c u v)
    (ht : ∀ S, Tight r lam x S → cutVal d S = 0) : d = 0 := by
  obtain ⟨⟨hx, hxt⟩, hext⟩ := hxE
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), RootCutFeasible G r lam (x + t • d) := by
    have harc : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ u v,
        0 ≤ (x + t • d) u v ∧ (x + t • d) u v ≤ G.c u v := by
      refine eventually_all.2 fun u => eventually_all.2 fun v => ?_
      by_cases h0 : d u v = 0
      · exact Eventually.of_forall fun t => by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h0, mul_zero, add_zero]
          exact ⟨hx.nonneg u v, hx.le_cap u v⟩
      · obtain ⟨h1, h2⟩ := hd u v h0
        have hT : Tendsto (fun t : ℝ => x u v + t * d u v) (𝓝 0) (𝓝 (x u v)) := by
          have := ((tendsto_id (x := 𝓝 (0 : ℝ))).mul_const (d u v)).const_add (x u v)
          simpa using this
        filter_upwards [hT.eventually (lt_mem_nhds h1), hT.eventually (gt_mem_nhds h2)]
          with t ht1 ht2
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        exact ⟨ht1.le, ht2.le⟩
    have hcuts : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ S : Finset V, S.Nonempty → r ∉ S →
        lam ≤ cutVal (x + t • d) S := by
      refine eventually_all.2 fun S => ?_
      by_cases hS : S.Nonempty ∧ r ∉ S
      · by_cases htS : cutVal x S = lam
        · refine Eventually.of_forall fun t _ _ => ?_
          rw [cutVal_add_smul, ht S ⟨hS.1, hS.2, htS⟩, htS]; simp
        · have hlt : lam < cutVal x S := lt_of_le_of_ne (hx.cut S hS.1 hS.2) (Ne.symm htS)
          have hT : Tendsto (fun t : ℝ => cutVal x S + t * cutVal d S) (𝓝 0)
              (𝓝 (cutVal x S)) := by
            have := ((tendsto_id (x := 𝓝 (0 : ℝ))).mul_const (cutVal d S)).const_add
              (cutVal x S)
            simpa using this
          filter_upwards [hT.eventually (lt_mem_nhds hlt)] with t h _ _
          rw [cutVal_add_smul]; exact h.le
      · exact Eventually.of_forall fun t h1 h2 => absurd ⟨h1, h2⟩ hS
    filter_upwards [harc, hcuts] with t h1 h2
    exact ⟨fun u v => (h1 u v).1, fun u v => (h1 u v).2, h2⟩
  have hev' : ∀ᶠ t in 𝓝 (0 : ℝ), RootCutFeasible G r lam (x + (-t) • d) := by
    have : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_neg.tendsto (0 : ℝ))
    exact this.eventually hev
  obtain ⟨t, ⟨h1, h2⟩, htpos⟩ :=
    (((hev.and hev').filter_mono nhdsWithin_le_nhds).and
      (eventually_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)) (a := 0))).exists
  have htpos' : 0 < t := htpos
  have g1 := h1.total_ge
  have g2 := h2.total_ge
  rw [total_add_smul] at g1 g2
  rw [hxt] at g1 g2
  have hD : t * total d = 0 := by nlinarith
  have hF1 : x + t • d ∈ minFace G r lam := ⟨h1, by rw [total_add_smul, hxt, hD, add_zero]⟩
  have hF2 : x + (-t) • d ∈ minFace G r lam :=
    ⟨h2, by rw [total_add_smul, hxt, neg_mul, hD, neg_zero, add_zero]⟩
  have hseg : x ∈ openSegment ℝ (x + t • d) (x + (-t) • d) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    funext u v
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hxx := hext hF1 hF2 hseg
  have : t • d = 0 := by
    have := congrArg (fun z => z - x) hxx
    simpa using this
  exact (smul_eq_zero.1 this).resolve_left htpos'.ne'

/-! ### The sparse optimal packing -/

/-- Extension by zero of a vector on a finite arc set. -/
def extK (K : Finset (V × V)) (f : K → ℝ) : V → V → ℝ :=
  fun u v => if h : (u, v) ∈ K then f ⟨(u, v), h⟩ else 0

omit [Fintype V] in
theorem extK_add (K : Finset (V × V)) (f g : K → ℝ) : extK K (f + g) = extK K f + extK K g := by
  funext u v; simp only [extK, Pi.add_apply]; split_ifs <;> simp

omit [Fintype V] in
theorem extK_smul (K : Finset (V × V)) (c : ℝ) (f : K → ℝ) : extK K (c • f) = c • extK K f := by
  funext u v; simp only [extK, Pi.smul_apply, smul_eq_mul]; split_ifs <;> simp

/-- The tight-row map `ℝ^K → ℝ^L`, `f ↦ (cutVal (extK f) A)_{A ∈ L}`. -/
def rowMap (K : Finset (V × V)) (L : Finset (Finset V)) : (K → ℝ) →ₗ[ℝ] (L → ℝ) where
  toFun f A := cutVal (extK K f) A
  map_add' f g := by funext A; simp only [extK_add, cutVal_add, Pi.add_apply]
  map_smul' c f := by
    funext A; simp only [extK_smul, cutVal_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

/-- **Sparse optimal root-cut vector.** Under the cut condition there is a minimum-total
feasible root-cut vector `y ≤ G.c` with at most `2 (|V| - 1)` free arcs `0 < y u v < G.c u v`. -/
theorem exists_sparse_min_feasible (G : WeightedDiGraph V) (r : V) (lam : ℝ) (hlam : 0 ≤ lam)
    (hcut : ∀ S : Finset V, S.Nonempty → r ∉ S → lam ≤ G.out S) :
    ∃ y, RootCutFeasible G r lam y ∧ total y = lam * ((Fintype.card V : ℝ) - 1) ∧
      (freeArcs G y).card ≤ 2 * (Fintype.card V - 1) := by
  classical
  obtain ⟨x, hxE⟩ := (isCompact_minFace G r lam).extremePoints_nonempty
    (by obtain ⟨y, hy, ht⟩ := exists_feasible_total_eq G r lam hlam hcut; exact ⟨y, hy, ht⟩)
  have hxF : x ∈ minFace G r lam := hxE.1
  -- an inclusion-maximal laminar family of tight sets
  let Tt : Finset (Finset V) := univ.filter (Tight r lam x)
  obtain ⟨L, hLmem, hLmax⟩ := exists_max_image (Tt.powerset.filter IsLaminar) card
    ⟨∅, mem_filter.2 ⟨empty_mem_powerset _, fun A hA => absurd hA (notMem_empty A)⟩⟩
  obtain ⟨hLsub, hLlam⟩ := mem_filter.1 hLmem
  have hLt : ∀ A ∈ L, Tight r lam x A := fun A hA => (mem_filter.1 (mem_powerset.1 hLsub hA)).2
  have hmax : ∀ S, Tight r lam x S → IsLaminar (insert S L) → S ∈ L := by
    intro S hS hins
    by_contra hSL
    have := hLmax (insert S L) (mem_filter.2 ⟨mem_powerset.2
      (insert_subset (mem_filter.2 ⟨mem_univ _, hS⟩) (mem_powerset.1 hLsub)), hins⟩)
    rw [card_insert_of_notMem hSL] at this
    omega
  -- the tight-row map on the free arcs is injective
  set K := freeArcs G x
  have hinj : Function.Injective (rowMap K L) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    have hsupp : ∀ u v, extK K f u v ≠ 0 → 0 < x u v ∧ x u v < G.c u v := by
      intro u v h
      unfold extK at h
      split_ifs at h with hK
      · exact mem_freeArcs.1 hK
      · exact absurd rfl h
    have hd0 := perturb_eq_zero hxE (extK K f) hsupp
      (tight_rows_zero hxF.1 L hLt hLlam hmax _ (fun u v h => (hsupp u v h).1)
        fun A hA => congrFun hf ⟨A, hA⟩)
    funext e
    have := congrFun (congrFun hd0 e.1.1) e.1.2
    simpa [extK] using this
  have hrank := LinearMap.finrank_le_finrank_of_injective hinj
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hrank
  have hLb := laminar_card_le (univ.erase r) L hLlam fun B hB =>
    ⟨(hLt B hB).1, fun z hz => mem_erase.2 ⟨fun h => (hLt B hB).2.1 (h ▸ hz), mem_univ _⟩⟩
  rw [card_erase_of_mem (mem_univ r), card_univ] at hLb
  exact ⟨x, hxF.1, hxF.2, hrank.trans hLb⟩

/-- **Sparse optimal packing.** Under the cut condition there is a packing of in-arborescences
toward `r` of value `lam` under `G` whose load has minimum total `lam (|V| - 1)` among feasible
root-cut vectors and at most `2 (|V| - 1)` free arcs `0 < load < G.c`. -/
theorem exists_sparse_inArb_packing (G : WeightedDiGraph V) (r : V) (lam : ℝ) (hlam : 0 ≤ lam)
    (hcut : ∀ S : Finset V, S.Nonempty → r ∉ S → lam ≤ G.out S) :
    ∃ a : InArb r → ℝ, (∀ T, 0 ≤ a T) ∧ (∑ T, a T = lam) ∧ (∀ u v, load a u v ≤ G.c u v) ∧
      total (load a) = lam * ((Fintype.card V : ℝ) - 1) ∧
      (freeArcs G (load a)).card ≤ 2 * (Fintype.card V - 1) := by
  obtain ⟨y, hy, ht, hK⟩ := exists_sparse_min_feasible G r lam hlam hcut
  obtain ⟨a, ha, hsum, hload⟩ := eq_load_of_total_eq hlam hy ht
  have hay : load a = y := funext fun u => funext fun v => hload u v
  exact ⟨a, ha, hsum, fun u v => hay ▸ hy.le_cap u v, hay ▸ ht, hay ▸ hK⟩

/-- **Sparse optimal out-arborescence packing** from `r` (by reversal): under the in-cut
condition there is a packing of out-arborescences of value `lam` whose arc load has total
`lam (|V| - 1)` and at most `2 (|V| - 1)` free arcs `0 < outLoad < G.c`. -/
theorem exists_sparse_outArb_packing (G : WeightedDiGraph V) (r : V) (lam : ℝ) (hlam : 0 ≤ lam)
    (hcut : ∀ S : Finset V, S.Nonempty → r ∉ S → lam ≤ G.out Sᶜ) :
    ∃ a : InArb r → ℝ, (∀ T, 0 ≤ a T) ∧ (∑ T, a T = lam) ∧ (∀ u v, outLoad a u v ≤ G.c u v) ∧
      total (outLoad a) = lam * ((Fintype.card V : ℝ) - 1) ∧
      (freeArcs G (outLoad a)).card ≤ 2 * (Fintype.card V - 1) := by
  obtain ⟨a, ha, hsum, hload, htot, hK⟩ := exists_sparse_inArb_packing G.rev r lam hlam
    (fun S hS hr => by rw [G.rev_out]; exact hcut S hS hr)
  refine ⟨a, ha, hsum, (outLoad_le_iff G a).2 hload, ?_, ?_⟩
  · rw [← htot]; unfold total; simp only [outLoad_eq_load]; exact sum_comm
  · have heq : freeArcs G (outLoad a) =
        (freeArcs G.rev (load a)).map (Equiv.prodComm V V).toEmbedding := by
      ext ⟨u, v⟩
      simp only [mem_map_equiv, mem_freeArcs, outLoad_eq_load, WeightedDiGraph.rev,
        Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap_prod_mk]
    rw [heq, card_map]; exact hK

end CutQueryComplexity.DirectedCertificate
