import CutQueryComplexity.CanonicalST.LongEdge.Assignments
import CutQueryComplexity.CanonicalST.LongEdge.Bins
import CutQueryComplexity.Primitive.CrossSearch

/-!
# Public deterministic long-edge search

Each assignment/color pair costs one three-query mass test. The first
positive answer triggers one logarithmic crossing-edge search, then returns.
No graph is an argument of the program, and the public budget applies to
every oracle. An explicit learned graph can be subtracted at unit query cost.
-/

set_option autoImplicit false

namespace CutQueryComplexity.CanonicalST.LongEdge

open Finset WeightedGraph
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

def testSets (φ : V → ℚ) (δ : ℚ) (A : Assignment) (r : Fin 3) :
    Finset V × Finset V :=
  (univ.filter (fun v => A.p (binIndex δ (φ v)) = r ∧ A.q (binIndex δ (φ v)) = false),
   univ.filter (fun v => A.p (binIndex δ (φ v)) = r ∧ A.q (binIndex δ (φ v)) = true))

def tests (φ : V → ℚ) (δ : ℚ) : List (Finset V × Finset V) :=
  ((family (binCount δ)).product (univ : Finset (Fin 3)).toList).map
    (fun Ar => testSets φ δ Ar.1 Ar.2)

omit [DecidableEq V] in
theorem tests_length (φ : V → ℚ) (δ : ℚ) :
    (tests φ δ).length = 24 * Nat.clog 2 (binCount δ) := by
  rw [tests, List.length_map]
  calc
    ((family (binCount δ)).product (univ : Finset (Fin 3)).toList).length =
        (family (binCount δ)).length * (univ : Finset (Fin 3)).toList.length :=
      List.length_product _ _
    _ = 24 * Nat.clog 2 (binCount δ) := by
      simp only [family_length, Finset.length_toList, Finset.card_univ, Fintype.card_fin]
      omega

omit [DecidableEq V] in
theorem testSets_disjoint (φ : V → ℚ) (δ : ℚ) (A : Assignment) (r : Fin 3) :
    Disjoint (testSets φ δ A r).1 (testSets φ δ A r).2 := by
  apply disjoint_left.mpr
  intro v hv hw
  have hv := (mem_filter.mp hv).2.2
  have hw := (mem_filter.mp hw).2.2
  simp_all

omit [DecidableEq V] in
theorem tests_disjoint (φ : V → ℚ) (δ : ℚ) :
    ∀ ST ∈ tests φ δ, Disjoint ST.1 ST.2 := by
  intro ST hST
  obtain ⟨⟨A, r⟩, _, rfl⟩ := List.mem_map.mp hST
  exact testSets_disjoint φ δ A r

private theorem match_gap {ℓ i j : ℕ} {A : Assignment}
    (hA : A ∈ family ℓ) (hi : i < ℓ) (hj : j < ℓ)
    (hp : A.p i = A.p j) (hq : A.q i ≠ A.q j) : i + 2 ≤ j ∨ j + 2 ≤ i := by
  by_contra h
  have hc : i = j ∨ i + 1 = j ∨ j + 1 = i := by omega
  rcases hc with h | h | h
  · exact hq (congrArg A.q h)
  · exact family_adjacent hA (i := i) (by omega) (by simpa only [h] using hp)
  · exact family_adjacent hA (i := j) (by omega) (by simpa only [h] using hp.symm)

omit [DecidableEq V] in
theorem tests_sound (φ : V → ℚ) {δ : ℚ} (hδ : 0 < δ)
    (hφ : ∀ v, 0 ≤ φ v ∧ φ v ≤ 1) {ST : Finset V × Finset V}
    (hST : ST ∈ tests φ δ) {u v : V} (hu : u ∈ ST.1) (hv : v ∈ ST.2) :
    δ / 2 ≤ |φ u - φ v| := by
  obtain ⟨⟨A, r⟩, hAr, rfl⟩ := List.mem_map.mp hST
  have hA := (List.mem_product.mp hAr).1
  obtain ⟨hpu, hqu⟩ := (mem_filter.mp hu).2
  obtain ⟨hpv, hqv⟩ := (mem_filter.mp hv).2
  have hq : A.q (binIndex δ (φ u)) ≠ A.q (binIndex δ (φ v)) := by
    rw [hqu, hqv]
    decide
  exact bin_backward hδ (hφ u).1 (hφ v).1
    (match_gap hA (binIndex_lt_count hδ (hφ u).2) (binIndex_lt_count hδ (hφ v).2)
      (hpu.trans hpv.symm) hq)

omit [DecidableEq V] in
theorem tests_cover (φ : V → ℚ) {δ : ℚ} (hδ : 0 < δ)
    (hφ : ∀ v, 0 ≤ φ v ∧ φ v ≤ 1) {u v : V} (hlength : δ ≤ |φ u - φ v|) :
    ∃ ST ∈ tests φ δ, (u ∈ ST.1 ∧ v ∈ ST.2) ∨ (v ∈ ST.1 ∧ u ∈ ST.2) := by
  obtain ⟨A, hA, hp, hq⟩ := family_separates
    (binIndex_lt_count hδ (hφ u).2) (binIndex_lt_count hδ (hφ v).2)
    (bin_forward hδ (hφ u).1 (hφ v).1 hlength)
  let r := A.p (binIndex δ (φ u))
  refine ⟨testSets φ δ A r, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨(A, r), List.mem_product.mpr
      ⟨hA, mem_toList.mpr (mem_univ _)⟩, rfl⟩
  · cases hu : A.q (binIndex δ (φ u)) <;>
      cases hv : A.q (binIndex δ (φ v)) <;>
      simp_all [testSets, r]

def scanTests (k : ℕ) : (ts : List (Finset V × Finset V)) →
    DTree (Finset V) ℝ (Option (V × V)) (3 * ts.length + 6 * (k + 1))
  | [] => DTree.pure none
  | ST :: ts =>
      ((crossQuery ST.1 ST.2).bind fun mass =>
        if 0 < mass then (findCross k ST.1 ST.2).weaken
          (r := 3 * ts.length + 6 * (k + 1)) (by omega)
        else scanTests k ts).cast (by simp; omega)

theorem scanTests_eval_cons (oracle : Finset V → ℝ) (k : ℕ)
    (ST : Finset V × Finset V) (ts : List (Finset V × Finset V)) :
    (scanTests k (ST :: ts)).eval oracle =
      if 0 < (crossQuery ST.1 ST.2).eval oracle then (findCross k ST.1 ST.2).eval oracle
      else (scanTests k ts).eval oracle := by
  simp only [scanTests, DTree.eval_cast, DTree.eval_bind]
  split_ifs <;> simp [DTree.eval]

def ScanResult (G : WeightedGraph V) (ts : List (Finset V × Finset V)) :
    Option (V × V) → Prop
  | none => ∀ ST ∈ ts, G.cross ST.1 ST.2 = 0
  | some (u, v) => ∃ ST ∈ ts, u ∈ ST.1 ∧ v ∈ ST.2 ∧ 0 < G.w u v

theorem scanTests_correct (G : WeightedGraph V) (k : ℕ) (hn : Fintype.card V ≤ 2 ^ k)
    (ts : List (Finset V × Finset V)) (hd : ∀ ST ∈ ts, Disjoint ST.1 ST.2) :
    ScanResult G ts ((scanTests k ts).eval G.cut) := by
  induction ts with
  | nil => simp [scanTests, ScanResult]
  | cons ST ts ih =>
      have hST := hd ST (List.mem_cons_self ..)
      have htail : ∀ X ∈ ts, Disjoint X.1 X.2 := fun X hX => hd X (List.mem_cons_of_mem _ hX)
      rw [scanTests_eval_cons, crossQuery_eval G hST]
      by_cases hp : 0 < G.cross ST.1 ST.2
      · rw [ite_eq_left hp]
        have hf := findCross_correct G k hST hn
        cases he : (findCross k ST.1 ST.2).eval G.cut with
        | none =>
            simp only [he, CrossResult] at hf
            exact False.elim (by linarith)
        | some e =>
            rcases e with ⟨u, v⟩
            simp only [he, CrossResult] at hf
            exact ⟨ST, List.mem_cons_self .., hf⟩
      · rw [ite_eq_right hp]
        have hz : G.cross ST.1 ST.2 = 0 :=
          le_antisymm (not_lt.mp hp) (G.cross_nonneg _ _)
        have ht := ih htail
        cases he : (scanTests k ts).eval G.cut with
        | none =>
            simp only [he, ScanResult] at ht ⊢
            intro X hX
            rcases List.mem_cons.mp hX with rfl | hX
            · exact hz
            · exact ht X hX
        | some e =>
            rcases e with ⟨u, v⟩
            simp only [he, ScanResult] at ht ⊢
            obtain ⟨X, hX, hrest⟩ := ht
            exact ⟨X, List.mem_cons_of_mem _ hX, hrest⟩

def longEdgeBudget (V : Type) [Fintype V] (δ : ℚ) : ℕ :=
  72 * Nat.clog 2 (binCount δ) + 6 * (Nat.clog 2 (Fintype.card V) + 1)

def longEdge (φ : V → ℚ) (δ : ℚ) :
    DTree (Finset V) ℝ (Option (V × V)) (longEdgeBudget V δ) :=
  (scanTests (searchDepth V) (tests φ δ)).cast (by
    rw [tests_length]
    unfold longEdgeBudget searchDepth
    ring)

def LongEdgeResult (G : WeightedGraph V) (φ : V → ℚ) (δ : ℚ) :
    Option (V × V) → Prop
  | none => ∀ u v, 0 < G.w u v → |φ u - φ v| < δ
  | some (u, v) => 0 < G.w u v ∧ δ / 2 ≤ |φ u - φ v|

theorem longEdge_correct (G : WeightedGraph V) (φ : V → ℚ) {δ : ℚ}
    (hδ : 0 < δ) (hφ : ∀ v, 0 ≤ φ v ∧ φ v ≤ 1) :
    LongEdgeResult G φ δ ((longEdge φ δ).eval G.cut) := by
  have hs := scanTests_correct G (searchDepth V) (Nat.le_pow_clog (by decide) _)
    (tests φ δ) (tests_disjoint φ δ)
  simp only [longEdge, DTree.eval_cast]
  cases he : (scanTests (searchDepth V) (tests φ δ)).eval G.cut with
  | none =>
      simp only [he, ScanResult] at hs
      intro u v huv
      by_contra hlen
      obtain ⟨ST, hST, hsep⟩ := tests_cover φ hδ hφ (not_lt.mp hlen)
      have hp : 0 < G.cross ST.1 ST.2 := by
        apply (G.cross_pos_iff _ _).mpr
        rcases hsep with ⟨hu, hv⟩ | ⟨hv, hu⟩
        · exact ⟨u, hu, v, hv, huv⟩
        · exact ⟨v, hv, u, hu, by simpa only [G.symm v u] using huv⟩
      rw [hs ST hST] at hp
      exact (lt_irrefl 0) hp
  | some e =>
      rcases e with ⟨u, v⟩
      simp only [he, ScanResult] at hs
      obtain ⟨ST, hST, hu, hv, hp⟩ := hs
      exact ⟨hp, tests_sound φ hδ hφ hST hu hv⟩

theorem longEdge_cost (φ : V → ℚ) (δ : ℚ) (oracle : Finset V → ℝ) :
    (longEdge φ δ).cost oracle ≤ longEdgeBudget V δ := DTree.cost_le _ _

omit [DecidableEq V] in
theorem longEdgeBudget_le {δ : ℚ} (hδ : 0 < δ) :
    longEdgeBudget V δ ≤ 72 * Nat.clog 2 (reciprocalScale δ) +
      6 * Nat.clog 2 (Fintype.card V) + 150 := by
  have h := binCount_clog_le hδ
  unfold longEdgeBudget
  omega

/-- Each virtual deletion query uses one original query and the explicit K. -/
def deletionLongEdge (K : WeightedGraph V) (φ : V → ℚ) (δ : ℚ) :
    DTree (Finset V) ℝ (Option (V × V)) (longEdgeBudget V δ) :=
  ((longEdge φ δ).substitute (deletionQuery K)).cast (Nat.mul_one _)

theorem deletionLongEdge_correct (G K : WeightedGraph V) (hK : ∀ u v, K.w u v ≤ G.w u v)
    (φ : V → ℚ) {δ : ℚ} (hδ : 0 < δ) (hφ : ∀ v, 0 ≤ φ v ∧ φ v ≤ 1) :
    LongEdgeResult (G.subtract K) φ δ ((deletionLongEdge K φ δ).eval G.cut) := by
  have he : (fun S => (deletionQuery K S).eval G.cut) = (G.subtract K).cut :=
    funext (deletionQuery_eval G K hK)
  simp only [deletionLongEdge, DTree.eval_cast, DTree.eval_substitute, he]
  exact longEdge_correct (G.subtract K) φ hδ hφ

theorem deletionLongEdge_cost (K : WeightedGraph V) (φ : V → ℚ) (δ : ℚ)
    (oracle : Finset V → ℝ) :
    (deletionLongEdge K φ δ).cost oracle ≤ longEdgeBudget V δ := DTree.cost_le _ _

/-- A successful deletion search finds strictly more capacity in the actual
input than in the explicitly learned graph. -/
theorem deletionLongEdge_found (G K : WeightedGraph V) (hK : ∀ u v, K.w u v ≤ G.w u v)
    (φ : V → ℚ) {δ : ℚ} (hδ : 0 < δ) (hφ : ∀ v, 0 ≤ φ v ∧ φ v ≤ 1)
    {u v : V} (he : (deletionLongEdge K φ δ).eval G.cut = some (u, v)) :
    K.w u v < G.w u v ∧ δ / 2 ≤ |φ u - φ v| := by
  have h := deletionLongEdge_correct G K hK φ hδ hφ
  rw [he] at h
  refine ⟨?_, h.2⟩
  have hp := h.1
  change 0 < max 0 (G.w u v - K.w u v) at hp
  rcases lt_max_iff.mp hp with hp | hp
  · exact False.elim ((lt_irrefl 0) hp)
  · linarith

/-- In the unit case the returned edge is genuinely unknown: its learned
weight is zero and its actual input weight is one. -/
theorem deletionLongEdge_found_unit (G K : WeightedGraph V)
    (hGunit : ∀ u v, G.w u v = 0 ∨ G.w u v = 1)
    (hKunit : ∀ u v, K.w u v = 0 ∨ K.w u v = 1)
    (hK : ∀ u v, K.w u v ≤ G.w u v)
    (φ : V → ℚ) {δ : ℚ} (hδ : 0 < δ) (hφ : ∀ v, 0 ≤ φ v ∧ φ v ≤ 1)
    {u v : V} (he : (deletionLongEdge K φ δ).eval G.cut = some (u, v)) :
    K.w u v = 0 ∧ G.w u v = 1 ∧ δ / 2 ≤ |φ u - φ v| := by
  obtain ⟨hlt, hlen⟩ := deletionLongEdge_found G K hK φ hδ hφ he
  have hn := K.nonneg u v
  have hg : G.w u v = 1 := (hGunit u v).resolve_left (by
    intro hz
    rw [hz] at hlt
    linarith)
  have hk : K.w u v = 0 := (hKunit u v).resolve_right (by
    intro ho
    rw [hg, ho] at hlt
    exact (lt_irrefl 1) hlt)
  exact ⟨hk, hg, hlen⟩

end
end CutQueryComplexity.CanonicalST.LongEdge

#print axioms CutQueryComplexity.CanonicalST.LongEdge.tests_sound
#print axioms CutQueryComplexity.CanonicalST.LongEdge.tests_cover
#print axioms CutQueryComplexity.CanonicalST.LongEdge.scanTests_correct
#print axioms CutQueryComplexity.CanonicalST.LongEdge.longEdge_correct
#print axioms CutQueryComplexity.CanonicalST.LongEdge.longEdge_cost
#print axioms CutQueryComplexity.CanonicalST.LongEdge.longEdgeBudget_le
#print axioms CutQueryComplexity.CanonicalST.LongEdge.deletionLongEdge_correct
#print axioms CutQueryComplexity.CanonicalST.LongEdge.deletionLongEdge_cost
#print axioms CutQueryComplexity.CanonicalST.LongEdge.deletionLongEdge_found_unit
