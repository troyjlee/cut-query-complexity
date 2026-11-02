import CutQueryComplexity.Search.SMAWK
import CutQueryComplexity.Search.Combinators
import CutQueryComplexity.Search.BinarySearch
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-! # All minimum entries of a Monge matrix at a known level

Given sorted row and column lists, a Monge matrix `M` and a level `ℓ` below every entry of
the rectangle, `allMinima rows cols ℓ` returns exactly the pairs `(i, j)` with `M i j = ℓ`.
The level need not be attained; empty rectangles give the empty list.

1. SMAWK finds the leftmost minimum `L i` of every row.
2. SMAWK on the matrix with both index orders reversed finds the rightmost minimum `R i`
   (`isLeftmostMin_dual_iff`; reversing both orders keeps the Monge inequality).
3. One query per row keeps the *active* rows, whose minimum value is `ℓ`.
4. For every column `j`, the active rows with `L i ≤ j ≤ R i` all have the same entry at `j`
   (`monge_equal_between_opposite_minima`), so one query decides all of them.

The minima of one row need not form an interval (two equal rows `[0, 1, 0]` are Monge); the
representative query resolves the gaps. Every entry equal to `ℓ` lies between the extreme
minima of its row and is therefore reported.

`allMinima_cost`: at most `9 * cols.length + 25 * rows.length` entry evaluations, independent
of the number of reported pairs. `allMinima_spec`: exact membership.
-/

set_option autoImplicit false

namespace CutQueryComplexity
namespace Search

open Comp

variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ]

/-! ### Extreme minima and the opposite-corner identity -/

/-- `j` is the rightmost minimum of row `r` among the columns `L`. -/
def IsRightmostMin (M : ι → κ → ℝ) (r : ι) (L : List κ) (j : κ) : Prop :=
  j ∈ L ∧ (∀ j' ∈ L, M r j ≤ M r j') ∧ ∀ j' ∈ L, j < j' → M r j < M r j'

/-- The matrix with both index orders reversed. -/
def dualM (M : ι → κ → ℝ) : ιᵒᵈ → κᵒᵈ → ℝ :=
  fun i j => M (OrderDual.ofDual i) (OrderDual.ofDual j)

omit [LinearOrder ι] [LinearOrder κ] in
theorem mem_reverse_map_toDual {L : List κ} {j : κᵒᵈ} :
    j ∈ L.reverse.map OrderDual.toDual ↔ OrderDual.ofDual j ∈ L := by
  simp only [List.mem_map, List.mem_reverse]
  exact ⟨fun ⟨x, hx, hxj⟩ => hxj ▸ hx, fun h => ⟨_, h, rfl⟩⟩

omit [LinearOrder ι] in
/-- The leftmost minimum in the reversed column order is the rightmost minimum. -/
theorem isLeftmostMin_dual_iff {M : ι → κ → ℝ} {r : ι} {L : List κ} {j : κᵒᵈ} :
    IsLeftmostMin (dualM M) (OrderDual.toDual r) (L.reverse.map OrderDual.toDual) j ↔
      IsRightmostMin M r L (OrderDual.ofDual j) := by
  unfold IsLeftmostMin IsRightmostMin dualM
  constructor
  · rintro ⟨hj, hmin, hleft⟩
    refine ⟨mem_reverse_map_toDual.mp hj, fun j' hj' => ?_, fun j' hj' hlt => ?_⟩
    · exact hmin (OrderDual.toDual j') (mem_reverse_map_toDual.mpr hj')
    · exact hleft (OrderDual.toDual j') (mem_reverse_map_toDual.mpr hj') hlt
  · rintro ⟨hj, hmin, hright⟩
    refine ⟨mem_reverse_map_toDual.mpr hj, fun j' hj' => ?_, fun j' hj' hlt => ?_⟩
    · exact hmin _ (mem_reverse_map_toDual.mp hj')
    · exact hright _ (mem_reverse_map_toDual.mp hj') hlt

omit [LinearOrder ι] [LinearOrder κ] in
theorem pairwise_reverse_map_toDual {α : Type} [LinearOrder α] {L : List α}
    (h : L.Pairwise (· < ·)) : (L.reverse.map OrderDual.toDual).Pairwise (· < ·) := by
  rw [List.pairwise_map, List.pairwise_reverse]
  exact h.imp fun hab => OrderDual.toDual_lt_toDual.mpr hab

/-- Reversing both index orders keeps the Monge inequality. -/
theorem IsMonge.dual {M : ι → κ → ℝ} {rows : List ι} {cols : List κ} (h : IsMonge M rows cols) :
    IsMonge (dualM M) (rows.reverse.map OrderDual.toDual) (cols.reverse.map OrderDual.toDual) := by
  intro r hr r' hr' c hc c' hc' hrr hcc
  have := h _ (mem_reverse_map_toDual.mp hr') _ (mem_reverse_map_toDual.mp hr)
    _ (mem_reverse_map_toDual.mp hc') _ (mem_reverse_map_toDual.mp hc) hrr hcc
  unfold dualM
  linarith

/-- Opposite minimum corners force the two rows to agree between them: if row `i` attains the
lower bound `lam` at `r`, row `k > i` attains it at `l`, and `l ≤ j ≤ r`, then the two rows
have the same entry at `j`. -/
theorem monge_equal_between_opposite_minima
    {M : ι → κ → ℝ} {rows : List ι} {cols : List κ}
    (hM : IsMonge M rows cols) {lam : ℝ}
    (hlow : ∀ i ∈ rows, ∀ j ∈ cols, lam ≤ M i j)
    {i k : ι} (hi : i ∈ rows) (hk : k ∈ rows) (hik : i < k)
    {l j r : κ} (hl : l ∈ cols) (hj : j ∈ cols) (hr : r ∈ cols)
    (hlj : l ≤ j) (hjr : j ≤ r)
    (hir : M i r = lam) (hkl : M k l = lam) :
    M i j = M k j := by
  by_cases hlr : l = r
  · have hjl : j = l := le_antisymm (hlr ▸ hjr) hlj
    subst j
    simpa [hlr, hir] using hkl.symm
  have hlr' : l < r := lt_of_le_of_ne (hlj.trans hjr) hlr
  have hcorner := hM i hi k hk l hl r hr hik hlr'
  have hil : M i l = lam := by
    have := hlow i hi l hl
    have := hlow k hk r hr
    linarith
  have hkr : M k r = lam := by
    have := hlow i hi l hl
    have := hlow k hk r hr
    linarith
  apply le_antisymm
  · rcases hjr.lt_or_eq with hjr' | rfl
    · have := hM i hi k hk j hj r hr hik hjr'
      linarith
    · rw [hir, hkr]
  · rcases hlj.lt_or_eq with hlj' | rfl
    · have := hM i hi k hk l hl j hj hik hlj'
      linarith
    · rw [hil, hkl]

/-! ### The program -/

/-- Keep the rows whose leftmost minimum has value `ℓ`, one query per row with both extreme
minima known. -/
noncomputable def activeRows (ℓ : ℝ) :
    List (ι × Option κ × Option κ) → Comp (ι × κ) ℝ (List (ι × κ × κ))
  | [] => Comp.pure []
  | (i, some l, some r) :: rest => (ask (i, l)).bind fun x =>
      (activeRows ℓ rest).map fun t => if x = ℓ then (i, l, r) :: t else t
  | (_, none, _) :: rest => activeRows ℓ rest
  | (_, some _, none) :: rest => activeRows ℓ rest

/-- Report column `j` for the listed active rows: one query in the first of them. -/
noncomputable def colReport (ℓ : ℝ) (j : κ) :
    List (ι × κ × κ) → Comp (ι × κ) ℝ (List (ι × κ))
  | [] => Comp.pure []
  | t :: A => (ask (t.1, j)).map fun x =>
      if x = ℓ then (t :: A).map fun t => (t.1, j) else []

/-- The active rows whose extreme minima enclose column `j`. -/
def enclosing (act : List (ι × κ × κ)) (j : κ) : List (ι × κ × κ) :=
  act.filter fun t => decide (t.2.1 ≤ j ∧ j ≤ t.2.2)

/-- Report column `j`. -/
noncomputable def colStep (act : List (ι × κ × κ)) (ℓ : ℝ) (j : κ) :
    Comp (ι × κ) ℝ (List (ι × κ)) :=
  colReport ℓ j (enclosing act j)

/-- **All minimum entries** of a Monge matrix at the level `ℓ`: two SMAWK runs, one query per
row and one query per column. -/
noncomputable def allMinima (rows : List ι) (cols : List κ) (ℓ : ℝ) :
    Comp (ι × κ) ℝ (List (ι × κ)) :=
  if rows = [] ∨ cols = [] then Comp.pure [] else
    (smawk rows cols).bind fun Ls =>
      ((smawk (rows.reverse.map OrderDual.toDual) (cols.reverse.map OrderDual.toDual)).mapQ
          fun p => (OrderDual.ofDual p.1, OrderDual.ofDual p.2)).bind fun Rs =>
        (activeRows ℓ (rows.zip (Ls.zip (Rs.reverse.map (Option.map OrderDual.ofDual))))).bind
          fun act => (mapList (colStep act ℓ) cols).map List.flatten

/-! ### Specifications of the pieces -/

variable {M : ι → κ → ℝ}

omit [LinearOrder ι] [LinearOrder κ] in
theorem activeRows_spec (ℓ : ℝ) : ∀ E : List (ι × Option κ × Option κ),
    (∀ t, t ∈ (activeRows ℓ E).eval (entryOracle M) ↔
        (t.1, some t.2.1, some t.2.2) ∈ E ∧ M t.1 t.2.1 = ℓ) ∧
      (activeRows ℓ E).cost (entryOracle M) ≤ E.length
  | [] => by simp [activeRows]
  | (i, some l, some r) :: rest => by
      obtain ⟨h1, h2⟩ := activeRows_spec ℓ rest
      simp only [activeRows, eval_bind, eval_ask, eval_map, cost_bind, cost_ask, cost_map,
        List.length_cons, entryOracle]
      refine ⟨fun t => ?_, by omega⟩
      by_cases hx : M i l = ℓ
      · simp only [hx, ite_true, List.mem_cons, h1]
        constructor
        · rintro (rfl | ⟨hm, hv⟩)
          · exact ⟨Or.inl rfl, hx⟩
          · exact ⟨Or.inr hm, hv⟩
        · rintro ⟨hm | hm, hv⟩
          · simp only [Prod.mk.injEq, Option.some.injEq] at hm
            obtain ⟨h1, h2, h3⟩ := hm
            exact Or.inl (Prod.ext h1 (Prod.ext h2 h3))
          · exact Or.inr ⟨hm, hv⟩
      · simp only [hx, ite_false, List.mem_cons, h1]
        constructor
        · rintro ⟨hm, hv⟩; exact ⟨Or.inr hm, hv⟩
        · rintro ⟨hm | hm, hv⟩
          · simp only [Prod.mk.injEq, Option.some.injEq] at hm
            obtain ⟨rfl, rfl, -⟩ := hm
            exact absurd hv hx
          · exact ⟨hm, hv⟩
  | (i, none, o) :: rest => by
      obtain ⟨h1, h2⟩ := activeRows_spec ℓ rest
      simp only [activeRows, List.length_cons, List.mem_cons]
      refine ⟨fun t => ?_, by omega⟩
      rw [h1]
      simp
  | (i, some l, none) :: rest => by
      obtain ⟨h1, h2⟩ := activeRows_spec ℓ rest
      simp only [activeRows, List.length_cons, List.mem_cons]
      refine ⟨fun t => ?_, by omega⟩
      rw [h1]
      simp

omit [LinearOrder ι] [LinearOrder κ] in
theorem colReport_cost (ℓ : ℝ) (j : κ) (o : ι × κ → ℝ) :
    ∀ F : List (ι × κ × κ), (colReport ℓ j F).cost o ≤ 1
  | [] => by simp [colReport]
  | t :: A => by simp [colReport]

omit [LinearOrder ι] [LinearOrder κ] in
/-- If all listed rows have the same entry at `j`, one query decides them all. -/
theorem colReport_spec (ℓ : ℝ) (j : κ) {F : List (ι × κ × κ)}
    (hEq : ∀ t ∈ F, ∀ t' ∈ F, M t.1 j = M t'.1 j) (p : ι × κ) :
    p ∈ (colReport ℓ j F).eval (entryOracle M) ↔
      p.2 = j ∧ (∃ t ∈ F, t.1 = p.1) ∧ M p.1 j = ℓ := by
  cases F with
  | nil => simp [colReport]
  | cons t A =>
      simp only [colReport, eval_map, eval_ask, entryOracle]
      by_cases hx : M t.1 j = ℓ
      · simp only [hx, ite_true, List.mem_map]
        constructor
        · rintro ⟨t', ht', rfl⟩
          exact ⟨rfl, ⟨t', ht', rfl⟩, (hEq t' ht' t (by simp)).trans hx⟩
        · rintro ⟨h2, ⟨t', ht', h1⟩, -⟩
          exact ⟨t', ht', Prod.ext h1 h2.symm⟩
      · simp only [hx, ite_false, List.not_mem_nil, false_iff, not_and]
        rintro - ⟨t', ht', h1⟩ hv
        exact hx ((hEq t (by simp) t' ht').trans (h1 ▸ hv))

omit [LinearOrder ι] in
theorem mem_enclosing {act : List (ι × κ × κ)} {j : κ} {t : ι × κ × κ} :
    t ∈ enclosing act j ↔ t ∈ act ∧ t.2.1 ≤ j ∧ j ≤ t.2.2 := by
  simp [enclosing]

omit [LinearOrder ι] [LinearOrder κ] in
/-- Two `Forall₂` relations on the same left list combine over the zipped right lists. -/
theorem forall₂_zip_and {α β γ : Type} {P : α → β → Prop} {Q : α → γ → Prop} :
    ∀ {l : List α} {l₁ : List β} {l₂ : List γ}, List.Forall₂ P l l₁ → List.Forall₂ Q l l₂ →
      List.Forall₂ (fun a b => P a b.1 ∧ Q a b.2) l (l₁.zip l₂)
  | _, _, _, List.Forall₂.nil, List.Forall₂.nil => List.Forall₂.nil
  | _, _, _, List.Forall₂.cons h t, List.Forall₂.cons h' t' =>
      List.Forall₂.cons ⟨h, h'⟩ (forall₂_zip_and t t')

/-- Both SMAWK runs, as one relation between the rows and their extreme minima. -/
theorem extremeMinima_spec {rows : List ι} {cols : List κ} (hR : rows.Pairwise (· < ·))
    (hC : cols.Pairwise (· < ·)) (hCne : cols ≠ []) (hM : IsMonge M rows cols) :
    List.Forall₂ (fun i p => GoodMin M cols i p.1 ∧
        ∃ j, p.2 = some j ∧ IsRightmostMin M i cols j) rows
      (((smawk rows cols).eval (entryOracle M)).zip
        ((((smawk (rows.reverse.map OrderDual.toDual) (cols.reverse.map OrderDual.toDual)).mapQ
          fun p => (OrderDual.ofDual p.1, OrderDual.ofDual p.2)).eval (entryOracle M)).reverse.map
            (Option.map OrderDual.ofDual))) ∧
      (smawk rows cols).cost (entryOracle M) ≤ 4 * cols.length + 12 * rows.length ∧
      ((smawk (rows.reverse.map OrderDual.toDual) (cols.reverse.map OrderDual.toDual)).mapQ
          (fun p => (OrderDual.ofDual p.1, OrderDual.ofDual p.2))).cost (entryOracle M) ≤
        4 * cols.length + 12 * rows.length := by
  obtain ⟨hL, hLc⟩ := smawk_spec rows.length rows cols le_rfl hR hC hCne hM.totallyMonotone
  have horacle : (entryOracle M ∘ fun p : ιᵒᵈ × κᵒᵈ =>
      (OrderDual.ofDual p.1, OrderDual.ofDual p.2)) = entryOracle (dualM M) := rfl
  have hCne' : cols.reverse.map OrderDual.toDual ≠ [] := by simpa using hCne
  obtain ⟨hD, hDc⟩ := smawk_spec (M := dualM M) (rows.reverse.map OrderDual.toDual).length _ _
    le_rfl (pairwise_reverse_map_toDual hR) (pairwise_reverse_map_toDual hC) hCne'
    hM.dual.totallyMonotone
  simp only [eval_mapQ, cost_mapQ, horacle]
  simp only [List.length_map, List.length_reverse] at hDc
  refine ⟨forall₂_zip_and (Q := fun i o => ∃ j, o = some j ∧ IsRightmostMin M i cols j) hL ?_,
    hLc, hDc⟩
  rw [List.forall₂_map_right_iff]
  rw [List.forall₂_map_left_iff] at hD
  rw [← List.forall₂_reverse_iff, List.reverse_reverse]
  refine hD.imp fun i o ⟨j, ho, hj⟩ => ⟨OrderDual.ofDual j, by rw [ho]; rfl, ?_⟩
  exact isLeftmostMin_dual_iff.mp hj

/-! ### Cost and correctness -/

/-- **Cost of `allMinima`**: at most `9 * cols.length + 25 * rows.length` entry evaluations
on every Monge matrix over sorted lists, whatever the level and the number of reported pairs. -/
theorem allMinima_cost {rows : List ι} {cols : List κ} (hR : rows.Pairwise (· < ·))
    (hC : cols.Pairwise (· < ·)) (hM : IsMonge M rows cols) (ℓ : ℝ) :
    (allMinima rows cols ℓ).cost (entryOracle M) ≤ 9 * cols.length + 25 * rows.length := by
  unfold allMinima
  by_cases hempty : rows = [] ∨ cols = []
  · rw [ite_eq_left hempty]; simp
  rw [ite_eq_right hempty]
  push Not at hempty
  obtain ⟨-, hc1, hc2⟩ := extremeMinima_spec hR hC hempty.2 hM
  simp only [cost_bind, cost_map]
  set E := rows.zip (((smawk rows cols).eval (entryOracle M)).zip
    ((((smawk (rows.reverse.map OrderDual.toDual) (cols.reverse.map OrderDual.toDual)).mapQ
      fun p => (OrderDual.ofDual p.1, OrderDual.ofDual p.2)).eval (entryOracle M)).reverse.map
        (Option.map OrderDual.ofDual)))
  have hE : E.length ≤ rows.length := by simp [E, List.length_zip]
  have h3 := (activeRows_spec (M := M) ℓ E).2
  have h4 := cost_mapList_le (entryOracle M)
    (colStep ((activeRows ℓ E).eval (entryOracle M)) ℓ) cols (c := 1)
    fun j _ => colReport_cost ℓ j _ _
  omega

/-- **All minimum entries of a Monge matrix.** For sorted row and column lists, a Monge matrix
and a level `ℓ` below every entry of the rectangle, the output contains exactly the pairs of
the rectangle whose entry is `ℓ`, with at most `9 * cols.length + 25 * rows.length`
evaluations. -/
theorem allMinima_spec {rows : List ι} {cols : List κ} {ℓ : ℝ}
    (hR : rows.Pairwise (· < ·)) (hC : cols.Pairwise (· < ·)) (hM : IsMonge M rows cols)
    (hlow : ∀ i ∈ rows, ∀ j ∈ cols, ℓ ≤ M i j) :
    (∀ p, p ∈ (allMinima rows cols ℓ).eval (entryOracle M) ↔
        p.1 ∈ rows ∧ p.2 ∈ cols ∧ M p.1 p.2 = ℓ) ∧
      (allMinima rows cols ℓ).cost (entryOracle M) ≤ 9 * cols.length + 25 * rows.length := by
  refine ⟨fun p => ?_, allMinima_cost hR hC hM ℓ⟩
  unfold allMinima
  by_cases hempty : rows = [] ∨ cols = []
  · rw [ite_eq_left hempty]
    rcases hempty with h | h <;> simp [h]
  rw [ite_eq_right hempty]
  push Not at hempty
  obtain ⟨hext, -, -⟩ := extremeMinima_spec hR hC hempty.2 hM
  simp only [eval_bind, eval_map, eval_mapList]
  set E := rows.zip (((smawk rows cols).eval (entryOracle M)).zip
    ((((smawk (rows.reverse.map OrderDual.toDual) (cols.reverse.map OrderDual.toDual)).mapQ
      fun p => (OrderDual.ofDual p.1, OrderDual.ofDual p.2)).eval (entryOracle M)).reverse.map
        (Option.map OrderDual.ofDual))) with hEdef
  set act := (activeRows ℓ E).eval (entryOracle M)
  have hact := (activeRows_spec (M := M) ℓ E).1
  -- every active triple is a row with its two extreme minima, of value `ℓ`
  have hA1 : ∀ t ∈ act, t.1 ∈ rows ∧ IsLeftmostMin M t.1 cols t.2.1 ∧
      IsRightmostMin M t.1 cols t.2.2 ∧ M t.1 t.2.1 = ℓ := by
    intro t ht
    obtain ⟨hmem, hv⟩ := (hact t).mp ht
    obtain ⟨hr, ⟨j, hj, hlm⟩, ⟨j', hj', hrm⟩⟩ := mem_zip_of_forall₂ hext _ hmem
    simp only [Option.some.injEq] at hj hj'
    exact ⟨hr, hj ▸ hlm, hj' ▸ hrm, hv⟩
  -- the extreme minima of an active row both have value `ℓ`
  have hright : ∀ t ∈ act, M t.1 t.2.2 = ℓ := by
    intro t ht
    obtain ⟨-, hl, hr, hv⟩ := hA1 t ht
    exact le_antisymm (hv ▸ hr.2.1 _ hl.1) (hv ▸ hl.2.1 _ hr.1)
  -- active rows enclosing a column agree there
  have hEq : ∀ j ∈ cols, ∀ t ∈ enclosing act j, ∀ t' ∈ enclosing act j,
      M t.1 j = M t'.1 j := by
    intro j hj t ht t' ht'
    obtain ⟨ht, htl, htr⟩ := mem_enclosing.mp ht
    obtain ⟨ht', htl', htr'⟩ := mem_enclosing.mp ht'
    obtain ⟨hti, htL, htR, htv⟩ := hA1 t ht
    obtain ⟨hti', htL', htR', htv'⟩ := hA1 t' ht'
    rcases lt_trichotomy t.1 t'.1 with hlt | heq | hgt
    · exact monge_equal_between_opposite_minima hM hlow hti hti' hlt htL'.1 hj htR.1 htl' htr
        (hright t ht) htv'
    · rw [heq]
    · exact (monge_equal_between_opposite_minima hM hlow hti' hti hgt htL.1 hj htR'.1 htl htr'
        (hright t' ht') htv).symm
  rw [List.mem_flatten]
  constructor
  · rintro ⟨l, hl, hpl⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hl
    obtain ⟨h2, ⟨t, ht, h1⟩, hv⟩ := (colReport_spec ℓ j (hEq j hj) p).mp hpl
    obtain ⟨hti, -⟩ := hA1 t (mem_enclosing.mp ht).1
    exact ⟨h1 ▸ hti, h2 ▸ hj, h2 ▸ hv⟩
  · rintro ⟨hi, hj, hv⟩
    refine ⟨_, List.mem_map.mpr ⟨p.2, hj, rfl⟩, (colReport_spec ℓ p.2 (hEq p.2 hj) p).mpr
      ⟨rfl, ?_, hv⟩⟩
    -- the row of `p` is active, and its extreme minima enclose `p.2`
    obtain ⟨y, hy⟩ := exists_mem_zip_of_forall₂ hext p.1 hi
    obtain ⟨-, ⟨l, hl, hlm⟩, ⟨r, hr, hrm⟩⟩ := mem_zip_of_forall₂ hext _ hy
    have hlv : M p.1 l = ℓ := le_antisymm (hv ▸ hlm.2.1 _ hj) (hlow _ hi _ hlm.1)
    have hmem : (p.1, l, r) ∈ act := by
      refine (hact _).mpr ⟨?_, hlv⟩
      have hy' : y = (some l, some r) := Prod.ext hl hr
      rw [hy'] at hy
      exact hy
    refine ⟨(p.1, l, r), mem_enclosing.mpr ⟨hmem, ?_, ?_⟩, rfl⟩
    · by_contra hlt
      push Not at hlt
      have := hlm.2.2 _ hj hlt
      have := hlow _ hi _ hlm.1
      linarith
    · by_contra hlt
      push Not at hlt
      have := hrm.2.2 _ hj hlt
      have := hlow _ hi _ hrm.1
      have hrv : M p.1 r = ℓ := le_antisymm (hv ▸ hrm.2.1 _ hj) (hlow _ hi _ hrm.1)
      linarith

/-- **Query bound for all minimum entries of a Monge matrix.** For fixed sorted row and column
lists and a fixed level `ℓ`, one decision tree over entry queries, with budget
`9 * cols.length + 25 * rows.length`, returns exactly the pairs of value `ℓ` of every Monge
matrix whose entries are at least `ℓ`. -/
theorem monge_allMinima_queryBound (rows : List ι) (cols : List κ) (hR : rows.Pairwise (· < ·))
    (hC : cols.Pairwise (· < ·)) (ℓ : ℝ) :
    ∃ T : DTree (ι × κ) ℝ (Option (List (ι × κ))) (9 * cols.length + 25 * rows.length),
      ∀ M : ι → κ → ℝ, IsMonge M rows cols → (∀ i ∈ rows, ∀ j ∈ cols, ℓ ≤ M i j) →
        ∃ out, T.eval (entryOracle M) = some out ∧
          ∀ p, p ∈ out ↔ p.1 ∈ rows ∧ p.2 ∈ cols ∧ M p.1 p.2 = ℓ := by
  refine ⟨(allMinima rows cols ℓ).toDTree _, fun M hM hlow => ?_⟩
  obtain ⟨hmem, hcost⟩ := allMinima_spec hR hC hM hlow
  exact ⟨_, Comp.toDTree_eval _ _ hcost, hmem⟩

end Search
end CutQueryComplexity
