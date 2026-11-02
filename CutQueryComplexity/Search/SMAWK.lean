import CutQueryComplexity.Search.Comp
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Order.Basic
import Mathlib.Data.Finset.Max

/-! # SMAWK row-minima search with a linear number of entry evaluations

Aggarwal, Klawe, Moran, Shor, and Wilber's algorithm finds the leftmost
minimum of every row of a totally monotone matrix. Rows and columns are given
as strictly increasing lists of indices, so every recursive call works on
subsequences. The only oracle is entry evaluation; comparisons and index
bookkeeping are free.

The main theorem `smawk_spec` proves that `smawk R C` returns the leftmost row
minima of every row, with at most `4 * C.length + 12 * R.length` evaluations.
`matrixMin_spec` finds a minimum entry with at most `4 * C.length +
13 * R.length` evaluations, and `IsMonge.totallyMonotone` supplies the
hypothesis for Monge matrices.
-/

namespace CutQueryComplexity
namespace Search

open Comp

variable {ι κ α : Type} [LinearOrder ι] [LinearOrder κ] [LinearOrder α]

/-- Total monotonicity on the given rows and columns: a strict preference for the
right column persists in every later row. -/
def TotallyMonotone (M : ι → κ → α) (R : List ι) (C : List κ) : Prop :=
  ∀ r ∈ R, ∀ r' ∈ R, ∀ c ∈ C, ∀ c' ∈ C,
    r < r' → c < c' → M r c' < M r c → M r' c' < M r' c

/-- `j` is the leftmost minimum of row `r` among the columns `L`. -/
def IsLeftmostMin (M : ι → κ → α) (r : ι) (L : List κ) (j : κ) : Prop :=
  j ∈ L ∧ (∀ j' ∈ L, M r j ≤ M r j') ∧ ∀ j' ∈ L, j' < j → M r j < M r j'

/-- The entry oracle of a matrix. -/
def entryOracle (M : ι → κ → α) : ι × κ → α := fun p => M p.1 p.2

section Order

variable {M : ι → κ → α}

theorem TotallyMonotone.mono {R R' : List ι} {C C' : List κ}
    (h : TotallyMonotone M R C) (hR : ∀ r ∈ R', r ∈ R) (hC : ∀ c ∈ C', c ∈ C) :
    TotallyMonotone M R' C' := fun r hr r' hr' c hc c' hc' =>
  h r (hR r hr) r' (hR r' hr') c (hC c hc) c' (hC c' hc')

/-- The non-strict form used by REDUCE: a weak preference for the left column
propagates to every earlier row. -/
theorem TotallyMonotone.le_of_le {R : List ι} {C : List κ} (h : TotallyMonotone M R C)
    {r r' : ι} (hr : r ∈ R) (hr' : r' ∈ R) {c c' : κ} (hc : c ∈ C) (hc' : c' ∈ C)
    (hrr : r ≤ r') (hcc : c < c') (hle : M r' c ≤ M r' c') : M r c ≤ M r c' := by
  rcases hrr.lt_or_eq with hlt | rfl
  · by_contra hne
    exact absurd (h r hr r' hr' c hc c' hc' hlt hcc (lt_of_not_ge hne)) (not_lt.mpr hle)
  · exact hle

/-- A strict preference for the right column propagates to every later row. -/
theorem TotallyMonotone.lt_of_lt {R : List ι} {C : List κ} (h : TotallyMonotone M R C)
    {r r' : ι} (hr : r ∈ R) (hr' : r' ∈ R) {c c' : κ} (hc : c ∈ C) (hc' : c' ∈ C)
    (hrr : r ≤ r') (hcc : c < c') (hlt : M r c' < M r c) : M r' c' < M r' c := by
  rcases hrr.lt_or_eq with hrr | rfl
  · exact h r hr r' hr' c hc c' hc' hrr hcc hlt
  · exact hlt

omit [LinearOrder ι] in
theorem IsLeftmostMin.unique {r : ι} {L : List κ} {j j' : κ}
    (h : IsLeftmostMin M r L j) (h' : IsLeftmostMin M r L j') : j = j' := by
  rcases lt_trichotomy j j' with hlt | heq | hgt
  · exact absurd (h.2.1 j' h'.1) (not_le.mpr (h'.2.2 j h.1 hlt))
  · exact heq
  · exact absurd (h'.2.1 j h.1) (not_le.mpr (h.2.2 j' h'.1 hgt))

omit [LinearOrder ι] in
/-- A leftmost minimum stays one after discarding other columns. -/
theorem IsLeftmostMin.of_subset {r : ι} {L L' : List κ} {j : κ}
    (h : IsLeftmostMin M r L j) (hsub : ∀ c ∈ L', c ∈ L) (hj : j ∈ L') :
    IsLeftmostMin M r L' j :=
  ⟨hj, fun j' hj' => h.2.1 j' (hsub j' hj'), fun j' hj' hlt => h.2.2 j' (hsub j' hj') hlt⟩

omit [LinearOrder ι] in
/-- A column with a weakly smaller entry to its left is not a leftmost minimum. -/
theorem not_isLeftmostMin_of_left {r : ι} {L : List κ} {c c' : κ}
    (hc' : c' ∈ L) (hlt : c' < c) (hle : M r c' ≤ M r c) : ¬ IsLeftmostMin M r L c :=
  fun h => absurd hle (not_le.mpr (h.2.2 c' hc' hlt))

omit [LinearOrder ι] in
/-- A column with a strictly smaller entry is not a minimum. -/
theorem not_isLeftmostMin_of_lt {r : ι} {L : List κ} {c c' : κ}
    (hc' : c' ∈ L) (hlt : M r c' < M r c) : ¬ IsLeftmostMin M r L c :=
  fun h => absurd (h.2.1 c' hc') (not_le.mpr hlt)

omit [LinearOrder ι] in
theorem exists_isLeftmostMin (r : ι) {L : List κ} (hL : L ≠ []) :
    ∃ j, IsLeftmostMin M r L j := by
  classical
  obtain ⟨m₀, hm₀⟩ := L.exists_mem_of_ne_nil hL
  have hne : (L.toFinset.image (M r)).Nonempty :=
    ⟨M r m₀, Finset.mem_image.mpr ⟨m₀, List.mem_toFinset.mpr hm₀, rfl⟩⟩
  have hv := (L.toFinset.image (M r)).min'_mem hne
  rw [Finset.mem_image] at hv
  obtain ⟨m, hm, hval⟩ := hv
  rw [List.mem_toFinset] at hm
  have hmin : ∀ x ∈ L, M r m ≤ M r x := by
    intro x hx
    rw [hval]
    exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨x, List.mem_toFinset.mpr hx, rfl⟩)
  let T := L.toFinset.filter fun x => M r x ≤ M r m
  have hT : T.Nonempty := ⟨m, by simp [T, hm]⟩
  have hjT := T.min'_mem hT
  simp only [T, Finset.mem_filter, List.mem_toFinset] at hjT
  refine ⟨T.min' hT, hjT.1, fun x hx => le_trans hjT.2 (hmin x hx), fun x hx hlt => ?_⟩
  by_contra hge
  have hxT : x ∈ T := by
    simp only [T, Finset.mem_filter, List.mem_toFinset]
    exact ⟨hx, le_trans (not_lt.mp hge) hjT.2⟩
  exact absurd (T.min'_le x hxT) (not_le.mpr hlt)

/-- Leftmost row minima move weakly to the right in later rows. -/
theorem TotallyMonotone.leftmost_mono {R : List ι} {C : List κ} (h : TotallyMonotone M R C)
    {r r' : ι} (hr : r ∈ R) (hr' : r' ∈ R) (hrr : r < r') {j j' : κ}
    (hj : IsLeftmostMin M r C j) (hj' : IsLeftmostMin M r' C j') : j ≤ j' := by
  by_contra hlt
  have hlt := lt_of_not_ge hlt
  have := h r hr r' hr' j' hj'.1 j hj.1 hrr hlt (hj.2.2 j' hj'.1 hlt)
  exact absurd (hj'.2.1 j hj.1) (not_le.mpr this)

end Order

/-! ### Monge matrices -/

/-- The Monge inequality on the given rows and columns, oriented for minima. -/
def IsMonge {β : Type} [AddCommGroup β] [LinearOrder β] (M : ι → κ → β)
    (R : List ι) (C : List κ) : Prop :=
  ∀ r ∈ R, ∀ r' ∈ R, ∀ c ∈ C, ∀ c' ∈ C, r < r' → c < c' →
    M r c + M r' c' ≤ M r c' + M r' c

theorem IsMonge.totallyMonotone {β : Type} [AddCommGroup β] [LinearOrder β]
    [IsOrderedAddMonoid β] {M : ι → κ → β} {R : List ι} {C : List κ}
    (h : IsMonge M R C) : TotallyMonotone M R C := by
  intro r hr r' hr' c hc c' hc' hrr hcc hlt
  have hm := h r hr r' hr' c hc c' hc' hrr hcc
  by_contra hge
  have := add_lt_add_of_lt_of_le hlt (not_lt.mp hge)
  exact absurd hm (not_le.mpr this)

/-! ### Sorted-list helpers -/

section Lists

/-- Every second element, starting with the second. -/
def odds {β : Type} : List β → List β
  | _ :: b :: t => b :: odds t
  | _ => []

theorem odds_sublist {β : Type} : ∀ l : List β, (odds l).Sublist l
  | [] => List.Sublist.slnil
  | [_] => List.nil_sublist _
  | _ :: b :: t => ((odds_sublist t).cons_cons b).cons _

theorem length_odds {β : Type} : ∀ l : List β, (odds l).length = l.length / 2
  | [] => by simp [odds]
  | [_] => by simp [odds]
  | _ :: _ :: t => by simp [odds, length_odds t]; omega

variable {β : Type} [LinearOrder β]

theorem mem_takeWhile_le {l : List β} (hl : l.Pairwise (· < ·)) {j c : β} :
    c ∈ l.takeWhile (fun x => decide (x ≤ j)) ↔ c ∈ l ∧ c ≤ j := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [List.pairwise_cons] at hl
      by_cases hx : x ≤ j
      · have e : (x :: xs).takeWhile (fun x => decide (x ≤ j)) =
            x :: xs.takeWhile (fun x => decide (x ≤ j)) := by simp [hx]
        rw [e, List.mem_cons, ih hl.2, List.mem_cons]
        constructor
        · rintro (rfl | h)
          · exact ⟨Or.inl rfl, hx⟩
          · exact ⟨Or.inr h.1, h.2⟩
        · rintro ⟨rfl | h, hc⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨h, hc⟩
      · have e : (x :: xs).takeWhile (fun x => decide (x ≤ j)) = [] := by
          simp [hx]
        rw [e, List.mem_cons]
        simp only [List.not_mem_nil, false_iff, not_and]
        rintro (rfl | h) hc
        · exact hx hc
        · exact hx (le_trans (le_of_lt (hl.1 c h)) hc)

theorem mem_dropWhile_lt {l : List β} (hl : l.Pairwise (· < ·)) {j c : β} :
    c ∈ l.dropWhile (fun x => decide (x < j)) ↔ c ∈ l ∧ j ≤ c := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [List.pairwise_cons] at hl
      by_cases hx : x < j
      · have e : (x :: xs).dropWhile (fun x => decide (x < j)) =
            xs.dropWhile (fun x => decide (x < j)) := by simp [hx]
        rw [e, ih hl.2, List.mem_cons]
        constructor
        · rintro ⟨h, hc⟩
          exact ⟨Or.inr h, hc⟩
        · rintro ⟨rfl | h, hc⟩
          · exact absurd hx (not_lt.mpr hc)
          · exact ⟨h, hc⟩
      · have e : (x :: xs).dropWhile (fun x => decide (x < j)) = x :: xs := by
          simp [hx]
        rw [e, List.mem_cons]
        constructor
        · rintro (rfl | h)
          · exact ⟨Or.inl rfl, not_lt.mp hx⟩
          · exact ⟨Or.inr h, le_trans (not_lt.mp hx) (le_of_lt (hl.1 c h))⟩
        · rintro ⟨h, -⟩
          exact h

/-- The window up to `j` and the suffix from `j` overlap in at most one element. -/
theorem length_takeWhile_le_add {l : List β} (hl : l.Pairwise (· < ·)) (j : β) :
    (l.takeWhile (fun x => decide (x ≤ j))).length +
      (l.dropWhile (fun x => decide (x < j))).length ≤ l.length + 1 := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [List.pairwise_cons] at hl
      by_cases hxlt : x < j
      · have e1 : (x :: xs).takeWhile (fun x => decide (x ≤ j)) =
            x :: xs.takeWhile (fun x => decide (x ≤ j)) := by
          simp [le_of_lt hxlt]
        have e2 : (x :: xs).dropWhile (fun x => decide (x < j)) =
            xs.dropWhile (fun x => decide (x < j)) := by simp [hxlt]
        rw [e1, e2, List.length_cons, List.length_cons]
        have := ih hl.2
        omega
      · have e2 : (x :: xs).dropWhile (fun x => decide (x < j)) = x :: xs := by
          simp [hxlt]
        rw [e2]
        by_cases hxle : x ≤ j
        · have hxj : x = j := le_antisymm hxle (not_lt.mp hxlt)
          have hnil : xs.takeWhile (fun y => decide (y ≤ j)) = [] := by
            cases xs with
            | nil => rfl
            | cons y ys =>
                have : j < y := hxj ▸ hl.1 y (by simp)
                simp [not_le.mpr this]
          have e1 : (x :: xs).takeWhile (fun x => decide (x ≤ j)) = [x] := by
            simp [hxle, hnil]
          rw [e1]
          simp only [List.length_cons, List.length_nil]
          omega
        · have e1 : (x :: xs).takeWhile (fun x => decide (x ≤ j)) = [] := by
            simp [hxle]
          rw [e1]
          simp only [List.length_cons, List.length_nil]
          omega

end Lists

/-! ### REDUCE -/

section Reduce

/-- Insert column `c` into the REDUCE stack. The stack is listed top first and
each entry carries the row it is compared on; `rl` holds the unused rows. -/
def insertCol (c : κ) : List (κ × ι) → List ι → Comp (ι × κ) α (List (κ × ι) × List ι)
  | [], [] => Comp.pure ([], [])
  | [], r :: rl => Comp.pure ([(c, r)], rl)
  | (t, r) :: st, rl =>
      (ask (r, t)).bind fun x => (ask (r, c)).bind fun y =>
        if y < x then insertCol c st (r :: rl)
        else match rl with
          | [] => Comp.pure ((t, r) :: st, [])
          | r' :: rl' => Comp.pure ((c, r') :: (t, r) :: st, rl')

/-- Process the remaining columns in order. -/
def reduceAux : List (κ × ι) → List ι → List κ →
    Comp (ι × κ) α (List (κ × ι) × List ι)
  | st, rl, [] => Comp.pure (st, rl)
  | st, rl, c :: cs => (insertCol c st rl).bind fun p => reduceAux p.1 p.2 cs

/-- REDUCE: at most one column per row survives, including every leftmost row
minimum. The surviving columns are returned in increasing order. -/
def reduce (R : List ι) (C : List κ) : Comp (ι × κ) α (List κ) :=
  (reduceAux [] R C).map fun p => p.1.reverse.map Prod.fst

variable (M : ι → κ → α)

/-- Adjacent stack entries: every row up to the lower entry's row weakly prefers
the lower column. -/
def StackAdj (R : List ι) : List (κ × ι) → Prop
  | (t, _) :: (t', r') :: rest =>
      (∀ ρ ∈ R, ρ ≤ r' → M ρ t' ≤ M ρ t) ∧ StackAdj R ((t', r') :: rest)
  | _ => True

/-- The REDUCE invariant after processing the columns `P`. -/
structure ReduceInv (R : List ι) (C P : List κ) (st : List (κ × ι)) (rl : List ι) :
    Prop where
  rows : st.reverse.map Prod.snd ++ rl = R
  sub : (st.reverse.map Prod.fst).Sublist P
  adj : StackAdj M R st
  discard : ∀ c ∈ P, c ∉ st.map Prod.fst → ∀ ρ ∈ R, ¬ IsLeftmostMin M ρ C c

variable {M}

theorem lt_of_mem_prefix {X Y : List ι} {r ρ : ι} (hR : (X ++ r :: Y).Pairwise (· < ·))
    (hρ : ρ ∈ X) : ρ < r := by
  rw [List.pairwise_append] at hR
  exact hR.2.2 ρ hρ r (by simp)

theorem mem_prefix_of_lt {X Y : List ι} {r ρ : ι} (hR : (X ++ r :: Y).Pairwise (· < ·))
    (hρ : ρ ∈ X ++ r :: Y) (hlt : ρ < r) : ρ ∈ X := by
  rw [List.pairwise_append, List.pairwise_cons] at hR
  rcases List.mem_append.mp hρ with h | h
  · exact h
  · rcases List.mem_cons.mp h with rfl | h
    · exact absurd hlt (lt_irrefl _)
    · exact absurd (hR.2.1.1 ρ h) (not_lt.mpr (le_of_lt hlt))

theorem insertCol_spec {R : List ι} {C P : List κ} (hR : R.Pairwise (· < ·))
    (hTM : TotallyMonotone M R C) (hPC : ∀ p ∈ P, p ∈ C) (hP : P.Pairwise (· < ·))
    {c : κ} (hc : c ∈ C) (hPc : ∀ p ∈ P, p < c) :
    ∀ (st : List (κ × ι)) (rl : List ι), ReduceInv M R C P st rl →
      ReduceInv M R C (P ++ [c]) ((insertCol c st rl).eval (entryOracle M)).1
          ((insertCol c st rl).eval (entryOracle M)).2 ∧
        (insertCol c st rl).cost (entryOracle M) +
            2 * ((insertCol c st rl).eval (entryOracle M)).1.length ≤
          2 * st.length + 4
  | [], [], h => by
      have hR0 : R = [] := by simpa using h.rows.symm
      simp only [insertCol, eval_pure, cost_pure]
      refine ⟨⟨by simp [hR0], by simp, trivial, ?_⟩, by simp⟩
      intro c' _ _ ρ hρ
      simp [hR0] at hρ
  | [], r :: rl, h => by
      simp only [insertCol, eval_pure, cost_pure]
      refine ⟨⟨by simpa using h.rows, by simp, trivial, ?_⟩, by simp⟩
      intro c' hc' hnot ρ hρ
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hnot
      rcases List.mem_append.mp hc' with hc' | hc'
      · exact h.discard c' hc' (by simp) ρ hρ
      · exact absurd (List.mem_singleton.mp hc') hnot
  | (t, r) :: st, rl, h => by
      have hrows := h.rows
      simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.singleton_append] at hrows
      have hRsplit : (st.reverse.map Prod.snd ++ r :: rl).Pairwise (· < ·) := hrows ▸ hR
      have hrR : r ∈ R := hrows ▸ by simp
      have hsubP : (st.reverse.map Prod.fst ++ [t]).Sublist P := by
        simpa using h.sub
      have htP : t ∈ P := hsubP.subset (by simp)
      have htC : t ∈ C := hPC t htP
      have htc : t < c := hPc t htP
      simp only [insertCol, eval_bind, cost_bind, eval_ask, cost_ask, entryOracle]
      by_cases hyx : M r c < M r t
      · -- Pop the top entry: `t` is no leftmost minimum of any row.
        simp only [hyx, ite_true]
        have htdead : ∀ ρ ∈ R, ¬ IsLeftmostMin M ρ C t := by
          intro ρ hρ
          by_cases hrρ : r ≤ ρ
          · exact not_isLeftmostMin_of_lt hc (hTM.lt_of_lt hrR hρ htC hc hrρ htc hyx)
          · have hρX := mem_prefix_of_lt hRsplit (hrows ▸ hρ) (lt_of_not_ge hrρ)
            cases st with
            | nil => simp at hρX
            | cons e st2 =>
                obtain ⟨t', r'⟩ := e
                have hρr' : ρ ≤ r' := by
                  simp only [List.reverse_cons, List.map_append, List.map_cons,
                    List.map_nil] at hρX
                  rcases List.mem_append.mp hρX with h2 | h2
                  · have hR2 := hRsplit
                    simp only [List.reverse_cons, List.map_append, List.map_cons,
                      List.map_nil, List.append_assoc, List.singleton_append] at hR2
                    exact le_of_lt (lt_of_mem_prefix hR2 h2)
                  · exact le_of_eq (List.mem_singleton.mp h2)
                have hsorted := hP.sublist hsubP
                simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
                  List.append_assoc, List.singleton_append, List.pairwise_append,
                  List.pairwise_cons] at hsorted
                have ht't : t' < t := hsorted.2.1.1 t (by simp)
                have ht'C : t' ∈ C := hPC t' (hsubP.subset (by simp))
                exact not_isLeftmostMin_of_left ht'C ht't (h.adj.1 ρ hρ hρr')
        have hinv : ReduceInv M R C P st (r :: rl) := by
          refine ⟨?_, ?_, ?_, ?_⟩
          · simpa using hrows
          · exact (List.sublist_append_left _ _).trans hsubP
          · cases st with
            | nil => trivial
            | cons e st2 => exact h.adj.2
          · intro c' hc' hnot ρ hρ
            by_cases hct : c' = t
            · exact hct ▸ htdead ρ hρ
            · exact h.discard c' hc' (by simp [hct, hnot]) ρ hρ
        have ih := insertCol_spec hR hTM hPC hP hc hPc st (r :: rl) hinv
        refine ⟨ih.1, ?_⟩
        simp only [List.length_cons]
        omega
      · simp only [hyx, ite_false]
        have hle : M r t ≤ M r c := not_lt.mp hyx
        cases rl with
        | nil =>
            -- The stack is full: `c` loses to `t` on every row.
            refine ⟨⟨h.rows, h.sub.trans (List.sublist_append_left _ _), h.adj, ?_⟩, ?_⟩
            · intro c' hc' hnot ρ hρ
              rcases List.mem_append.mp hc' with hc' | hc'
              · exact h.discard c' hc' hnot ρ hρ
              · rw [List.mem_singleton.mp hc']
                have hρr : ρ ≤ r := by
                  by_cases hρr : ρ < r
                  · exact le_of_lt hρr
                  · have : ρ ∈ st.reverse.map Prod.snd ++ [r] := hrows ▸ hρ
                    rcases List.mem_append.mp this with h2 | h2
                    · exact le_of_lt (lt_of_mem_prefix hRsplit h2)
                    · exact le_of_eq (List.mem_singleton.mp h2)
                exact not_isLeftmostMin_of_left htC htc
                  (hTM.le_of_le hρ hrR htC hc hρr htc hle)
            · simp only [eval_pure, cost_pure, List.length_cons]
              omega
        | cons r' rl' =>
            refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
            · simpa using hrows
            · simpa using hsubP.append (List.Sublist.refl [c])
            · exact ⟨fun ρ hρ hρr => hTM.le_of_le hρ hrR htC hc hρr htc hle, h.adj⟩
            · intro c' hc' hnot ρ hρ
              simp only [eval_pure, List.map_cons, List.mem_cons, not_or] at hnot
              rcases List.mem_append.mp hc' with hc' | hc'
              · exact h.discard c' hc' (by simp [hnot.2.1, hnot.2.2]) ρ hρ
              · exact absurd (List.mem_singleton.mp hc') hnot.1
            · simp only [eval_pure, cost_pure, List.length_cons]
              omega

theorem reduceAux_spec {R : List ι} {C : List κ} (hR : R.Pairwise (· < ·))
    (hC : C.Pairwise (· < ·)) (hTM : TotallyMonotone M R C) :
    ∀ (cs P : List κ) (st : List (κ × ι)) (rl : List ι), P ++ cs = C →
      ReduceInv M R C P st rl →
      ReduceInv M R C C ((reduceAux st rl cs).eval (entryOracle M)).1
          ((reduceAux st rl cs).eval (entryOracle M)).2 ∧
        (reduceAux st rl cs).cost (entryOracle M) +
            2 * ((reduceAux st rl cs).eval (entryOracle M)).1.length ≤
          2 * st.length + 4 * cs.length
  | [], P, st, rl, hPC, h => by
      simp only [List.append_nil] at hPC
      subst hPC
      exact ⟨h, by simp [reduceAux]⟩
  | c :: cs, P, st, rl, hPC, h => by
      have hC' := hC
      rw [← hPC, List.pairwise_append, List.pairwise_cons] at hC'
      have hins := insertCol_spec hR hTM (fun p hp => hPC ▸ List.mem_append_left _ hp)
        hC'.1 (hPC ▸ by simp) (fun p hp => hC'.2.2 p hp c (by simp)) st rl h
      have ih := reduceAux_spec hR hC hTM cs (P ++ [c]) _ _ (by simp [hPC]) hins.1
      simp only [reduceAux, eval_bind, cost_bind]
      refine ⟨ih.1, ?_⟩
      simp only [List.length_cons]
      have := hins.2
      omega

/-- REDUCE keeps a sorted subsequence of at most `R.length` columns, including every
leftmost row minimum, using at most `4 * C.length` evaluations. -/
theorem reduce_spec {R : List ι} {C : List κ} (hR : R.Pairwise (· < ·))
    (hC : C.Pairwise (· < ·)) (hTM : TotallyMonotone M R C) :
    ((reduce R C).eval (entryOracle M)).Sublist C ∧
      ((reduce R C).eval (entryOracle M)).length ≤ R.length ∧
      (∀ r ∈ R, ∀ j, IsLeftmostMin M r C j → j ∈ (reduce R C).eval (entryOracle M)) ∧
      (reduce R C).cost (entryOracle M) ≤ 4 * C.length := by
  have h0 : ReduceInv M R C [] [] R := ⟨by simp, by simp, trivial, by simp⟩
  have h := reduceAux_spec hR hC hTM C [] [] R (by simp) h0
  simp only [reduce, eval_map, cost_map]
  refine ⟨h.1.sub, ?_, ?_, ?_⟩
  · have := congrArg List.length h.1.rows
    simp only [List.length_append, List.length_map, List.length_reverse] at this
    simp only [List.length_map, List.length_reverse]
    omega
  · intro r hr j hj
    by_contra hnot
    exact h.1.discard j hj.1 (by simpa using hnot) r hr hj
  · have h2 := h.2
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add] at h2
    omega

end Reduce

/-- `Forall₂.imp` with access to membership of the left element. -/
theorem forall₂_imp_mem {β γ : Type} {P Q : β → γ → Prop} :
    ∀ {l : List β} {l' : List γ}, List.Forall₂ P l l' →
      (∀ x ∈ l, ∀ y, P x y → Q x y) → List.Forall₂ Q l l'
  | _, _, List.Forall₂.nil, _ => List.Forall₂.nil
  | _, _, List.Forall₂.cons h t, H =>
      List.Forall₂.cons (H _ (by simp) _ h)
        (forall₂_imp_mem t fun x hx y hxy => H x (by simp [hx]) y hxy)

/-! ### Scanning, INTERPOLATE, and the recursion -/

section Main

/-- Left-to-right scan keeping the first strict improvement. -/
def scanFrom (r : ι) : κ → α → List κ → Comp (ι × κ) α κ
  | j, _, [] => Comp.pure j
  | j, v, c :: cs => (ask (r, c)).bind fun x =>
      if x < v then scanFrom r c x cs else scanFrom r j v cs

/-- The leftmost minimum of row `r` over a sorted list, or `none` for no columns. -/
def scan (r : ι) : List κ → Comp (ι × κ) α (Option κ)
  | [] => Comp.pure none
  | c :: cs => (ask (r, c)).bind fun x => (scanFrom r c x cs).map some

/-- INTERPOLATE: given the leftmost minima of the odd-position rows, scan each
even-position row only between its neighbours' minima. `suf` is the suffix of
columns not yet excluded on the left. -/
def interp : List ι → List (Option κ) → List κ → Comp (ι × κ) α (List (Option κ))
  | [], _, _ => Comp.pure []
  | [r0], _, suf => (scan r0 suf).map fun o => [o]
  | r0 :: _ :: rest, some j1 :: os, suf =>
      (scan r0 (suf.takeWhile fun c => decide (c ≤ j1))).bind fun o0 =>
        (interp rest os (suf.dropWhile fun c => decide (c < j1))).map
          fun tl => o0 :: some j1 :: tl
  | _ :: _ :: _, _, _ => Comp.pure []

/-- SMAWK: REDUCE, recurse on the odd-position rows, then INTERPOLATE. -/
def smawk : List ι → List κ → Comp (ι × κ) α (List (Option κ))
  | [], _ => Comp.pure []
  | r :: rs, C => (reduce (r :: rs) C).bind fun C' =>
      (smawk (odds (r :: rs)) C').bind fun od => interp (r :: rs) od C'
termination_by R => R.length
decreasing_by simp only [length_odds, List.length_cons]; omega

variable {M : ι → κ → α}

omit [LinearOrder ι] in
theorem scanFrom_spec (r : ι) :
    ∀ (cs P : List κ) (j : κ), IsLeftmostMin M r P j → (P ++ cs).Pairwise (· < ·) →
      IsLeftmostMin M r (P ++ cs) ((scanFrom r j (M r j) cs).eval (entryOracle M)) ∧
        (scanFrom r j (M r j) cs).cost (entryOracle M) = cs.length
  | [], P, j, hj, _ => by simpa [scanFrom] using hj
  | c :: cs, P, j, hj, hsort => by
      have hsort' : ((P ++ [c]) ++ cs).Pairwise (· < ·) := by simpa using hsort
      have hPc : ∀ p ∈ P, p < c := by
        rw [List.pairwise_append] at hsort
        exact fun p hp => hsort.2.2 p hp c (by simp)
      have heq : P ++ c :: cs = (P ++ [c]) ++ cs := by simp
      simp only [scanFrom, eval_bind, cost_bind, eval_ask, cost_ask, entryOracle]
      by_cases hlt : M r c < M r j
      · simp only [hlt, ite_true]
        have hj' : IsLeftmostMin M r (P ++ [c]) c := by
          refine ⟨by simp, fun j' hj' => ?_, fun j' hj' hjc => ?_⟩
          · rcases List.mem_append.mp hj' with h | h
            · exact le_of_lt (lt_of_lt_of_le hlt (hj.2.1 j' h))
            · rw [List.mem_singleton.mp h]
          · rcases List.mem_append.mp hj' with h | h
            · exact lt_of_lt_of_le hlt (hj.2.1 j' h)
            · exact absurd (List.mem_singleton.mp h ▸ hjc) (lt_irrefl _)
        have ih := scanFrom_spec r cs (P ++ [c]) c hj' hsort'
        rw [heq]
        exact ⟨ih.1, by simp [ih.2]; omega⟩
      · simp only [hlt, ite_false]
        have hj' : IsLeftmostMin M r (P ++ [c]) j := by
          refine ⟨by simp [hj.1], fun j' hj' => ?_, fun j' hj' hjc => ?_⟩
          · rcases List.mem_append.mp hj' with h | h
            · exact hj.2.1 j' h
            · rw [List.mem_singleton.mp h]; exact not_lt.mp hlt
          · rcases List.mem_append.mp hj' with h | h
            · exact hj.2.2 j' h hjc
            · exact absurd (lt_trans (List.mem_singleton.mp h ▸ hjc) (hPc j hj.1))
                (lt_irrefl _)
        have ih := scanFrom_spec r cs (P ++ [c]) j hj' hsort'
        rw [heq]
        exact ⟨ih.1, by simp [ih.2]; omega⟩

omit [LinearOrder ι] in
theorem scan_spec (r : ι) {L : List κ} (hL : L ≠ []) (hsort : L.Pairwise (· < ·)) :
    ∃ j, (scan r L).eval (entryOracle M) = some j ∧ IsLeftmostMin M r L j := by
  cases L with
  | nil => exact absurd rfl hL
  | cons c cs =>
      have h1 : IsLeftmostMin M r [c] c :=
        ⟨by simp, fun j' hj' => by rw [List.mem_singleton.mp hj'],
          fun j' hj' hlt => absurd (List.mem_singleton.mp hj' ▸ hlt) (lt_irrefl _)⟩
      have := (scanFrom_spec r cs [c] c h1 (by simpa using hsort)).1
      exact ⟨(scanFrom r c (M r c) cs).eval (entryOracle M), by simp [scan, entryOracle],
        by simpa using this⟩

omit [LinearOrder ι] in
theorem scan_cost (r : ι) (L : List κ) : (scan (α := α) r L).cost (entryOracle M) ≤ L.length := by
  cases L with
  | nil => simp [scan]
  | cons c cs =>
      have h1 : IsLeftmostMin M r [c] c :=
        ⟨by simp, fun j' hj' => by rw [List.mem_singleton.mp hj'],
          fun j' hj' hlt => absurd (List.mem_singleton.mp hj' ▸ hlt) (lt_irrefl _)⟩
      -- The cost of `scanFrom` does not depend on sortedness; reprove it directly.
      have key : ∀ (cs : List κ) (j : κ) (v : α),
          (scanFrom r j v cs).cost (entryOracle M) = cs.length := by
        intro cs
        induction cs with
        | nil => intro j v; simp [scanFrom]
        | cons c cs ih =>
            intro j v
            simp only [scanFrom, cost_bind, cost_ask, eval_ask]
            by_cases hlt : entryOracle M (r, c) < v
            · simp only [hlt, ite_true, ih, List.length_cons]; omega
            · simp only [hlt, ite_false, ih, List.length_cons]; omega
      simp [scan, key]
      omega

/-- A candidate row output is correct over the column list `L`. -/
def GoodMin (M : ι → κ → α) (L : List κ) (r : ι) (o : Option κ) : Prop :=
  ∃ j, o = some j ∧ IsLeftmostMin M r L j

theorem interp_spec {C' : List κ} (hC' : C'.Pairwise (· < ·)) (hne : C' ≠ []) :
    ∀ (Rs : List ι) (os : List (Option κ)) (suf : List κ),
      Rs.Pairwise (· < ·) → TotallyMonotone M Rs C' →
      List.Forall₂ (GoodMin M C') (odds Rs) os → suf.Sublist C' →
      (∀ r ∈ Rs, ∀ j, IsLeftmostMin M r C' j → j ∈ suf) →
      List.Forall₂ (GoodMin M C') Rs ((interp Rs os suf).eval (entryOracle M)) ∧
        (interp Rs os suf).cost (entryOracle M) ≤ suf.length + (Rs.length + 1) / 2
  | [], os, suf, _, _, _, _, _ => by simp [interp]
  | [r0], os, suf, _, _, _, hsuf, hmem => by
      obtain ⟨j0, hj0⟩ := exists_isLeftmostMin (M := M) r0 hne
      have hj0s := hmem r0 (by simp) j0 hj0
      obtain ⟨j, hjeval, hj⟩ := scan_spec (M := M) r0 (List.ne_nil_of_mem hj0s)
        (hC'.sublist hsuf)
      have hjj : j = j0 := hj.unique (hj0.of_subset hsuf.subset hj0s)
      refine ⟨?_, ?_⟩
      · simp only [interp, eval_map, hjeval]
        exact List.Forall₂.cons ⟨j, rfl, hjj ▸ hj0⟩ List.Forall₂.nil
      · simp only [interp, cost_map, List.length_singleton]
        have := scan_cost (M := M) r0 suf
        omega
  | r0 :: r1 :: rest, os, suf, hRs, hTM, hod, hsuf, hmem => by
      simp only [odds] at hod
      obtain ⟨o1, os', hGood1, hod', rfl⟩ : ∃ o1 os', GoodMin M C' r1 o1 ∧
          List.Forall₂ (GoodMin M C') (odds rest) os' ∧ os = o1 :: os' := by
        cases hod with
        | cons h1 h2 => exact ⟨_, _, h1, h2, rfl⟩
      obtain ⟨j1, rfl, hj1⟩ := hGood1
      have hsufsort : suf.Pairwise (· < ·) := hC'.sublist hsuf
      have hRs' := hRs
      rw [List.pairwise_cons, List.pairwise_cons] at hRs'
      have hr01 : r0 < r1 := hRs'.1 r1 (by simp)
      -- The even row's minimum lies in the window up to `j1`.
      obtain ⟨j0, hj0⟩ := exists_isLeftmostMin (M := M) r0 hne
      have hj0s := hmem r0 (by simp) j0 hj0
      have hj0le : j0 ≤ j1 := hTM.leftmost_mono (by simp) (by simp) hr01 hj0 hj1
      set W := suf.takeWhile fun c => decide (c ≤ j1)
      have hWsub : W.Sublist C' := (List.takeWhile_sublist _).trans hsuf
      have hj0W : j0 ∈ W := (mem_takeWhile_le hsufsort).mpr ⟨hj0s, hj0le⟩
      obtain ⟨j, hjeval, hj⟩ := scan_spec (M := M) r0 (List.ne_nil_of_mem hj0W)
        (hC'.sublist hWsub)
      have hjj : j = j0 := hj.unique (hj0.of_subset hWsub.subset hj0W)
      -- The remaining rows' minima lie in the suffix from `j1`.
      set suf' := suf.dropWhile fun c => decide (c < j1)
      have hsuf' : suf'.Sublist C' := (List.dropWhile_sublist _).trans hsuf
      have hmem' : ∀ r ∈ rest, ∀ j, IsLeftmostMin M r C' j → j ∈ suf' := by
        intro r hr j hj
        have hr1 : r1 < r := hRs'.2.1 r hr
        exact (mem_dropWhile_lt hsufsort).mpr ⟨hmem r (by simp [hr]) j hj,
          hTM.leftmost_mono (by simp) (by simp [hr]) hr1 hj1 hj⟩
      have ih := interp_spec hC' hne rest os' suf' hRs'.2.2
        (hTM.mono (fun r hr => by simp [hr]) (fun c hc => hc)) hod' hsuf' hmem'
      refine ⟨?_, ?_⟩
      · simp only [interp, eval_bind, eval_map]
        exact List.Forall₂.cons ⟨j, hjeval, hjj ▸ hj0⟩ (List.Forall₂.cons ⟨j1, rfl, hj1⟩ ih.1)
      · simp only [interp, cost_bind, cost_map, List.length_cons]
        have h1 := scan_cost (M := M) r0 W
        have h2 : W.length + suf'.length ≤ suf.length + 1 :=
          length_takeWhile_le_add hsufsort j1
        have h3 := ih.2
        simp only [W, suf'] at h1 h2 h3
        omega

/-- **SMAWK.** On a totally monotone matrix with sorted row and column lists,
`smawk` returns the leftmost minimum of every row, using at most
`4 * C.length + 12 * R.length` entry evaluations. -/
theorem smawk_spec : ∀ (n : ℕ) (R : List ι) (C : List κ), R.length ≤ n →
    R.Pairwise (· < ·) → C.Pairwise (· < ·) → C ≠ [] → TotallyMonotone M R C →
    List.Forall₂ (GoodMin M C) R ((smawk R C).eval (entryOracle M)) ∧
      (smawk R C).cost (entryOracle M) ≤ 4 * C.length + 12 * R.length
  | _, [], C, _, _, _, _, _ => by simp [smawk]
  | 0, _ :: _, _, hlen, _, _, _, _ => by simp at hlen
  | n + 1, r :: rs, C, hlen, hR, hC, hne, hTM => by
      obtain ⟨hsub, hlenC', hkeep, hcost⟩ := reduce_spec hR hC hTM
      set C' := (reduce (r :: rs) C).eval (entryOracle M)
      obtain ⟨j0, hj0⟩ := exists_isLeftmostMin (M := M) r hne
      have hC'ne : C' ≠ [] := List.ne_nil_of_mem (hkeep r (by simp) j0 hj0)
      have hC'sort : C'.Pairwise (· < ·) := hC.sublist hsub
      have hTM' : TotallyMonotone M (r :: rs) C' := hTM.mono (fun x hx => hx) hsub.subset
      have hodd := odds_sublist (r :: rs)
      have hoddlen : (odds (r :: rs)).length ≤ n := by
        rw [length_odds]; simp only [List.length_cons] at hlen ⊢; omega
      have ih := smawk_spec n (odds (r :: rs)) C' hoddlen (hR.sublist hodd) hC'sort hC'ne
        (hTM'.mono hodd.subset fun c hc => hc)
      set od := (smawk (odds (r :: rs)) C').eval (entryOracle M)
      have hint := interp_spec hC'sort hC'ne (r :: rs) od C' hR hTM' ih.1
        (List.Sublist.refl _) (fun _ _ j hj => hj.1)
      have e1 : (smawk (r :: rs) C).eval (entryOracle M) =
          (interp (r :: rs) od C').eval (entryOracle M) := by
        rw [smawk]; simp only [eval_bind]; rfl
      have e2 : (smawk (r :: rs) C).cost (entryOracle M) =
          (reduce (r :: rs) C).cost (entryOracle M) +
            ((smawk (odds (r :: rs)) C').cost (entryOracle M) +
              (interp (r :: rs) od C').cost (entryOracle M)) := by
        rw [smawk]; simp only [cost_bind]; rfl
      refine ⟨?_, ?_⟩
      · rw [e1]
        refine forall₂_imp_mem hint.1 fun x hx o ⟨j, ho, hj⟩ => ⟨j, ho, ?_⟩
        obtain ⟨j', hj'⟩ := exists_isLeftmostMin (M := M) x hne
        have := hj.unique (hj'.of_subset hsub.subset (hkeep x hx j' hj'))
        exact this ▸ hj'
      · rw [e2]
        have h2 := ih.2
        have h3 := hint.2
        rw [length_odds] at h2
        simp only [List.length_cons] at hlenC' h2 h3 ⊢
        omega

end Main

/-! ### Minimum entry and query-complexity statements -/

section MatrixMin

/-- Evaluate each chosen candidate once and keep the first one of least value. -/
def bestPair : List (ι × Option κ) → Comp (ι × κ) α (Option (ι × κ × α))
  | [] => Comp.pure none
  | (_, none) :: rest => bestPair rest
  | (r, some j) :: rest => (ask (r, j)).bind fun x => (bestPair rest).map fun b =>
      match b with
      | none => some (r, j, x)
      | some (r', j', y) => if y < x then some (r', j', y) else some (r, j, x)

/-- A minimum entry: SMAWK row minima followed by one evaluation per row. -/
def matrixMin (R : List ι) (C : List κ) : Comp (ι × κ) α (Option (ι × κ)) :=
  (smawk R C).bind fun out =>
    (bestPair (R.zip out)).map (Option.map fun p => (p.1, p.2.1))

variable {M : ι → κ → α}

omit [LinearOrder ι] [LinearOrder κ] in
theorem bestPair_cost : ∀ L : List (ι × Option κ),
    (bestPair (α := α) L).cost (entryOracle M) ≤ L.length
  | [] => by simp [bestPair]
  | (_, none) :: rest => by
      have := bestPair_cost rest
      simp only [bestPair, List.length_cons]; omega
  | (r, some j) :: rest => by
      have := bestPair_cost rest
      simp only [bestPair, cost_bind, cost_ask, cost_map, List.length_cons]; omega

omit [LinearOrder ι] [LinearOrder κ] in
theorem bestPair_spec : ∀ L : List (ι × Option κ),
    ((bestPair L).eval (entryOracle M) = none → ∀ p ∈ L, p.2 = none) ∧
      ∀ r j x, (bestPair L).eval (entryOracle M) = some (r, j, x) →
        x = M r j ∧ (r, some j) ∈ L ∧ ∀ p ∈ L, ∀ j', p.2 = some j' → x ≤ M p.1 j'
  | [] => by simp [bestPair]
  | (r, none) :: rest => by
      obtain ⟨h1, h2⟩ := bestPair_spec rest
      simp only [bestPair]
      refine ⟨fun h p hp => ?_, fun r' j x h => ?_⟩
      · rcases List.mem_cons.mp hp with rfl | hp
        · rfl
        · exact h1 h p hp
      · obtain ⟨hx, hmem, hmin⟩ := h2 r' j x h
        refine ⟨hx, List.mem_cons_of_mem _ hmem, fun p hp j' hj' => ?_⟩
        rcases List.mem_cons.mp hp with rfl | hp
        · simp at hj'
        · exact hmin p hp j' hj'
  | (r, some j) :: rest => by
      obtain ⟨h1, h2⟩ := bestPair_spec rest
      simp only [bestPair, eval_bind, eval_map, eval_ask, entryOracle]
      rcases hb : (bestPair rest).eval (entryOracle M) with _ | ⟨r', j', y⟩
      · have hall := h1 hb
        refine ⟨fun h => by simp at h, fun r'' j'' x h => ?_⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        refine ⟨rfl, by simp, fun p hp j' hj' => ?_⟩
        rcases List.mem_cons.mp hp with rfl | hp
        · simp only [Option.some.injEq] at hj'
          rw [hj']
        · simp [hall p hp] at hj'
      · obtain ⟨hy, hmem, hmin⟩ := h2 r' j' y hb
        refine ⟨fun h => by by_cases hlt : y < M r j <;> simp [hlt] at h, fun r'' j'' x h => ?_⟩
        by_cases hlt : y < M r j
        · simp only [hlt, ite_true, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          refine ⟨hy, List.mem_cons_of_mem _ hmem, fun p hp j₀ hj₀ => ?_⟩
          rcases List.mem_cons.mp hp with rfl | hp
          · simp only [Option.some.injEq] at hj₀
            rw [← hj₀]; exact le_of_lt hlt
          · exact hmin p hp j₀ hj₀
        · simp only [hlt, ite_false, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          refine ⟨rfl, by simp, fun p hp j₀ hj₀ => ?_⟩
          rcases List.mem_cons.mp hp with rfl | hp
          · simp only [Option.some.injEq] at hj₀
            rw [hj₀]
          · exact le_trans (not_lt.mp hlt) (hmin p hp j₀ hj₀)

theorem mem_zip_of_forall₂ {β γ : Type} {P : β → γ → Prop} :
    ∀ {l : List β} {l' : List γ}, List.Forall₂ P l l' →
      ∀ p ∈ l.zip l', p.1 ∈ l ∧ P p.1 p.2
  | _, _, List.Forall₂.nil, p, hp => by simp at hp
  | _, _, List.Forall₂.cons h t, p, hp => by
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨by simp, h⟩
      · obtain ⟨h1, h2⟩ := mem_zip_of_forall₂ t p hp
        exact ⟨List.mem_cons_of_mem _ h1, h2⟩

theorem exists_mem_zip_of_forall₂ {β γ : Type} {P : β → γ → Prop} :
    ∀ {l : List β} {l' : List γ}, List.Forall₂ P l l' → ∀ x ∈ l, ∃ y, (x, y) ∈ l.zip l'
  | _, _, List.Forall₂.nil, x, hx => by simp at hx
  | _, _, List.Forall₂.cons (b := y) h t, x, hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨y, by simp⟩
      · obtain ⟨y', hy'⟩ := exists_mem_zip_of_forall₂ t x hx
        exact ⟨y', List.mem_cons_of_mem _ hy'⟩

/-- A minimum entry of a totally monotone matrix in at most
`4 * C.length + 13 * R.length` evaluations. -/
theorem matrixMin_spec {R : List ι} {C : List κ} (hR : R.Pairwise (· < ·))
    (hC : C.Pairwise (· < ·)) (hRne : R ≠ []) (hCne : C ≠ []) (hTM : TotallyMonotone M R C) :
    (∃ r j, (matrixMin R C).eval (entryOracle M) = some (r, j) ∧ r ∈ R ∧ j ∈ C ∧
      ∀ r' ∈ R, ∀ c ∈ C, M r j ≤ M r' c) ∧
      (matrixMin R C).cost (entryOracle M) ≤ 4 * C.length + 13 * R.length := by
  obtain ⟨hgood, hcost⟩ := smawk_spec R.length R C le_rfl hR hC hCne hTM
  set out := (smawk R C).eval (entryOracle M)
  obtain ⟨hnone, hsome⟩ := bestPair_spec (M := M) (R.zip out)
  have hlen : (R.zip out).length = R.length := by
    simp [List.length_zip, hgood.length_eq]
  refine ⟨?_, ?_⟩
  · obtain ⟨r0, hr0⟩ := List.exists_mem_of_ne_nil R hRne
    obtain ⟨o0, ho0⟩ := exists_mem_zip_of_forall₂ hgood r0 hr0
    obtain ⟨-, j0, hj0, -⟩ := mem_zip_of_forall₂ hgood _ ho0
    rcases hb : (bestPair (R.zip out)).eval (entryOracle M) with _ | ⟨r, j, x⟩
    · simp only at hj0
      exact absurd (hnone hb _ ho0) (by simp [hj0])
    · obtain ⟨hx, hmem, hmin⟩ := hsome r j x hb
      obtain ⟨hr, j', hj', hlm⟩ := mem_zip_of_forall₂ hgood _ hmem
      simp only [Option.some.injEq] at hj'
      subst hj'
      refine ⟨r, j, by simp [matrixMin, hb, out], hr, hlm.1, fun r' hr' c hc => ?_⟩
      obtain ⟨o', ho'⟩ := exists_mem_zip_of_forall₂ hgood r' hr'
      obtain ⟨-, j'', hj'', hlm'⟩ := mem_zip_of_forall₂ hgood _ ho'
      rw [← hx]
      exact le_trans (hmin _ ho' j'' hj'') (hlm'.2.1 c hc)
  · simp only [matrixMin, cost_bind, cost_map]
    have h1 := bestPair_cost (M := M) (R.zip ((smawk R C).eval (entryOracle M)))
    have h2 : (R.zip ((smawk R C).eval (entryOracle M))).length = R.length := hlen
    omega

/-- **Query bound for SMAWK.** For fixed sorted row and column lists there is one
decision tree over entry queries, with budget `4 * C.length + 12 * R.length`,
that returns every leftmost row minimum of every totally monotone matrix. -/
theorem smawk_queryBound (R : List ι) (C : List κ) (hR : R.Pairwise (· < ·))
    (hC : C.Pairwise (· < ·)) (hCne : C ≠ []) :
    ∃ T : DTree (ι × κ) α (Option (List (Option κ))) (4 * C.length + 12 * R.length),
      ∀ M : ι → κ → α, TotallyMonotone M R C →
        ∃ out, T.eval (entryOracle M) = some out ∧ List.Forall₂ (GoodMin M C) R out := by
  refine ⟨(smawk R C).toDTree _, fun M hTM => ?_⟩
  obtain ⟨hgood, hcost⟩ := smawk_spec R.length R C le_rfl hR hC hCne hTM
  exact ⟨_, Comp.toDTree_eval _ _ hcost, hgood⟩

end MatrixMin

/-- **Query bound for the minimum of a Monge matrix** (Lemma 38 of the deterministic
mincut paper): one decision tree with `4 * C.length + 13 * R.length` entry queries. -/
theorem monge_min_queryBound {β : Type} [AddCommGroup β] [LinearOrder β]
    [IsOrderedAddMonoid β] (R : List ι) (C : List κ) (hR : R.Pairwise (· < ·))
    (hC : C.Pairwise (· < ·)) (hRne : R ≠ []) (hCne : C ≠ []) :
    ∃ T : DTree (ι × κ) β (Option (Option (ι × κ))) (4 * C.length + 13 * R.length),
      ∀ M : ι → κ → β, IsMonge M R C →
        ∃ r j, T.eval (entryOracle M) = some (some (r, j)) ∧ r ∈ R ∧ j ∈ C ∧
          ∀ r' ∈ R, ∀ c ∈ C, M r j ≤ M r' c := by
  refine ⟨(matrixMin R C).toDTree _, fun M hM => ?_⟩
  obtain ⟨⟨r, j, heval, hr, hj, hmin⟩, hcost⟩ :=
    matrixMin_spec hR hC hRne hCne hM.totallyMonotone
  exact ⟨r, j, by rw [Comp.toDTree_eval _ _ hcost, heval], hr, hj, hmin⟩

end Search
end CutQueryComplexity
