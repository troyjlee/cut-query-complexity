import CutQueryComplexity.TwoRespecting.Cuts
import CutQueryComplexity.TwoRespecting.HeavyPath
import CutQueryComplexity.Search.Combinators

/-! # Monge rectangles of pair cuts and the same-path recursion

`rectMin rows cols` runs SMAWK on the matrix `K r c = cut (A r ∆ A c)`, with one
cut query per entry. `samePath L` searches all pairs of distinct edges of one
chain `L` by splitting it in half, searching the nested rectangle between the
halves, and recursing (paper App. A, "Two edges on the same heavy path").
-/

namespace CutQueryComplexity
namespace TwoRespecting

open Search Search.Comp RootedTree

variable {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace RootedTree

variable (T : RootedTree V)

/-- A vertex set sorted in preorder. -/
noncomputable def sortPre (s : Finset V) : List (Pre T) :=
  (show Finset (Pre T) from s).sort (· ≤ ·)

/-- A vertex set sorted in reverse preorder, as a list of the dual order. -/
noncomputable def sortDual (s : Finset V) : List (Pre T)ᵒᵈ :=
  (show Finset (Pre T)ᵒᵈ from s).sort (· ≤ ·)

variable {T}

omit [Fintype V] in
theorem mem_sortPre {s : Finset V} {x : Pre T} : x ∈ T.sortPre s ↔ x.val ∈ s :=
  Finset.mem_sort _

omit [Fintype V] in
theorem mem_sortDual {s : Finset V} {x : (Pre T)ᵒᵈ} :
    x ∈ T.sortDual s ↔ (OrderDual.ofDual x).val ∈ s :=
  Finset.mem_sort _

omit [Fintype V] in
theorem length_sortPre (s : Finset V) : (T.sortPre s).length = s.card :=
  Finset.length_sort _

omit [Fintype V] in
theorem length_sortDual (s : Finset V) : (T.sortDual s).length = s.card :=
  Finset.length_sort _

theorem pairwise_lt_sort {α : Type} [LinearOrder α] (s : Finset α) :
    (s.sort (· ≤ ·)).Pairwise (· < ·) :=
  ((Finset.pairwise_sort s (· ≤ ·)).and (Finset.sort_nodup s (· ≤ ·))).imp
    fun ⟨hle, hne⟩ => lt_of_le_of_ne hle hne

omit [Fintype V] in
theorem sortPre_pairwise (s : Finset V) : (T.sortPre s).Pairwise (· < ·) := pairwise_lt_sort _

omit [Fintype V] in
theorem sortDual_pairwise (s : Finset V) : (T.sortDual s).Pairwise (· < ·) := pairwise_lt_sort _

omit [Fintype V] in
/-- In a set of pairwise comparable vertices, the preorder is the ancestry order. -/
theorem isAnc_of_lt_of_chain {x y : Pre T} (hc : T.IsAnc x.val y.val ∨ T.IsAnc y.val x.val)
    (hlt : x < y) : T.IsAnc x.val y.val :=
  isAnc_of_rootPath_le hc (Pre.le_iff.mp (le_of_lt hlt))

end RootedTree

section Rect

variable (T : RootedTree V)

/-- Search one full rectangle of pair cuts with SMAWK. -/
noncomputable def rectMin {κ : Type} [LinearOrder κ] (toV : κ → V) (rows : List (Pre T))
    (cols : List κ) : Comp (Finset V) ℝ (List (V × V)) :=
  if rows = [] ∨ cols = [] then Comp.pure [] else
    ((matrixMin (α := ℝ) rows cols).mapQ fun p => T.pairShore p.1.val (toV p.2)).map
      fun o => match o with
        | none => []
        | some p => [(p.1.val, toV p.2)]

/-- All pairs of distinct edges in one chain, by halving. -/
noncomputable def samePath (L : List (Pre T)) : Comp (Finset V) ℝ (List (V × V)) :=
  if L.length < 2 then Comp.pure [] else
    (rectMin T (fun c : (Pre T)ᵒᵈ => (OrderDual.ofDual c).val) (L.take (L.length / 2))
        ((L.drop (L.length / 2)).reverse.map OrderDual.toDual)).bind fun l0 =>
      (samePath (L.take (L.length / 2))).bind fun l1 =>
        (samePath (L.drop (L.length / 2))).map fun l2 => l0 ++ l1 ++ l2
termination_by L.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop]
  all_goals omega

variable {T}

theorem rectMin_spec (G : WeightedGraph V) {κ : Type} [LinearOrder κ] (toV : κ → V)
    {rows : List (Pre T)} {cols : List κ} (hR : rows.Pairwise (· < ·))
    (hC : cols.Pairwise (· < ·))
    (hM : IsMonge (fun r c => T.pairCut G r.val (toV c)) rows cols) :
    (∀ p ∈ (rectMin T toV rows cols).eval G.cut,
        (∃ r ∈ rows, p.1 = r.val) ∧ ∃ c ∈ cols, p.2 = toV c) ∧
      (∀ r ∈ rows, ∀ c ∈ cols, ∃ p ∈ (rectMin T toV rows cols).eval G.cut,
        T.pairCut G p.1 p.2 ≤ T.pairCut G r.val (toV c)) ∧
      ((rectMin T toV rows cols).eval G.cut).length ≤ 1 ∧
      (rectMin T toV rows cols).cost G.cut ≤ 4 * cols.length + 13 * rows.length := by
  unfold rectMin
  by_cases hempty : rows = [] ∨ cols = []
  · rw [ite_eq_left hempty]
    refine ⟨by simp, ?_, by simp, by simp⟩
    rcases hempty with h | h <;> simp [h]
  · rw [ite_eq_right hempty]
    push Not at hempty
    have horacle : (G.cut ∘ fun p : Pre T × κ => T.pairShore p.1.val (toV p.2)) =
        entryOracle (fun r c => T.pairCut G r.val (toV c)) := rfl
    obtain ⟨⟨r, c, heval, hr, hc, hmin⟩, hcost⟩ :=
      matrixMin_spec hR hC hempty.1 hempty.2 hM.totallyMonotone
    simp only [eval_map, eval_mapQ, cost_map, cost_mapQ, horacle, heval]
    refine ⟨?_, ?_, by simp, hcost⟩
    · intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      exact ⟨⟨r, hr, rfl⟩, c, hc, rfl⟩
    · intro r' hr' c' hc'
      exact ⟨_, List.mem_singleton_self _, hmin r' hr' c' hc'⟩

omit [LinearOrder V] in
theorem rectMin_length_le (o : Finset V → ℝ) {κ : Type} [LinearOrder κ] (toV : κ → V)
    (rows : List (Pre T)) (cols : List κ) :
    ((rectMin T toV rows cols).eval o).length ≤ rows.length ∧
      ((rectMin T toV rows cols).eval o).length ≤ 1 := by
  unfold rectMin
  by_cases h : rows = [] ∨ cols = []
  · rw [ite_eq_left h]; simp
  · rw [ite_eq_right h]
    push Not at h
    have hr : 1 ≤ rows.length := List.length_pos_iff.mpr h.1
    simp only [eval_map]
    split <;> simp; omega

theorem samePath_of_lt_two {L : List (Pre T)} (h : L.length < 2) : samePath T L = Comp.pure [] := by
  rw [samePath, ite_eq_left h]

theorem samePath_of_two_le {L : List (Pre T)} (h : ¬ L.length < 2) :
    samePath T L =
      (rectMin T (fun c : (Pre T)ᵒᵈ => (OrderDual.ofDual c).val) (L.take (L.length / 2))
          ((L.drop (L.length / 2)).reverse.map OrderDual.toDual)).bind fun l0 =>
        (samePath T (L.take (L.length / 2))).bind fun l1 =>
          (samePath T (L.drop (L.length / 2))).map fun l2 => l0 ++ l1 ++ l2 := by
  rw [samePath, ite_eq_right h]

/-- A list sorted in preorder whose members are pairwise comparable. -/
def IsChainList (L : List (Pre T)) : Prop :=
  L.Pairwise (· < ·) ∧ ∀ x ∈ L, ∀ y ∈ L, T.IsAnc x.val y.val ∨ T.IsAnc y.val x.val

omit [Fintype V] in
theorem IsChainList.sublist {L L' : List (Pre T)} (h : IsChainList L) (hs : L'.Sublist L) :
    IsChainList L' :=
  ⟨h.1.sublist hs, fun x hx y hy => h.2 x (hs.subset hx) y (hs.subset hy)⟩

theorem samePath_spec (G : WeightedGraph V) : ∀ (n : ℕ) (L : List (Pre T)), L.length ≤ n →
    IsChainList L →
    (∀ p ∈ (samePath T L).eval G.cut,
        (∃ x ∈ L, p.1 = x.val) ∧ (∃ y ∈ L, p.2 = y.val) ∧ p.1 ≠ p.2) ∧
      (∀ x ∈ L, ∀ y ∈ L, x < y → ∃ p ∈ (samePath T L).eval G.cut,
        T.pairCut G p.1 p.2 ≤ T.pairCut G x.val y.val) ∧
      ((samePath T L).eval G.cut).length ≤ L.length - 1 ∧
      (samePath T L).cost G.cut ≤ 17 * L.length * Nat.clog 2 L.length := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro L hn hL
  by_cases hk : L.length < 2
  · rw [samePath_of_lt_two hk]
    refine ⟨by simp, fun x hx y hy hxy => ?_, by simp, by simp⟩
    exfalso
    have hlen : L.length ≤ 1 := by omega
    have : x = y := by
      match L, hlen, hx, hy with
      | [a], _, hx, hy => rw [List.mem_singleton.mp hx, List.mem_singleton.mp hy]
    exact lt_irrefl _ (this ▸ hxy)
  · rw [samePath_of_two_le hk]
    set m := L.length / 2 with hm
    set U := L.take m
    set W := L.drop m
    have hUW : U ++ W = L := List.take_append_drop m L
    have hUs : U.Sublist L := List.take_sublist _ _
    have hWs : W.Sublist L := List.drop_sublist _ _
    have hUlen : U.length = m := by simp [U, List.length_take]; omega
    have hWlen : W.length = L.length - m := by simp [W]
    have hpw := hUW ▸ hL.1
    rw [List.pairwise_append] at hpw
    -- the rectangle between the two halves is nested and Monge
    have hcols : (W.reverse.map OrderDual.toDual).Pairwise (· < ·) := by
      rw [List.pairwise_map, List.pairwise_reverse]
      exact hpw.2.1.imp fun h => OrderDual.toDual_lt_toDual.mpr h
    have hMonge : IsMonge (fun r (c : (Pre T)ᵒᵈ) => T.pairCut G r.val (OrderDual.ofDual c).val)
        U (W.reverse.map OrderDual.toDual) := by
      intro r hr r' hr' c hc c' hc' hrr hcc
      simp only [List.mem_map, List.mem_reverse] at hc hc'
      obtain ⟨c, hc, rfl⟩ := hc
      obtain ⟨c', hc', rfl⟩ := hc'
      rw [OrderDual.toDual_lt_toDual] at hcc
      have hr'L := hUs.subset hr'
      exact pairCut_monge_nested G
        (isAnc_of_lt_of_chain (hL.2 r (hUs.subset hr) r' hr'L) hrr)
        (isAnc_of_lt_of_chain (hL.2 c' (hWs.subset hc') c (hWs.subset hc)) hcc)
        (isAnc_of_lt_of_chain (hL.2 r' hr'L c' (hWs.subset hc')) (hpw.2.2 r' hr' c' hc'))
    obtain ⟨hR1, hR2, hR3, hR4⟩ := rectMin_spec G (fun c : (Pre T)ᵒᵈ => (OrderDual.ofDual c).val)
      hpw.1 hcols hMonge
    have hlt_n : ∀ k, k < L.length → k < n + 1 := fun k hk => by omega
    obtain ⟨hU1, hU2, hU3, hU4⟩ := ih U.length (by omega) U le_rfl (hL.sublist hUs)
    obtain ⟨hW1, hW2, hW3, hW4⟩ := ih W.length (by omega) W le_rfl (hL.sublist hWs)
    simp only [eval_bind, eval_map, cost_bind, cost_map]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro p hp
      simp only [List.mem_append] at hp
      rcases hp with (hp | hp) | hp
      · obtain ⟨⟨r, hr, h1⟩, c, hc, h2⟩ := hR1 p hp
        simp only [List.mem_map, List.mem_reverse] at hc
        obtain ⟨c, hc, rfl⟩ := hc
        refine ⟨⟨r, hUs.subset hr, h1⟩, ⟨c, hWs.subset hc, h2⟩, ?_⟩
        rw [h1, h2]
        intro he
        have hrc : r = c := he
        exact lt_irrefl _ (hrc ▸ hpw.2.2 r hr c hc)
      · obtain ⟨⟨x, hx, h1⟩, ⟨y, hy, h2⟩, h3⟩ := hU1 p hp
        exact ⟨⟨x, hUs.subset hx, h1⟩, ⟨y, hUs.subset hy, h2⟩, h3⟩
      · obtain ⟨⟨x, hx, h1⟩, ⟨y, hy, h2⟩, h3⟩ := hW1 p hp
        exact ⟨⟨x, hWs.subset hx, h1⟩, ⟨y, hWs.subset hy, h2⟩, h3⟩
    · intro x hx y hy hxy
      rw [← hUW] at hx hy
      rcases List.mem_append.mp hx with hx | hx <;> rcases List.mem_append.mp hy with hy | hy
      · obtain ⟨p, hp, hle⟩ := hU2 x hx y hy hxy
        exact ⟨p, List.mem_append_left _ (List.mem_append_right _ hp), hle⟩
      · obtain ⟨p, hp, hle⟩ := hR2 x hx (OrderDual.toDual y)
          (List.mem_map.mpr ⟨y, List.mem_reverse.mpr hy, rfl⟩)
        exact ⟨p, List.mem_append_left _ (List.mem_append_left _ hp), hle⟩
      · exact absurd (lt_trans hxy (hpw.2.2 y hy x hx)) (lt_irrefl _)
      · obtain ⟨p, hp, hle⟩ := hW2 x hx y hy hxy
        exact ⟨p, List.mem_append_right _ hp, hle⟩
    · simp only [List.length_append]
      omega
    · -- `T(k) ≤ 17k + T(⌊k/2⌋) + T(⌈k/2⌉)` and `clog` drops by one on each half
      have hk2 : 2 ≤ L.length := by omega
      have hclog : Nat.clog 2 L.length = Nat.clog 2 ((L.length + 1) / 2) + 1 := by
        have := Nat.clog_of_two_le (b := 2) (n := L.length) (by decide) hk2
        rwa [show L.length + 2 - 1 = L.length + 1 by omega] at this
      have hcU : Nat.clog 2 U.length ≤ Nat.clog 2 ((L.length + 1) / 2) :=
        Nat.clog_mono_right 2 (by omega)
      have hcW : Nat.clog 2 W.length ≤ Nat.clog 2 ((L.length + 1) / 2) :=
        Nat.clog_mono_right 2 (by omega)
      simp only [List.length_map, List.length_reverse] at hR4
      set c := Nat.clog 2 ((L.length + 1) / 2)
      have h1 : 17 * U.length * Nat.clog 2 U.length ≤ 17 * U.length * c :=
        Nat.mul_le_mul_left _ hcU
      have h2 : 17 * W.length * Nat.clog 2 W.length ≤ 17 * W.length * c :=
        Nat.mul_le_mul_left _ hcW
      have h3 : 17 * U.length * c + 17 * W.length * c = 17 * L.length * c := by
        rw [← Nat.add_mul, ← Nat.mul_add, hUlen, hWlen]; congr 2; omega
      have h4 : 17 * L.length * Nat.clog 2 L.length = 17 * L.length * c + 17 * L.length := by
        rw [hclog, Nat.mul_succ]
      omega

end Rect

end TwoRespecting
end CutQueryComplexity
