import CutQueryComplexity.TwoRespecting.Main
import CutQueryComplexity.Search.MongeAllMinima

/-! # Reporting all pairs of a given cut value in the Monge rectangles (all-minima plan, M4)

The searches of `TwoRespecting.Rect` and `TwoRespecting.Main` with the SMAWK minimum replaced
by the all-minima reporter `Search.allMinima`:

* `rectAll rows cols ℓ`: every pair of a Monge rectangle of pair cuts whose value is `ℓ`
  (`rectAll_spec`), given that `ℓ` is a lower bound on the rectangle;
* `samePathAll ℓ L`: every pair `x < y` of one chain with pair cut `ℓ`, by the same halving
  recursion as `samePath` (`samePathAll_spec`, `17 k ⌈log₂ k⌉` queries);
* `diffBlockAll I ℓ P Q`: the pairs of the two rectangles of an ordered pair of heavy paths with
  pair cut `ℓ` (`diffBlockAll_spec`).

Costs depend on the rectangle dimensions only, never on the number of reported pairs.
-/

set_option autoImplicit false

namespace CutQueryComplexity
namespace TwoRespecting

open Search Search.Comp RootedTree

variable {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]

section Rect

variable (T : RootedTree V)

/-- All pairs of one full rectangle of pair cuts whose value is `ℓ`. -/
noncomputable def rectAll {κ : Type} [LinearOrder κ] (toV : κ → V) (rows : List (Pre T))
    (cols : List κ) (ℓ : ℝ) : Comp (Finset V) ℝ (List (V × V)) :=
  ((allMinima rows cols ℓ).mapQ fun p => T.pairShore p.1.val (toV p.2)).map
    fun l => l.map fun p => (p.1.val, toV p.2)

/-- All pairs of distinct edges of one chain whose pair cut is `ℓ`, by halving. -/
noncomputable def samePathAll (ℓ : ℝ) (L : List (Pre T)) : Comp (Finset V) ℝ (List (V × V)) :=
  if L.length < 2 then Comp.pure [] else
    (rectAll T (fun c : (Pre T)ᵒᵈ => (OrderDual.ofDual c).val) (L.take (L.length / 2))
        ((L.drop (L.length / 2)).reverse.map OrderDual.toDual) ℓ).bind fun l0 =>
      (samePathAll ℓ (L.take (L.length / 2))).bind fun l1 =>
        (samePathAll ℓ (L.drop (L.length / 2))).map fun l2 => l0 ++ l1 ++ l2
termination_by L.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop]
  all_goals omega

/-- The pairs of value `ℓ` in the two rectangles of an ordered pair of distinct heavy paths. -/
noncomputable def diffBlockAll (I : V → Finset V) (ℓ : ℝ) (P Q : V) :
    Comp (Finset V) ℝ (List (V × V)) :=
  (rectAll T (fun c : (Pre T)ᵒᵈ => (OrderDual.ofDual c).val)
      (T.sortPre ((T.lpq I P Q).filter fun e => T.IsAnc e Q))
      (T.sortDual (T.lpq I Q P)) ℓ).bind fun l1 =>
    (rectAll T (fun c : Pre T => c.val)
        (T.sortPre ((T.lpq I P Q).filter fun e => ¬ T.IsAnc e Q))
        (T.sortPre ((T.lpq I Q P).filter fun f => ¬ T.IsAnc f P)) ℓ).map fun l3 => l1 ++ l3

variable {T}

theorem rectAll_cost (G : WeightedGraph V) {κ : Type} [LinearOrder κ] (toV : κ → V)
    {rows : List (Pre T)} {cols : List κ} (hR : rows.Pairwise (· < ·))
    (hC : cols.Pairwise (· < ·))
    (hM : IsMonge (fun r c => T.pairCut G r.val (toV c)) rows cols) (ℓ : ℝ) :
    (rectAll T toV rows cols ℓ).cost G.cut ≤ 9 * cols.length + 25 * rows.length := by
  have horacle : (G.cut ∘ fun p : Pre T × κ => T.pairShore p.1.val (toV p.2)) =
      entryOracle (fun r c => T.pairCut G r.val (toV c)) := rfl
  simp only [rectAll, cost_map, cost_mapQ, horacle]
  exact allMinima_cost hR hC hM ℓ

/-- **One rectangle.** Given a lower bound `ℓ` on a Monge rectangle of pair cuts, the output is
exactly the set of its pairs of value `ℓ`. -/
theorem rectAll_spec (G : WeightedGraph V) {κ : Type} [LinearOrder κ] (toV : κ → V)
    {rows : List (Pre T)} {cols : List κ} (hR : rows.Pairwise (· < ·))
    (hC : cols.Pairwise (· < ·))
    (hM : IsMonge (fun r c => T.pairCut G r.val (toV c)) rows cols) {ℓ : ℝ}
    (hlow : ∀ r ∈ rows, ∀ c ∈ cols, ℓ ≤ T.pairCut G r.val (toV c)) (p : V × V) :
    p ∈ (rectAll T toV rows cols ℓ).eval G.cut ↔
      ∃ r ∈ rows, ∃ c ∈ cols, p = (r.val, toV c) ∧ T.pairCut G r.val (toV c) = ℓ := by
  have horacle : (G.cut ∘ fun p : Pre T × κ => T.pairShore p.1.val (toV p.2)) =
      entryOracle (fun r c => T.pairCut G r.val (toV c)) := rfl
  obtain ⟨hmem, -⟩ := allMinima_spec hR hC hM hlow
  simp only [rectAll, eval_map, eval_mapQ, horacle, List.mem_map]
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨h1, h2, h3⟩ := (hmem q).mp hq
    exact ⟨q.1, h1, q.2, h2, rfl, h3⟩
  · rintro ⟨r, hr, c, hc, rfl, hv⟩
    exact ⟨(r, c), (hmem (r, c)).mpr ⟨hr, hc, hv⟩, rfl⟩

theorem samePathAll_of_lt_two {ℓ : ℝ} {L : List (Pre T)} (h : L.length < 2) :
    samePathAll T ℓ L = Comp.pure [] := by
  rw [samePathAll, ite_eq_left h]

theorem samePathAll_of_two_le {ℓ : ℝ} {L : List (Pre T)} (h : ¬ L.length < 2) :
    samePathAll T ℓ L =
      (rectAll T (fun c : (Pre T)ᵒᵈ => (OrderDual.ofDual c).val) (L.take (L.length / 2))
          ((L.drop (L.length / 2)).reverse.map OrderDual.toDual) ℓ).bind fun l0 =>
        (samePathAll T ℓ (L.take (L.length / 2))).bind fun l1 =>
          (samePathAll T ℓ (L.drop (L.length / 2))).map fun l2 => l0 ++ l1 ++ l2 := by
  rw [samePathAll, ite_eq_right h]

/-- **One heavy path.** On a chain list, the output is the set of ordered pairs `x < y` of the
list whose pair cut is `ℓ`, when `ℓ` is a lower bound on these pair cuts; the cost is at most
`17 k ⌈log₂ k⌉` for a list of length `k`, for every level. -/
theorem samePathAll_spec (G : WeightedGraph V) (ℓ : ℝ) :
    ∀ (n : ℕ) (L : List (Pre T)), L.length ≤ n → IsChainList L →
      ((∀ x ∈ L, ∀ y ∈ L, x < y → ℓ ≤ T.pairCut G x.val y.val) →
        ∀ p, p ∈ (samePathAll T ℓ L).eval G.cut ↔
          ∃ x ∈ L, ∃ y ∈ L, x < y ∧ p = (x.val, y.val) ∧ T.pairCut G x.val y.val = ℓ) ∧
      (samePathAll T ℓ L).cost G.cut ≤ 17 * L.length * Nat.clog 2 L.length := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro L hn hL
  by_cases hk : L.length < 2
  · rw [samePathAll_of_lt_two hk]
    refine ⟨fun _ p => ?_, by simp⟩
    simp only [eval_pure, List.not_mem_nil, false_iff, not_exists, not_and]
    intro x hx y hy hxy
    exfalso
    have hlen : L.length ≤ 1 := by omega
    have : x = y := by
      match L, hlen, hx, hy with
      | [a], _, hx, hy => rw [List.mem_singleton.mp hx, List.mem_singleton.mp hy]
    exact lt_irrefl _ (this ▸ hxy)
  · rw [samePathAll_of_two_le hk]
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
    have hR4 := rectAll_cost G (fun c : (Pre T)ᵒᵈ => (OrderDual.ofDual c).val)
      hpw.1 hcols hMonge ℓ
    obtain ⟨hU1, hU4⟩ := ih U.length (by omega) U le_rfl (hL.sublist hUs)
    obtain ⟨hW1, hW4⟩ := ih W.length (by omega) W le_rfl (hL.sublist hWs)
    simp only [eval_bind, eval_map, cost_bind, cost_map]
    refine ⟨fun hlow p => ?_, ?_⟩
    · have hlowR : ∀ r ∈ U, ∀ c ∈ W.reverse.map OrderDual.toDual,
          ℓ ≤ T.pairCut G r.val (OrderDual.ofDual c).val := by
        intro r hr c hc
        simp only [List.mem_map, List.mem_reverse] at hc
        obtain ⟨c, hc, rfl⟩ := hc
        exact hlow r (hUs.subset hr) c (hWs.subset hc) (hpw.2.2 r hr c hc)
      have hR1 := rectAll_spec G (fun c : (Pre T)ᵒᵈ => (OrderDual.ofDual c).val) hpw.1 hcols
        hMonge hlowR p
      have hU := hU1 (fun x hx y hy => hlow x (hUs.subset hx) y (hUs.subset hy)) p
      have hW := hW1 (fun x hx y hy => hlow x (hWs.subset hx) y (hWs.subset hy)) p
      simp only [List.mem_append, hR1, hU, hW]
      constructor
      · rintro ((⟨r, hr, c, hc, rfl, hv⟩ | ⟨x, hx, y, hy, hxy, rfl, hv⟩) |
          ⟨x, hx, y, hy, hxy, rfl, hv⟩)
        · simp only [List.mem_map, List.mem_reverse] at hc
          obtain ⟨c, hc, rfl⟩ := hc
          exact ⟨r, hUs.subset hr, c, hWs.subset hc, hpw.2.2 r hr c hc, rfl, hv⟩
        · exact ⟨x, hUs.subset hx, y, hUs.subset hy, hxy, rfl, hv⟩
        · exact ⟨x, hWs.subset hx, y, hWs.subset hy, hxy, rfl, hv⟩
      · rintro ⟨x, hx, y, hy, hxy, rfl, hv⟩
        rw [← hUW] at hx hy
        rcases List.mem_append.mp hx with hx | hx <;> rcases List.mem_append.mp hy with hy | hy
        · exact Or.inl (Or.inr ⟨x, hx, y, hy, hxy, rfl, hv⟩)
        · exact Or.inl (Or.inl ⟨x, hx, OrderDual.toDual y,
            List.mem_map.mpr ⟨y, List.mem_reverse.mpr hy, rfl⟩, rfl, hv⟩)
        · exact absurd (lt_trans hxy (hpw.2.2 y hy x hx)) (lt_irrefl _)
        · exact Or.inr ⟨x, hx, y, hy, hxy, rfl, hv⟩
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

/-- **Two heavy paths.** The output pairs lie on the paths `P` and `Q` and have pair cut `ℓ`;
when `ℓ` is a lower bound on the pair cuts of distinct non-root edges, every pair `(e, f)` of the
interest lists with `f` not above `P` and pair cut `ℓ` is reported. The cost is linear in the
interest lists. -/
theorem diffBlockAll_spec (G : WeightedGraph V) (I : V → Finset V) {ℓ : ℝ} {P Q : V}
    (hPQ : P ≠ Q)
    (hpair : ∀ e f, e ≠ T.root → f ≠ T.root → e ≠ f → ℓ ≤ T.pairCut G e f) :
    (∀ p ∈ (diffBlockAll T I ℓ P Q).eval G.cut,
        (p.1 ≠ T.root ∧ T.head p.1 = P) ∧ (p.2 ≠ T.root ∧ T.head p.2 = Q) ∧
          T.pairCut G p.1 p.2 = ℓ) ∧
      (∀ e ∈ T.lpq I P Q, ∀ f ∈ T.lpq I Q P, ¬ T.IsAnc f P → T.pairCut G e f = ℓ →
        (e, f) ∈ (diffBlockAll T I ℓ P Q).eval G.cut) := by
  classical
  have hne : ∀ e f, (e ≠ T.root ∧ T.head e = P) → (f ≠ T.root ∧ T.head f = Q) → e ≠ f :=
    fun e f he hf hef => hPQ (he.2.symm.trans (hef ▸ hf.2))
  have hlow1 : ∀ r ∈ T.sortPre ((T.lpq I P Q).filter fun e => T.IsAnc e Q),
      ∀ c ∈ T.sortDual (T.lpq I Q P), ℓ ≤ T.pairCut G r.val (OrderDual.ofDual c).val := by
    intro r hr c hc
    rw [mem_sortPre, Finset.mem_filter, mem_lpq] at hr
    rw [mem_sortDual, mem_lpq] at hc
    exact hpair _ _ hr.1.1.1 hc.1.1 (hne _ _ hr.1.1 hc.1)
  have hlow3 : ∀ r ∈ T.sortPre ((T.lpq I P Q).filter fun e => ¬ T.IsAnc e Q),
      ∀ c ∈ T.sortPre ((T.lpq I Q P).filter fun f => ¬ T.IsAnc f P),
        ℓ ≤ T.pairCut G r.val c.val := by
    intro r hr c hc
    rw [mem_sortPre, Finset.mem_filter, mem_lpq] at hr hc
    exact hpair _ _ hr.1.1.1 hc.1.1.1 (hne _ _ hr.1.1 hc.1.1)
  have a1 := rectAll_spec G (fun c : (Pre T)ᵒᵈ => (OrderDual.ofDual c).val)
    (sortPre_pairwise _) (sortDual_pairwise _) (rect1_monge G I P Q) hlow1
  have b1 := rectAll_spec G (fun c : Pre T => c.val)
    (sortPre_pairwise _) (sortPre_pairwise _) (rect3_monge (T := T) G I hPQ) hlow3
  simp only [diffBlockAll, eval_bind, eval_map]
  refine ⟨fun p hp => ?_, fun e he f hf hfP hv => ?_⟩
  · rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨r, hr, c, hc, rfl, hv⟩ := (a1 p).mp hp
      rw [mem_sortPre, Finset.mem_filter, mem_lpq] at hr
      rw [mem_sortDual, mem_lpq] at hc
      exact ⟨hr.1.1, hc.1, hv⟩
    · obtain ⟨r, hr, c, hc, rfl, hv⟩ := (b1 p).mp hp
      rw [mem_sortPre, Finset.mem_filter, mem_lpq] at hr hc
      exact ⟨hr.1.1, hc.1.1, hv⟩
  · by_cases heQ : T.IsAnc e Q
    · exact List.mem_append_left _ ((a1 (e, f)).mpr ⟨Pre.of T e,
        mem_sortPre.mpr (Finset.mem_filter.mpr ⟨he, heQ⟩), OrderDual.toDual (Pre.of T f),
        mem_sortDual.mpr hf, rfl, hv⟩)
    · exact List.mem_append_right _ ((b1 (e, f)).mpr ⟨Pre.of T e,
        mem_sortPre.mpr (Finset.mem_filter.mpr ⟨he, heQ⟩), Pre.of T f,
        mem_sortPre.mpr (Finset.mem_filter.mpr ⟨hf, hfP⟩), rfl, hv⟩)

/-- The cost of the two rectangles of an ordered pair of heavy paths, for every level. -/
theorem diffBlockAll_cost (G : WeightedGraph V) (I : V → Finset V) (ℓ : ℝ) {P Q : V}
    (hPQ : P ≠ Q) :
    (diffBlockAll T I ℓ P Q).cost G.cut ≤ 25 * (T.lpq I P Q).card + 18 * (T.lpq I Q P).card := by
  classical
  have a4 := rectAll_cost G (fun c : (Pre T)ᵒᵈ => (OrderDual.ofDual c).val)
    (sortPre_pairwise _) (sortDual_pairwise _) (rect1_monge G I P Q) ℓ
  have b4 := rectAll_cost G (fun c : Pre T => c.val)
    (sortPre_pairwise _) (sortPre_pairwise _) (rect3_monge (T := T) G I hPQ) ℓ
  have hpart := Finset.card_filter_add_card_filter_not (s := T.lpq I P Q)
    (p := fun e => T.IsAnc e Q)
  have hsub3 := Finset.card_filter_le (T.lpq I Q P) (fun f => ¬ T.IsAnc f P)
  simp only [diffBlockAll, cost_bind, cost_map]
  rw [length_sortPre, length_sortDual] at a4
  rw [length_sortPre, length_sortPre] at b4
  omega

end Rect

end TwoRespecting
end CutQueryComplexity
