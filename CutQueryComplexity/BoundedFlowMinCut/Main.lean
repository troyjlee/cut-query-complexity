import CutQueryComplexity.BoundedFlowMinCut.Flow.Program
import CutQueryComplexity.BoundedFlowMinCut.LowDegree
import CutQueryComplexity.AllPairs.Representation

/-! # Assembly of the two branches (M7)

`shoreProg` queries all degrees, takes a minimum-degree vertex `v₀` of degree
`δ`, and selects a shore:

* `δ = 0`: the isolated vertex `{v₀}`;
* `1 ≤ δ ≤ cutoff n`: the low-degree branch (`lowDegreeTree δ`);
* `δ > cutoff n`: the high-degree branch (`highBranch`): a dominating set `R`, a
  source `s ∈ R`, a bounded flow with threshold `δ` from `s` to every other
  vertex of `R`, and the best of `{v₀}` and the returned exact cuts (`pickBest`).

If the minimum cut value `λ` is `δ`, the singleton `{v₀}` is already minimum.
If `λ < δ`, a minimum shore meets `R` on both sides
(`small_cut_meets_dominating`), so it separates `s` from some `r ∈ R`; the
bounded flow to `r` cannot overflow and returns a shore of value at most `λ`.

`mainProg` then queries the selected shore for its value.

**Cost.** `n` degree queries; the low branch costs `2δ · forestBudget ≤ 24 n t L²`
(`low_branch_balances`); the high branch costs `13 n L` for `R` plus at most
`|R| ≤ t` bounded flows of `flowCap n` each (`high_branch_balances`); one final
query. Hence `queryBudget n = n + totalConst · n · t · L² + 1` with
`totalConst = 83 + 48 · 3^8` (`mainProg_cost`).
-/

set_option autoImplicit false

namespace CutQueryComplexity.BoundedFlowMinCut
noncomputable section
open scoped Classical
open WeightedGraph Certificate CanonicalST DirectedUnitST.Repair GHReduction

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Selecting the best candidate -/

/-- Keep the current best shore and value unless a returned cut is strictly
smaller. -/
def pickBest : Finset V × ℕ → List (FlowOutcome V) → Finset V × ℕ
  | b, [] => b
  | b, .cut S v :: rest => pickBest (if v < b.2 then (S, v) else b) rest
  | b, .overflow :: rest => pickBest b rest

theorem pickBest_spec (G : WeightedGraph V) :
    ∀ (outs : List (FlowOutcome V)) (b : Finset V × ℕ),
      ProperShore b.1 → G.cut b.1 = b.2 →
      (∀ S v, FlowOutcome.cut S v ∈ outs → ProperShore S ∧ G.cut S = v) →
      ProperShore (pickBest b outs).1 ∧ G.cut (pickBest b outs).1 = (pickBest b outs).2 ∧
        (pickBest b outs).2 ≤ b.2 ∧ ∀ S v, FlowOutcome.cut S v ∈ outs → (pickBest b outs).2 ≤ v
  | [], b, hp, hv, _ => ⟨hp, hv, le_rfl, fun _ _ h => by simp at h⟩
  | .cut S v :: rest, b, hp, hv, hall => by
      have hSv := hall S v (List.mem_cons_self ..)
      have hrest : ∀ S' v', FlowOutcome.cut S' v' ∈ rest → ProperShore S' ∧ G.cut S' = v' :=
        fun S' v' h => hall S' v' (List.mem_cons_of_mem _ h)
      by_cases hlt : v < b.2
      · obtain ⟨h1, h2, h3, h4⟩ := pickBest_spec G rest (S, v) hSv.1 hSv.2 hrest
        rw [pickBest, ite_eq_left hlt]
        refine ⟨h1, h2, h3.trans hlt.le, fun S' v' h => ?_⟩
        rcases List.mem_cons.mp h with h | h
        · cases h
          exact h3
        · exact h4 S' v' h
      · obtain ⟨h1, h2, h3, h4⟩ := pickBest_spec G rest b hp hv hrest
        rw [pickBest, ite_eq_right hlt]
        refine ⟨h1, h2, h3, fun S' v' h => ?_⟩
        rcases List.mem_cons.mp h with h | h
        · cases h
          exact h3.trans (not_lt.mp hlt)
        · exact h4 S' v' h
  | .overflow :: rest, b, hp, hv, hall => by
      obtain ⟨h1, h2, h3, h4⟩ := pickBest_spec G rest b hp hv
        (fun S' v' h => hall S' v' (List.mem_cons_of_mem _ h))
      rw [pickBest]
      refine ⟨h1, h2, h3, fun S' v' h => ?_⟩
      rcases List.mem_cons.mp h with h | h
      · cases h
      · exact h4 S' v' h

/-! ### The branches -/

/-- The high-degree branch. -/
def highBranch (deg : V → ℕ) (δ : ℕ) (v₀ : V) : Prog (Finset V) ℝ (Finset V) :=
  (dominatingProg deg).bind fun R =>
    if h : R.Nonempty then
      (sequenceList (fun r => boundedFlow deg δ h.choose r) (R.erase h.choose).toList).map
        fun outs => (pickBest ({v₀}, δ) outs).1
    else .pure {v₀}

/-- The branch selection after the degrees are known. -/
def selectShore (deg : V → ℕ) (h : (Finset.univ : Finset V).Nonempty) :
    Prog (Finset V) ℝ (Finset V) :=
  if deg (minVertex deg h) = 0 then .pure {minVertex deg h}
  else if deg (minVertex deg h) ≤ cutoff (Fintype.card V) then
    liftDTree (lowDegreeTree (deg (minVertex deg h)))
  else highBranch deg (deg (minVertex deg h)) (minVertex deg h)

/-- Degrees, then the selected branch. -/
def shoreProg : Prog (Finset V) ℝ (Finset V) :=
  degreeProg.bind fun deg =>
    if h : (Finset.univ : Finset V).Nonempty then selectShore deg h else .pure ∅

/-- The selected shore, with its value queried at the end. -/
def mainProg : Prog (Finset V) ℝ (AllPairs.STAnswer V) :=
  shoreProg.bind fun S => (Prog.ask S).map fun a => ⟨S, a⟩

/-! ### Correctness -/

theorem highBranch_correct {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G)
    (hn : 2 ≤ Fintype.card V) {deg : V → ℕ} (hdeg : ∀ v, deg v = natDegree G v) {δ : ℕ}
    (hδ1 : 1 ≤ δ) (hδ : ∀ v, δ ≤ natDegree G v) {v₀ : V} (hv₀ : G.cut {v₀} = δ) :
    IsMinCut G (Prog.eval G.cut (highBranch deg δ v₀)) := by
  obtain ⟨hdom, -, -⟩ := dominating_correct G hG deg hdeg hδ
  set R := Prog.eval G.cut (dominatingProg deg)
  have hRne : R.Nonempty := by
    rcases hdom v₀ with h | ⟨r, hr, -⟩
    · exact ⟨v₀, h⟩
    · exact ⟨r, hr⟩
  have hsing : ProperShore ({v₀} : Finset V) := by
    refine ⟨Finset.singleton_nonempty v₀, fun h => ?_⟩
    have := congrArg Finset.card h
    rw [Finset.card_singleton, Finset.card_univ] at this
    omega
  set s := hRne.choose
  have hs : s ∈ R := hRne.choose_spec
  set outs := ((R.erase s).toList).map (fun r => Prog.eval G.cut (boundedFlow deg δ s r))
  have heval : Prog.eval G.cut (highBranch deg δ v₀) = (pickBest ({v₀}, δ) outs).1 := by
    rw [highBranch, Prog.eval_bind, dite_eq_left hRne, Prog.eval_map, sequenceList_eval]
  have hvalid : ∀ r ∈ R.erase s, (Prog.eval G.cut (boundedFlow deg δ s r)).Valid G δ s r :=
    fun r _ => (boundedFlow_spec hG hδ1 hδ hdeg s r).1
  have hcuts : ∀ S v, FlowOutcome.cut S v ∈ outs → ProperShore S ∧ G.cut S = v := by
    intro S v hm
    obtain ⟨r, hr, hro⟩ := List.mem_map.mp hm
    have hr' := Finset.mem_toList.mp hr
    have hv := hvalid r hr'
    rw [hro] at hv
    obtain ⟨⟨hsS, hrS, -⟩, hcut, -⟩ := hv
    refine ⟨⟨⟨s, hsS⟩, fun h => hrS (h ▸ Finset.mem_univ r)⟩, hcut⟩
  obtain ⟨hP, hval, hle, hbest⟩ := pickBest_spec G outs ({v₀}, δ) hsing hv₀ hcuts
  rw [heval]
  refine ⟨hP, fun T hT => ?_⟩
  rw [hval]
  by_cases hTδ : (δ : ℝ) ≤ G.cut T
  · exact (Nat.cast_le.mpr hle).trans hTδ
  · push Not at hTδ
    obtain ⟨hin, hout⟩ := small_cut_meets_dominating G hG hδ hdom hT hTδ
    -- a shore `U ∈ {T, Tᶜ}` with `s ∈ U` and some `r ∈ R \ U`
    obtain ⟨U, r, hsU, hrU, hrR, hUT⟩ : ∃ U r, s ∈ U ∧ r ∉ U ∧ r ∈ R ∧ G.cut U = G.cut T := by
      by_cases hsT : s ∈ T
      · obtain ⟨r, hr⟩ := hout
        rw [Finset.mem_inter, Finset.mem_compl] at hr
        exact ⟨T, r, hsT, hr.1, hr.2, rfl⟩
      · obtain ⟨r, hr⟩ := hin
        rw [Finset.mem_inter] at hr
        exact ⟨Tᶜ, r, Finset.mem_compl.mpr hsT, fun h => (Finset.mem_compl.mp h) hr.1, hr.2,
          G.cut_compl T⟩
    have hrs : r ∈ R.erase s := Finset.mem_erase.mpr ⟨fun h => hrU (h ▸ hsU), hrR⟩
    have hv := hvalid r hrs
    have hmem : Prog.eval G.cut (boundedFlow deg δ s r) ∈ outs :=
      List.mem_map.mpr ⟨r, Finset.mem_toList.mpr hrs, rfl⟩
    revert hv hmem
    cases Prog.eval G.cut (boundedFlow deg δ s r) with
    | cut S v =>
        intro hv hmem
        obtain ⟨⟨-, -, hmin⟩, hcut, -⟩ := hv
        have h1 := hbest S v hmem
        have h2 : G.cut S ≤ G.cut U := hmin U hsU hrU
        rw [hcut, hUT] at h2
        exact (Nat.cast_le.mpr h1).trans h2
    | overflow =>
        intro hv _
        have := hv U hsU hrU
        rw [hUT] at this
        linarith

theorem selectShore_correct {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G)
    (hn : 2 ≤ Fintype.card V) (h : (Finset.univ : Finset V).Nonempty) :
    IsMinCut G (Prog.eval G.cut (selectShore (natDegree G) h)) := by
  set v₀ := minVertex (natDegree G) h
  have hδ : ∀ v, natDegree G v₀ ≤ natDegree G v := minVertex_le _ h
  have hv₀ : G.cut {v₀} = natDegree G v₀ := cut_singleton_eq_natDegree hG v₀
  have hsing : ProperShore ({v₀} : Finset V) := by
    refine ⟨Finset.singleton_nonempty v₀, fun h => ?_⟩
    have := congrArg Finset.card h
    rw [Finset.card_singleton, Finset.card_univ] at this
    omega
  unfold selectShore
  by_cases h0 : natDegree G v₀ = 0
  · rw [ite_eq_left h0, Prog.eval_pure]
    refine ⟨hsing, fun T _ => ?_⟩
    rw [hv₀, h0, Nat.cast_zero]
    exact Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => G.nonneg u v
  · rw [ite_eq_right h0]
    by_cases hlow : natDegree G v₀ ≤ cutoff (Fintype.card V)
    · rw [ite_eq_left hlow, liftDTree_eval]
      exact lowDegree_correct G hG hn (Nat.one_le_iff_ne_zero.mpr h0) hv₀
    · rw [ite_eq_right hlow]
      exact highBranch_correct hG hn (fun _ => rfl) (Nat.one_le_iff_ne_zero.mpr h0) hδ hv₀

theorem shoreProg_correct {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G)
    (hn : 2 ≤ Fintype.card V) : IsMinCut G (Prog.eval G.cut (shoreProg (V := V))) := by
  have h : (Finset.univ : Finset V).Nonempty :=
    Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp (by omega))
  rw [shoreProg, Prog.eval_bind, degreeProg_eval hG, dite_eq_left h]
  exact selectShore_correct hG hn h

theorem mainProg_correct {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G)
    (hn : 2 ≤ Fintype.card V) :
    IsMinCut G (Prog.eval G.cut (mainProg (V := V))).shore ∧
      (Prog.eval G.cut (mainProg (V := V))).value =
        G.cut (Prog.eval G.cut (mainProg (V := V))).shore := by
  simp only [mainProg, Prog.eval_bind, Prog.eval_map, Prog.eval_ask]
  exact ⟨shoreProg_correct hG hn, trivial⟩

/-! ### Cost -/

/-- The constant of the main cap: `13` for the dominating set plus the flows'
`70 + 48 · 3^8`; it also covers the low branch's `24`. -/
def totalConst : ℕ := 83 + 48 * 3 ^ 8

/-- The query cap: `n` degree queries, the branch, and the final value query. -/
def queryBudget (n : ℕ) : ℕ := n + totalConst * n * cutoffRoot n * logFactor n ^ 2 + 1

theorem highBranch_cost {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G)
    {deg : V → ℕ} (hdeg : ∀ v, deg v = natDegree G v) {δ : ℕ}
    (hlarge : cutoff (Fintype.card V) < δ) (hδ : ∀ v, δ ≤ natDegree G v) (v₀ : V) :
    Prog.cost G.cut (highBranch deg δ v₀) ≤
      totalConst * Fintype.card V * cutoffRoot (Fintype.card V) *
        logFactor (Fintype.card V) ^ 2 := by
  have hδ1 : 1 ≤ δ := by have := cutoffRoot_le_cutoff (Fintype.card V); unfold cutoffRoot at this; omega
  obtain ⟨-, hsize, hdomcost⟩ := dominating_correct G hG deg hdeg hδ
  rw [highBranch, Prog.cost_bind]
  set R := Prog.eval G.cut (dominatingProg deg)
  set n := Fintype.card V
  set L := logFactor n
  set t := cutoffRoot n
  have hRt : R.card ≤ t := high_branch_balances hlarge hsize
  have hflows : ∀ (S : Finset V) (s : V), Prog.cost G.cut
      (sequenceList (fun r => boundedFlow deg δ s r) S.toList) ≤ S.card * flowCap n := by
    intro S s
    have := sequenceList_cost_le (fun r => boundedFlow deg δ s r) S.toList G.cut
      (fun _ => flowCap n) (fun r _ => (boundedFlow_spec hG hδ1 hδ hdeg s r).2)
    simpa [List.map_const', List.sum_replicate, Finset.length_toList] using this
  have hrest : Prog.cost G.cut (if h : R.Nonempty then
      (sequenceList (fun r => boundedFlow deg δ h.choose r) (R.erase h.choose).toList).map
        (fun outs => (pickBest ({v₀}, δ) outs).1) else Prog.pure {v₀}) ≤ t * flowCap n := by
    by_cases h : R.Nonempty
    · rw [dite_eq_left h, Prog.cost_map]
      refine (hflows _ _).trans (Nat.mul_le_mul_right _ ((Finset.card_erase_le).trans hRt))
    · rw [dite_eq_right h, Prog.cost_pure]
      exact Nat.zero_le _
  have hL1 : 1 ≤ L := one_le_logFactor n
  have ht1 : 1 ≤ t := Nat.le_add_left 1 _
  have hreal : ((13 * n * L + t * flowCap n : ℕ) : ℝ) ≤ ((totalConst * n * t * L ^ 2 : ℕ) : ℝ) := by
    simp only [flowCap, totalConst]
    push_cast
    have hL1R : (1 : ℝ) ≤ L := by exact_mod_cast hL1
    have ht1R : (1 : ℝ) ≤ t := by exact_mod_cast ht1
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h1 : (n : ℝ) * L ≤ n * t * L ^ 2 := by
      have : (L : ℝ) ≤ t * L ^ 2 := by nlinarith
      nlinarith
    nlinarith
  have := (Nat.cast_le (α := ℝ)).mp hreal
  omega

theorem selectShore_cost {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G)
    (h : (Finset.univ : Finset V).Nonempty) :
    Prog.cost G.cut (selectShore (natDegree G) h) ≤
      totalConst * Fintype.card V * cutoffRoot (Fintype.card V) *
        logFactor (Fintype.card V) ^ 2 := by
  set v₀ := minVertex (natDegree G) h
  have hδ : ∀ v, natDegree G v₀ ≤ natDegree G v := minVertex_le _ h
  unfold selectShore
  by_cases h0 : natDegree G v₀ = 0
  · rw [ite_eq_left h0, Prog.cost_pure]
    exact Nat.zero_le _
  · rw [ite_eq_right h0]
    by_cases hlow : natDegree G v₀ ≤ cutoff (Fintype.card V)
    · rw [ite_eq_left hlow]
      refine (liftDTree_cost_le _ _).trans ((low_branch_balances hlow).trans ?_)
      unfold totalConst
      gcongr
      norm_num
    · rw [ite_eq_right hlow]
      exact highBranch_cost hG (fun _ => rfl) (not_le.mp hlow) hδ v₀

theorem mainProg_cost {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G) :
    Prog.cost G.cut (mainProg (V := V)) ≤ queryBudget (Fintype.card V) := by
  have hdeg := degreeProg_cost (V := V) G.cut
  simp only [mainProg, shoreProg, Prog.cost_bind, Prog.cost_map, Prog.cost_ask,
    degreeProg_eval hG, hdeg]
  unfold queryBudget
  by_cases h : (Finset.univ : Finset V).Nonempty
  · rw [dite_eq_left h]
    have := selectShore_cost hG h
    omega
  · rw [dite_eq_right h, Prog.cost_pure]
    omega

end
end CutQueryComplexity.BoundedFlowMinCut
