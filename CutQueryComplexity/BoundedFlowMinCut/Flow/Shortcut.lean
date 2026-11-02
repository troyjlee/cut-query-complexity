import CutQueryComplexity.BoundedFlowMinCut.Flow.Forest
import CutQueryComplexity.BoundedFlowMinCut.Ordered
import CutQueryComplexity.BoundedFlowMinCut.Dominating

/-! # Shortening an augmenting path (M4, Lemma 4.3 of the paper)

Let `d ≥ 1` bound every degree from below, `q = usedCount f`, and let `π` be a
simple augmenting path with `r` vertices. While `d (r - 1) > 8 (n + q)`, one
shortcut (`shortcutStep`, `13 ⌈log₂ n⌉` queries):

* average search with the incidence oracle of `H_f = G \ K_f` on the vertex set
  `P` of `π` finds a centre `u` with `c ≥ (r d - 2q)/n` path neighbours in `H_f`
  (the total incidence is `Σ_{p ∈ P} (deg p - deg_{K_f} p) ≥ r d - 2q`);
* two ordered binary searches (`firstNbrTree`, on `π` and on its reverse) find
  the first and last positions `i ≤ j` of a neighbour of `u`; every neighbour
  lies between them, so `c ≤ j - i + 1`;
* the walk `π[0..i] → u → π[j..]` (`splice`) uses two unused edges, hence is
  residual with the same ends, and `loopErase` makes it simple again.

The new path has at most `r + 3 - c` vertices, and the stopping rule gives
`8 n r' ≤ (8 n - 3 d) r` (`shortcutStep_spec`). The loop (`shortcutLoop`) thus
ends with `d (r - 1) ≤ 8 (n + q)` after at most `(8n / 3d) ln r + 1` shortcuts,
measured by the potential `domPotential (8n) (3d)` (`shortcutLoop_spec`); the
cost is `O(⌈n/d⌉ L²)` (`shortcutLoop_cost_le`).
-/

set_option autoImplicit false

namespace CutQueryComplexity.BoundedFlowMinCut
noncomputable section
open scoped Classical
open WeightedGraph Certificate CanonicalST DirectedUnitST.Repair GHReduction

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The neighbour mass of `u` over `A` in `G.subtract K`, in three queries. -/
def nbrMassQuery (K : WeightedGraph V) (u : V) (A : Finset V) : DTree (Finset V) ℝ ℝ 3 :=
  residualCross K {u} (A \ {u})

theorem nbrMassQuery_eval (G K : WeightedGraph V) (hK : ∀ u v, K.w u v ≤ G.w u v) (u : V)
    (A : Finset V) : (nbrMassQuery K u A).eval G.cut = ∑ x ∈ A, (G.subtract K).w u x := by
  rw [nbrMassQuery, residualCross_eval G K hK Finset.disjoint_sdiff, WeightedGraph.cross,
    Finset.sum_singleton]
  apply Finset.sum_subset Finset.sdiff_subset
  intro x hx hn
  have : x = u := by simpa [Finset.mem_sdiff, hx] using hn
  subst this
  exact (G.subtract K).diag x

/-- The first position along `L` of a neighbour of `u` in `G.subtract K`. -/
def firstNbrTree (K : WeightedGraph V) (u : V) (L : List V) :
    DTree (Finset V) ℝ ℕ (searchDepth V * 3) :=
  (searchFirst L (searchDepth V) 0 L.length).substitute (nbrMassQuery K u)

/-- The average path incidence, from the cached degrees and the explicit `K`. -/
def pathTarget (deg : V → ℕ) (K : WeightedGraph V) (π : List V) : ℝ :=
  (∑ p ∈ π.toFinset, ((deg p : ℝ) - K.degree p)) / Fintype.card V

/-- A vertex with at least the average number of path neighbours in `G.subtract K`. -/
def pathCenterTree (deg : V → ℕ) (K : WeightedGraph V) (π : List V) :
    DTree (Finset V) ℝ (Option V) (searchDepth V * 7) :=
  (searchAverage (searchDepth V) Finset.univ (pathTarget deg K π)).substitute
    (incidenceTree K (fun v => (deg v : ℝ)) π.toFinset)

/-- Splice `π[0..i] → u → π[j..]`. -/
def splice (π : List V) (i j : ℕ) (u : V) : List V := π.take (i + 1) ++ u :: π.drop j

/-- One shortcut: a centre, its first and last path neighbours, splice, loop erasure. -/
def shortcutStep (deg : V → ℕ) (K : WeightedGraph V) (π : List V) : Prog (Finset V) ℝ (List V) :=
  (liftDTree (pathCenterTree deg K π)).bind fun ou => match ou with
    | none => .pure π
    | some u => (liftDTree (firstNbrTree K u π)).bind fun i =>
        (liftDTree (firstNbrTree K u π.reverse)).map fun j' =>
          loopErase (splice π i (π.length - 1 - j') u)

theorem shortcutStep_cost_le (deg : V → ℕ) (K : WeightedGraph V) (π : List V)
    (read : Finset V → ℝ) : Prog.cost read (shortcutStep deg K π) ≤ 13 * searchDepth V := by
  have h1 := liftDTree_cost_le (pathCenterTree deg K π) read
  unfold shortcutStep
  rw [Prog.cost_bind]
  cases ou : Prog.eval read (liftDTree (pathCenterTree deg K π)) with
  | none => simp only [Prog.cost_pure]; omega
  | some u =>
      simp only [Prog.cost_bind, Prog.cost_map]
      have h2 := liftDTree_cost_le (firstNbrTree K u π) read
      have h3 := liftDTree_cost_le (firstNbrTree K u π.reverse) read
      omega

end
end CutQueryComplexity.BoundedFlowMinCut

namespace CutQueryComplexity.BoundedFlowMinCut
noncomputable section
open scoped Classical
open WeightedGraph Certificate CanonicalST DirectedUnitST.Repair GHReduction

variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- The splice is a walk along `R` with the ends of `π`, when `π` is. -/
theorem splice_spec {R : V → V → Prop} {π : List V} (hne : π ≠ []) (hc : π.IsChain R) {i j : ℕ}
    (hi : i < π.length) (hj : j < π.length) {u : V} (hin : R π[i] u) (hout : R u π[j]) :
    ∃ h : splice π i j u ≠ [], (splice π i j u).head h = π.head hne ∧
      (splice π i j u).getLast h = π.getLast hne ∧ (splice π i j u).IsChain R ∧
      (splice π i j u).length = i + 2 + (π.length - j) := by
  have h1 : π.take (i + 1) ≠ [] := by simp [hne]
  have h2 : π.drop j ≠ [] := by simp; omega
  generalize hW : splice π i j u = W
  rw [splice] at hW
  subst hW
  refine ⟨by simp, ?_, ?_, ?_, by simp; omega⟩
  · rw [List.head_append_of_ne_nil h1, List.head_take]
  · rw [List.getLast_append_of_ne_nil _ (List.cons_ne_nil _ _), List.getLast_cons h2,
      List.getLast_drop]
  · apply List.IsChain.append (hc.take (i + 1))
    · rw [List.isChain_cons]
      refine ⟨fun y hy => ?_, hc.drop j⟩
      rw [List.head?_drop, List.getElem?_eq_getElem hj] at hy
      simp only [Option.mem_def, Option.some.injEq] at hy
      rw [← hy]
      exact hout
    · intro x hx y hy
      rw [List.getLast?_take, ite_eq_right (Nat.succ_ne_zero i), Nat.add_sub_cancel,
        List.getElem?_eq_getElem hi, Option.some_or] at hx
      simp only [Option.mem_def, Option.some.injEq, List.head?_cons] at hx hy
      rw [← hx, ← hy]
      exact hin

theorem unusedGraph_unit {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G) {s t : V} {i : ℝ}
    {f : V → V → ℝ} (hf : Augmentation.FlowSpec G s t i f) :
    AllPairsAudit.Unweighted (unusedGraph G f) := by
  intro u v
  change max 0 (G.w u v - (Reachability.usedGraph f).w u v) = 0 ∨
    max 0 (G.w u v - (Reachability.usedGraph f).w u v) = 1
  rw [Reachability.usedGraph_weight hG hf]
  have hle := hf.1.2 u v
  rcases hf.unit_values hG u v with h | h | h <;> rcases hG u v with hw | hw <;>
    simp_all

theorem usedCount_nonneg (f : V → V → ℝ) : 0 ≤ usedCount f := by
  simp only [usedCount, WeightedGraph.edgeMass]
  have : 0 ≤ ∑ u, ∑ v, (Reachability.usedGraph f).w u v :=
    Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => (Reachability.usedGraph f).nonneg u v
  positivity

theorem sum_degree_usedGraph (f : V → V → ℝ) :
    ∑ v, (Reachability.usedGraph f).degree v = 2 * usedCount f := by
  simp only [usedCount, WeightedGraph.edgeMass, WeightedGraph.degree]
  ring

/-- **One shortcut.** On an honest oracle, a too-long simple augmenting path is
replaced by a simple augmenting path at most `1 - 3d/(8n)` times as long. -/
theorem shortcutStep_spec {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G) {d : ℕ}
    (hδ : ∀ v, d ≤ natDegree G v) {deg : V → ℕ} (hdeg : ∀ v, deg v = natDegree G v)
    {s t : V} {i : ℝ} {f : V → V → ℝ} (hf : Augmentation.FlowSpec G s t i f) {π : List V}
    (hπ : IsAugPath G f s t π)
    (hlong : 8 * ((Fintype.card V : ℝ) + usedCount f) < d * ((π.length : ℝ) - 1)) :
    let π' := Prog.eval G.cut (shortcutStep deg (Reachability.usedGraph f) π)
    IsAugPath G f s t π' ∧ π'.length < π.length ∧
      (8 * Fintype.card V : ℝ) * π'.length ≤ (8 * Fintype.card V - 3 * d) * π.length := by
  intro π'
  set n := Fintype.card V
  set K := Reachability.usedGraph f
  set H := unusedGraph G f
  set r := π.length
  set q := usedCount f
  have hK : ∀ u v, K.w u v ≤ G.w u v := Reachability.usedGraph_le hG hf
  have hH : AllPairsAudit.Unweighted H := unusedGraph_unit hG hf
  have hr1 : 1 ≤ r := List.length_pos_iff.mpr hπ.ne_nil
  have hnpos : 0 < n := Fintype.card_pos_iff.mpr ⟨s⟩
  set P := π.toFinset
  have hPcard : P.card = r := List.toFinset_card_of_nodup hπ.nodup
  have hrn : r ≤ n := hPcard ▸ Finset.card_le_univ P
  -- the centre
  set wt : V → ℝ := fun v => ∑ p ∈ P, H.w v p
  have hdegR : ∀ v, ((deg v : ℕ) : ℝ) = G.degree v := fun v => by
    rw [hdeg, degree_eq_natDegree hG]
  have hsumwt : subsetSum wt Finset.univ = ∑ p ∈ P, ((deg p : ℝ) - K.degree p) := by
    simp only [subsetSum, wt]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    rw [hdegR, ← degree_subtract G K hK]
    exact Finset.sum_congr rfl (fun v _ => (G.subtract K).symm v p)
  have hav : pathTarget deg K π * (Finset.univ : Finset V).card ≤ subsetSum wt Finset.univ := by
    rw [hsumwt, pathTarget, Finset.card_univ, div_mul_cancel₀ _ (by exact_mod_cast hnpos.ne')]
  have : Nonempty V := ⟨s⟩
  obtain ⟨u, hu, -, hwu⟩ := searchAverage_correct wt (searchDepth V) Finset.univ
    (pathTarget deg K π) (card_le_pow_searchDepth _) Finset.univ_nonempty hav
  have hcenter : (pathCenterTree deg K π).eval G.cut = some u := by
    rw [pathCenterTree, DTree.eval_substitute]
    have hread : (fun A => (incidenceTree K (fun v => (deg v : ℝ)) P A).eval G.cut) = subsetSum wt := by
      funext A
      rw [incidenceTree_eval G K hK _ hdegR]
      rfl
    rw [hread, hu]
  -- the centre has many path neighbours
  have htarget : ((r : ℝ) * d - 2 * q) / n ≤ pathTarget deg K π := by
    rw [pathTarget]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [Finset.sum_sub_distrib]
    have h1 : (r : ℝ) * d ≤ ∑ p ∈ P, (deg p : ℝ) := by
      have : ∑ p ∈ P, (d : ℝ) ≤ ∑ p ∈ P, (deg p : ℝ) :=
        Finset.sum_le_sum (fun p _ => by rw [hdeg]; exact_mod_cast hδ p)
      simpa [hPcard, mul_comm] using this
    have h2 : ∑ p ∈ P, K.degree p ≤ 2 * q := by
      rw [← sum_degree_usedGraph f]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ P)
        (fun v _ _ => Finset.sum_nonneg (fun u _ => K.nonneg v u))
    linarith
  have hq0 : 0 ≤ q := usedCount_nonneg f
  have hdpos : (0 : ℝ) < d := by
    by_contra h
    have : (d : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg d)
    rw [this, zero_mul] at hlong
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hrd : (8 : ℝ) * n < r * d := by
    have : (d : ℝ) * ((r : ℝ) - 1) ≤ r * d := by nlinarith
    linarith
  have hcpos : 0 < wt u := by
    have : 0 < ((r : ℝ) * d - 2 * q) / n := by
      apply div_pos _ (by exact_mod_cast hnpos)
      linarith
    linarith
  -- the neighbours of the centre along the path
  have hHu : ∀ x, (G.subtract K).w u x = H.w u x := fun x => rfl
  have hfirstEval : ∀ L : List V, (firstNbrTree K u L).eval G.cut =
      (searchFirst L (searchDepth V) 0 L.length).eval (fun A => ∑ x ∈ A, H.w u x) := by
    intro L
    rw [firstNbrTree, DTree.eval_substitute]
    congr 1
    funext A
    exact nbrMassQuery_eval G K hK u A
  have hHnn : ∀ x, 0 ≤ H.w u x := fun x => H.nonneg u x
  have hexists : ∃ m < r, ∃ h : m < r, 0 < H.w u π[m] := by
    by_contra hno
    have hle : ∀ p ∈ P, H.w u p ≤ 0 := by
      intro p hp
      by_contra hpos
      obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hp)
      exact hno ⟨m, hm, hm, lt_of_not_ge hpos⟩
    have : wt u ≤ 0 := Finset.sum_nonpos hle
    linarith
  have hsearch : ∀ L : List V, L.length ≤ n → (∃ m < L.length, ∃ h : m < L.length, 0 < H.w u L[m]) →
      ∃ h : (firstNbrTree K u L).eval G.cut < L.length,
        0 < H.w u L[(firstNbrTree K u L).eval G.cut] ∧
        ∀ m < (firstNbrTree K u L).eval G.cut, ∀ h' : m < L.length, H.w u L[m] = 0 := by
    intro L hL hex
    rw [hfirstEval L]
    have hpow := card_le_pow_searchDepth (Finset.univ : Finset V)
    rw [Finset.card_univ] at hpow
    exact searchFirst_correct (fun x => H.w u x) hHnn L (searchDepth V) 0 L.length
      (by obtain ⟨m, hm, -⟩ := hex; omega) le_rfl (by omega)
      (fun m hm => absurd hm (Nat.not_lt_zero m)) hex
  -- the first neighbour
  obtain ⟨hi_lt, hi_pos, hi_first⟩ := hsearch π hrn hexists
  set i := (firstNbrTree K u π).eval G.cut with hi_def
  -- the last neighbour, as the first one along the reversed path
  have hexists' : ∃ m < π.reverse.length, ∃ h : m < π.reverse.length, 0 < H.w u π.reverse[m] := by
    obtain ⟨m, hm, hm', hpos⟩ := hexists
    refine ⟨r - 1 - m, by simp; omega, by simp; omega, ?_⟩
    rw [List.getElem_reverse]
    convert hpos using 3
    have : r = π.length := rfl
    omega
  obtain ⟨hj_lt', hj_pos', hj_first'⟩ := hsearch π.reverse (by simpa using hrn) hexists'
  set j' := (firstNbrTree K u π.reverse).eval G.cut with hj'_def
  have hj'r : j' < r := by simpa using hj_lt'
  set j := r - 1 - j' with hj_def
  have hj_lt : j < r := by omega
  have hj_pos : 0 < H.w u π[j] := by
    rw [List.getElem_reverse] at hj_pos'
    exact hj_pos'
  have hj_last : ∀ m, j < m → ∀ h : m < r, H.w u π[m] = 0 := by
    intro m hm h
    have := hj_first' (r - 1 - m) (by omega) (by simp; omega)
    rw [List.getElem_reverse] at this
    convert this using 3
    have : r = π.length := rfl
    omega
  have hij : i ≤ j := by
    by_contra hji
    have := hj_last i (by omega) hi_lt
    linarith
  -- the step's output
  have hπ'eq : π' = loopErase (splice π i j u) := by
    show Prog.eval G.cut (shortcutStep deg K π) = _
    simp only [shortcutStep, Prog.eval_bind, liftDTree_eval, hcenter, Prog.eval_map]
    rfl
  -- the spliced walk and its loop erasure
  have hres_in : Res G f π[i] u := by
    rw [Res, Reachability.residual_iff hG hf]
    right
    show 0 < H.w π[i] u
    rw [H.symm]
    exact hi_pos
  have hres_out : Res G f u π[j] := by
    rw [Res, Reachability.residual_iff hG hf]
    exact Or.inr hj_pos
  obtain ⟨hWne, hWhead, hWlast, hWchain, hWlen⟩ :=
    splice_spec hπ.ne_nil hπ.chain hi_lt hj_lt hres_in hres_out
  obtain ⟨hne', hh', hl', hnd', hc', hlen'⟩ := loopErase_spec (splice π i j u) hWne hWchain
  have hAug : IsAugPath G f s t π' := by
    rw [hπ'eq]
    exact ⟨hne', hh'.trans (hWhead.trans hπ.head), hl'.trans (hWlast.trans hπ.last), hnd', hc'⟩
  -- the centre's path neighbours lie between positions `i` and `j`
  set c := j + 1 - i with hc_def
  have hcount : wt u ≤ c := by
    set P' := (Finset.Icc i j).image (fun m => π[m]?.getD s) with hP'
    have hzero : ∀ p ∈ P ∪ P', p ∉ P' → H.w u p = 0 := by
      intro p hp hpn
      rcases Finset.mem_union.mp hp with hp | hp
      · obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hp)
        by_cases hmi : m < i
        · exact hi_first m hmi hm
        by_cases hmj : j < m
        · exact hj_last m hmj hm
        exact absurd (Finset.mem_image.mpr ⟨m, Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
          by simp [hm]⟩) hpn
      · exact absurd hp hpn
    calc wt u = ∑ p ∈ P, H.w u p := rfl
      _ ≤ ∑ p ∈ P ∪ P', H.w u p :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun x _ _ => hHnn x)
      _ = ∑ p ∈ P', H.w u p := (Finset.sum_subset Finset.subset_union_right hzero).symm
      _ ≤ ∑ p ∈ P', (1 : ℝ) := Finset.sum_le_sum (fun p _ => by
          rcases hH u p with h | h <;> simp [h])
      _ = (P'.card : ℝ) := by simp
      _ ≤ ((Finset.Icc i j).card : ℝ) := by exact_mod_cast Finset.card_image_le
      _ = c := by rw [Nat.card_Icc]
  -- the length bound
  have hlenle : π'.length ≤ (splice π i j u).length := by rw [hπ'eq]; exact hlen'
  have hnat : π'.length + c ≤ r + 3 := by
    have hr : r = π.length := rfl
    rw [hWlen] at hlenle
    omega
  have hreal : (π'.length : ℝ) + wt u ≤ r + 3 := by
    have : ((π'.length + c : ℕ) : ℝ) ≤ ((r + 3 : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast at this
    linarith
  have hnc : (r : ℝ) * d - 2 * q ≤ n * wt u := by
    have := htarget.trans hwu
    rw [div_le_iff₀ (by exact_mod_cast hnpos)] at this
    linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h8 := mul_le_mul_of_nonneg_left hreal (by linarith : (0 : ℝ) ≤ 8 * n)
  have hmain : (8 * n : ℝ) * π'.length ≤ (8 * n - 3 * d) * r := by linarith
  refine ⟨hAug, ?_, hmain⟩
  have hlt : (π'.length : ℝ) < r := by
    by_contra hge
    have := mul_le_mul_of_nonneg_left (not_lt.mp hge) (by linarith : (0 : ℝ) ≤ 8 * n)
    linarith
  exact_mod_cast hlt

/-- Shortcut while the path is long, `d (|π| - 1) > 8 (n + |K_f|)`; the test reads only
the public degree bound, the vertex count and the flow. -/
def shortcutLoop (deg : V → ℕ) (d : ℕ) (f : V → V → ℝ) : ℕ → List V → Prog (Finset V) ℝ (List V)
  | 0, π => .pure π
  | fuel + 1, π =>
      if 8 * ((Fintype.card V : ℝ) + usedCount f) < d * ((π.length : ℝ) - 1) then
        (shortcutStep deg (Reachability.usedGraph f) π).bind (shortcutLoop deg d f fuel)
      else .pure π

/-- On every oracle, the loop spends at most `13 ⌈log₂ n⌉` queries per unit of fuel. -/
theorem shortcutLoop_cost_le_fuel (deg : V → ℕ) (d : ℕ) (f : V → V → ℝ) (read : Finset V → ℝ) :
    ∀ (fuel : ℕ) (π : List V),
      Prog.cost read (shortcutLoop deg d f fuel π) ≤ 13 * searchDepth V * fuel := by
  intro fuel
  induction fuel with
  | zero => intro π; simp [shortcutLoop]
  | succ fuel ih =>
      intro π
      by_cases hlong : 8 * ((Fintype.card V : ℝ) + usedCount f) < d * ((π.length : ℝ) - 1)
      · rw [shortcutLoop, ite_eq_left hlong, Prog.cost_bind]
        have h1 := shortcutStep_cost_le deg (Reachability.usedGraph f) π read
        have h2 := ih (Prog.eval read (shortcutStep deg (Reachability.usedGraph f) π))
        rw [Nat.mul_succ]
        omega
      · rw [shortcutLoop, ite_eq_right hlong, Prog.cost_pure]
        exact Nat.zero_le _

/-- **Path shortening (Lemma 4.3).** Starting from a simple augmenting path, the loop
returns a simple augmenting path with `d (|π'| - 1) ≤ 8 (n + |K_f|)`, after at most
`(8n / 3d) ln |π| + 1` shortcuts of `13 ⌈log₂ n⌉` queries each. -/
theorem shortcutLoop_spec {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G) {d : ℕ}
    (hδ : ∀ v, d ≤ natDegree G v) {deg : V → ℕ} (hdeg : ∀ v, deg v = natDegree G v)
    {s t : V} {i : ℝ} {f : V → V → ℝ} (hf : Augmentation.FlowSpec G s t i f) :
    ∀ (fuel : ℕ) (π : List V), IsAugPath G f s t π → π.length ≤ fuel + 1 →
      let π' := Prog.eval G.cut (shortcutLoop deg d f fuel π)
      IsAugPath G f s t π' ∧ π'.length ≤ π.length ∧
        (d : ℝ) * ((π'.length : ℝ) - 1) ≤ 8 * ((Fintype.card V : ℝ) + usedCount f) ∧
        (Prog.cost G.cut (shortcutLoop deg d f fuel π) : ℝ) ≤
          13 * searchDepth V * domPotential (8 * Fintype.card V) (3 * d) π.length := by
  have hq0 := usedCount_nonneg f
  have hn0 : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ 13 * searchDepth V := by positivity
  intro fuel
  induction fuel with
  | zero =>
      intro π hπ hlen
      refine ⟨hπ, le_rfl, ?_, ?_⟩
      · have : ((π.length : ℝ) - 1) ≤ 0 := by
          have : (π.length : ℝ) ≤ 1 := by exact_mod_cast hlen
          linarith
        have := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg d) this
        simp only [shortcutLoop, Prog.eval_pure]
        linarith
      · simp only [shortcutLoop, Prog.cost_pure, Nat.cast_zero]
        exact mul_nonneg hk0 (domPotential_nonneg _ _ _)
  | succ fuel ih =>
      intro π hπ hlen
      by_cases hlong : 8 * ((Fintype.card V : ℝ) + usedCount f) < d * ((π.length : ℝ) - 1)
      · obtain ⟨hπ1, hlt1, hratio⟩ := shortcutStep_spec hG hδ hdeg hf hπ hlong
        set π1 := Prog.eval G.cut (shortcutStep deg (Reachability.usedGraph f) π)
        obtain ⟨hA, hL, hS, hC⟩ := ih π1 hπ1 (by omega)
        have hdpos : 0 < d := by
          by_contra h
          have : d = 0 := by omega
          rw [this, Nat.cast_zero, zero_mul] at hlong
          linarith
        have heval : Prog.eval G.cut (shortcutLoop deg d f (fuel + 1) π) =
            Prog.eval G.cut (shortcutLoop deg d f fuel π1) := by
          rw [shortcutLoop, ite_eq_left hlong, Prog.eval_bind]
        have hcost : Prog.cost G.cut (shortcutLoop deg d f (fuel + 1) π) =
            Prog.cost G.cut (shortcutStep deg (Reachability.usedGraph f) π) +
              Prog.cost G.cut (shortcutLoop deg d f fuel π1) := by
          rw [shortcutLoop, ite_eq_left hlong, Prog.cost_bind]
        refine ⟨heval ▸ hA, by rw [heval]; omega, heval ▸ hS, ?_⟩
        have hstep := domPotential_step (n := 8 * Fintype.card V) (d := 3 * d)
          (a := π.length) (a' := π1.length) (by omega) (by omega) (by push_cast; exact hratio)
        have hc1 : (Prog.cost G.cut (shortcutStep deg (Reachability.usedGraph f) π) : ℝ) ≤
            13 * searchDepth V := by
          exact_mod_cast shortcutStep_cost_le deg _ π G.cut
        rw [hcost, Nat.cast_add]
        have := mul_le_mul_of_nonneg_left hstep hk0
        linarith
      · have heval : shortcutLoop deg d f (fuel + 1) π = .pure π := by
          rw [shortcutLoop, ite_eq_right hlong]
        rw [heval, Prog.eval_pure, Prog.cost_pure, Nat.cast_zero]
        exact ⟨hπ, le_rfl, not_lt.mp hlong, mul_nonneg hk0 (domPotential_nonneg _ _ _)⟩

/-- The shortening cost in the plan's form, `O(⌈n/d⌉ L²)`: at most
`13 L (3 n L / d + 1)` queries, with `L = logFactor n`. -/
theorem shortcutLoop_cost_le {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G) {d : ℕ}
    (hδ : ∀ v, d ≤ natDegree G v) {deg : V → ℕ} (hdeg : ∀ v, deg v = natDegree G v)
    {s t : V} {i : ℝ} {f : V → V → ℝ} (hf : Augmentation.FlowSpec G s t i f) {fuel : ℕ}
    {π : List V} (hπ : IsAugPath G f s t π) (hfuel : π.length ≤ fuel + 1) :
    (Prog.cost G.cut (shortcutLoop deg d f fuel π) : ℝ) ≤
      13 * logFactor (Fintype.card V) *
        (3 * Fintype.card V * logFactor (Fintype.card V) / d + 1) := by
  obtain ⟨-, -, -, hC⟩ := shortcutLoop_spec hG hδ hdeg hf fuel π hπ hfuel
  refine hC.trans ?_
  set n := Fintype.card V
  set L := logFactor n
  have hk : (searchDepth V : ℝ) ≤ L := by
    exact_mod_cast (Nat.le_succ _).trans searchDepth_add_one_le_logFactor
  have hr0 : π.length ≠ 0 := by
    have := List.length_pos_iff.mpr hπ.ne_nil
    omega
  have hrn : π.length ≤ n := hπ.nodup.length_le_card
  have hlog0 : 0 ≤ Real.log π.length :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr0)
  have hlogL : Real.log π.length ≤ L := by
    have h1 : Real.log π.length ≤ Real.log n :=
      Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hr0) (by exact_mod_cast hrn)
    have h2 : Nat.clog 2 n ≤ L :=
      (Nat.clog_mono_right 2 (by omega : n ≤ 2 * n + 2)).trans (Nat.le_succ _)
    have h3 := real_log_le_clog n
    have h4 : ((Nat.clog 2 n : ℕ) : ℝ) ≤ L := by exact_mod_cast h2
    linarith
  have hΦ : domPotential (8 * n) (3 * d) π.length ≤ 3 * n * L / d + 1 := by
    rw [domPotential, ite_eq_right hr0]
    push_cast
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      simp
    · have hdR : (0 : ℝ) < d := by exact_mod_cast hd
      have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hcoef : 0 ≤ (8 * n : ℝ) / (3 * d) := by positivity
      have h1 : (8 * n : ℝ) / (3 * d) * Real.log π.length ≤ (8 * n : ℝ) / (3 * d) * L :=
        mul_le_mul_of_nonneg_left hlogL hcoef
      have h2 : (8 * n : ℝ) / (3 * d) * L = 8 / 9 * (3 * n * L / d) := by
        field_simp
        ring
      have h3 : 0 ≤ 3 * n * (L : ℝ) / d := by positivity
      linarith
  have hk0 : (0 : ℝ) ≤ searchDepth V := Nat.cast_nonneg _
  have hΦ0 := domPotential_nonneg (8 * n) (3 * d) π.length
  calc (13 : ℝ) * searchDepth V * domPotential (8 * n) (3 * d) π.length
      ≤ 13 * L * domPotential (8 * n) (3 * d) π.length := by gcongr
    _ ≤ 13 * L * (3 * n * L / d + 1) := by gcongr

end
end CutQueryComplexity.BoundedFlowMinCut
