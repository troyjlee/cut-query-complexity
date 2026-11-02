import CutQueryComplexity.DetMinCut.Budget
import CutQueryComplexity.Hierarchy.GuardConstant

/-! # The log-seven algorithm (log-seven plan, Milestones 4–5)

The main loop of `DetMinCut.Main` with three changes:

* phases use a constant-quality guard `ρ₀` (`ConstantCutGuard ρ₀`) and the tuned parameter
  `k = kLog7 N`;
* quotients with fewer than `thrN0` classes are reconstructed and minimized offline
  (`fallback`);
* the cost is paid by the halving potential `2 K N` with `K = cLog7 ⌊√n⌋ L(n)^7`, instead of
  `fuel · phaseMax`: a phase on `N` classes costs at most `K N`, and the next phase runs on at
  most `N / 2` classes.

`deterministic_mincut_log7_of_hierarchyBound_of_constantGuard` is Theorem 1 with the paper's
exponent: conditional on `HierarchyBound a h` with `a(r) ≤ A₀ L(r)³` and on
`ConstantCutGuard ρ₀`, one decision tree with `O(n (⌊√n⌋ + 1) L(n)^7)` queries returns a minimum
cut of every nonnegative weighted graph.
-/

namespace CutQueryComplexity
namespace DetMinCut

open TwoRespecting WeightedGraph Search Search.Comp Discovery Hierarchy Finset

/-! ## The threshold and the finite-size fallback -/

/-- The fixed finite-size threshold, chosen from the proved eventual inequality. -/
noncomputable def thrN0 : ℕ := Classical.choose exists_logL7_threshold

theorem thrN0_spec : 16 ≤ thrN0 ∧ ∀ N, thrN0 ≤ N → logL N ^ 7 ≤ Nat.sqrt N :=
  Classical.choose_spec exists_logL7_threshold

section Fallback

variable {W : Type} [Fintype W] [DecidableEq W]

open Classical in
/-- An optimal shore of an explicit graph, chosen offline (`∅` if there is none). -/
noncomputable def bestCut (Q : WeightedGraph W) : Finset W :=
  if h : (properShores W).Nonempty then Classical.choose (exists_mem_eq_inf' h Q.cut) else ∅

theorem bestCut_spec (Q : WeightedGraph W) (hn : 2 ≤ Fintype.card W) : IsMinCut Q (bestCut Q) := by
  classical
  have hne : (properShores W).Nonempty := by
    obtain ⟨v⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card W by omega)
    exact ⟨{v}, (mem_properShores _).mpr (properShore_singleton v hn)⟩
  have hs := Classical.choose_spec (exists_mem_eq_inf' hne Q.cut)
  simp only [bestCut, dite_eq_left hne]
  refine ⟨(mem_properShores _).mp hs.1, fun T hT => ?_⟩
  rw [← hs.2]
  exact inf'_le _ ((mem_properShores T).mpr hT)

end Fallback

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Reconstruct the current quotient and minimize its cuts offline. -/
noncomputable def fallback (r : V → V) : Comp (Finset V) ℝ (Finset V) :=
  (mapQ (pull (proj r)) (@learnContract (Cls r) _ (Cls r) _ (clsOrder r) id univ)).map
    fun Q => pull (proj r) (bestCut Q)

theorem pull_id {W : Type} [Fintype W] [DecidableEq W] (T : Finset W) : pull id T = T := by
  ext; simp

theorem fallback_spec (G : WeightedGraph V) {st : St V} (hI : Inv G st) :
    IsMinCut G ((fallback st.r).eval G.cut) ∧
      (fallback st.r).cost G.cut ≤
        Fintype.card (Cls st.r) + Fintype.card (Cls st.r) * Fintype.card (Cls st.r) := by
  have hcutq : G.cut ∘ pull (proj st.r) = (quot G st.r).cut := by
    funext T; exact (cut_contract G (proj st.r) T).symm
  simp only [fallback, eval_map, cost_map, eval_mapQ, cost_mapQ, hcutq]
  have hQ := @learnContract_eval (Cls st.r) _ _ (Cls st.r) _ _ (clsOrder st.r) (quot G st.r) id univ
    (fun v => mem_univ _)
  have hc := @learnContract_cost (Cls st.r) _ _ (Cls st.r) _ (clsOrder st.r) (quot G st.r) id univ
  rw [card_univ] at hc
  refine ⟨?_, hc⟩
  rw [hQ]
  apply isMinCut_pull hI
  have hb := bestCut_spec ((quot G st.r).contract id) hI.two_le
  refine ⟨hb.1, fun T hT => ?_⟩
  have := hb.2 T hT
  rwa [cut_contract (quot G st.r) id, cut_contract (quot G st.r) id, pull_id, pull_id] at this

/-! ## The main loop -/

variable {a : ℕ → ℝ} {h : ℕ → ℕ}

/-- **The log-seven main loop.** -/
noncomputable def mainLoop7 (hb : HierarchyBound a h) (ha : ∀ r, 1 ≤ a r) (ρ0 : ℝ)
    (hρ0 : 1 ≤ ρ0) : ℕ → St V → Comp (Finset V) ℝ (Finset V)
  | 0, st => .pure st.wit
  | fuel + 1, st =>
    if hstop : st.U ≤ 0 ∨ Fintype.card (Cls st.r) ≤ 2 then .pure st.wit
    else if Fintype.card (Cls st.r) < thrN0 then fallback st.r
    else
      (mapQ (pull (proj st.r)) (phaseG hb ha (fun _ => ρ0) (fun _ => hρ0)
        (fun c => st.deg c.val) st.U (kLog7 (Fintype.card (Cls st.r)))
        (Classical.choice (Fintype.card_pos_iff.mp (by omega))))).bind fun out =>
        match out with
        | .skel H => (mapQ (pull (proj st.r)) (@skeletonMinCut _ _ _ (clsOrder st.r) H)).map
            (pull (proj st.r))
        | .halve S val =>
            (normalize (Fintype.card V) ⟨st.r, st.deg, val, pull (proj st.r) S⟩).bind
              (mainLoop7 hb ha ρ0 hρ0 fuel)

theorem mainLoop7_of_U_le (hb : HierarchyBound a h) (ha : ∀ r, 1 ≤ a r) {ρ0 : ℝ}
    (hρ0 : 1 ≤ ρ0) (G : WeightedGraph V) (fuel : ℕ) {st : St V} (hU : st.U ≤ 0) :
    (mainLoop7 hb ha ρ0 hρ0 fuel st).eval G.cut = st.wit ∧
      (mainLoop7 hb ha ρ0 hρ0 fuel st).cost G.cut = 0 := by
  cases fuel with
  | zero => simp [mainLoop7]
  | succ fuel => simp [mainLoop7, dite_eq_left (Or.inl hU : st.U ≤ 0 ∨ _)]

/-- The phase constant per class: `K = cLog7 ⌊√n⌋ L(n)^7`. -/
noncomputable def phaseK (A0 ρ0 : ℝ) (n : ℕ) : ℝ :=
  cLog7 A0 ρ0 * (Nat.sqrt n * (logL n : ℝ) ^ 7)

theorem cLog7_nonneg (A0 ρ0 : ℝ) : 0 ≤ cLog7 A0 ρ0 := by unfold cLog7; positivity

/-- **The log-seven main loop.** From a stopped state with `U ≤ 0` or fewer than `2^fuel`
classes, the output is a minimum cut, using at most
`2 K N + (2⌈log₂ n⌉ + 1) N + skelBound n + thrN0 + thrN0²` queries. -/
theorem mainLoop7_spec (hb : HierarchyBound a h) (ha : ∀ r, 1 ≤ a r) (hma : Monotone a)
    {A0 ρ0 : ℝ} (hρ0 : 1 ≤ ρ0) (hcg : ConstantCutGuard ρ0)
    (hA : ∀ r, a r ≤ A0 * (logL r : ℝ) ^ 3) (G : WeightedGraph V) :
    ∀ (fuel : ℕ) (st : St V), Inv G st → Stopped st →
      (st.U ≤ 0 ∨ Fintype.card (Cls st.r) < 2 ^ fuel) →
      IsMinCut G ((mainLoop7 hb ha ρ0 hρ0 fuel st).eval G.cut) ∧
      ((mainLoop7 hb ha ρ0 hρ0 fuel st).cost G.cut : ℝ) ≤
        2 * phaseK A0 ρ0 (Fintype.card V) * Fintype.card (Cls st.r) +
          (2 * Nat.clog 2 (Fintype.card V) + 1 : ℕ) * Fintype.card (Cls st.r) +
          skelBound (Fintype.card V) + (thrN0 + thrN0 * thrN0 : ℕ) := by
  have hK0 : 0 ≤ phaseK A0 ρ0 (Fintype.card V) := by
    unfold phaseK; have := cLog7_nonneg A0 ρ0; positivity
  intro fuel
  induction fuel with
  | zero =>
      intro st hI _ hsmall
      have hU : st.U ≤ 0 := by
        rcases hsmall with h0 | h0
        · exact h0
        · have := hI.two_le; rw [pow_zero] at h0; omega
      simp only [mainLoop7, eval_pure, cost_pure, Nat.cast_zero]
      exact ⟨isMinCut_zero hI hU, by positivity⟩
  | succ fuel ih =>
      intro st hI hst hsmall
      by_cases hstop : st.U ≤ 0 ∨ Fintype.card (Cls st.r) ≤ 2
      · simp only [mainLoop7, dite_eq_left hstop, eval_pure, cost_pure, Nat.cast_zero]
        refine ⟨?_, by positivity⟩
        rcases hstop with h0 | h0
        · exact isMinCut_zero hI h0
        · exact isMinCut_two hI h0
      have hnot := hstop
      push Not at hstop
      obtain ⟨hU, hN3⟩ := hstop
      have hNle := card_cls_le st.r
      by_cases hsmallN : Fintype.card (Cls st.r) < thrN0
      · -- the finite-size fallback
        simp only [mainLoop7, dite_eq_right hnot, ite_eq_left hsmallN]
        obtain ⟨hmin, hc⟩ := fallback_spec G hI
        refine ⟨hmin, ?_⟩
        have hc' : (fallback st.r).cost G.cut ≤ thrN0 + thrN0 * thrN0 :=
          hc.trans (Nat.add_le_add hsmallN.le (Nat.mul_le_mul hsmallN.le hsmallN.le))
        have hcR : ((fallback st.r).cost G.cut : ℝ) ≤ ((thrN0 + thrN0 * thrN0 : ℕ) : ℝ) := by
          exact_mod_cast hc'
        have : (0 : ℝ) ≤ 2 * phaseK A0 ρ0 (Fintype.card V) * Fintype.card (Cls st.r) := by
          positivity
        have : (0 : ℝ) ≤ ((2 * Nat.clog 2 (Fintype.card V) + 1 : ℕ) : ℝ) * Fintype.card (Cls st.r) :=
          by positivity
        have : (0 : ℝ) ≤ skelBound (Fintype.card V) := Nat.cast_nonneg _
        linarith
      push Not at hsmallN
      have hcutq : G.cut ∘ pull (proj st.r) = (quot G st.r).cut := by
        funext T; exact (cut_contract G (proj st.r) T).symm
      simp only [mainLoop7, dite_eq_right hnot, ite_eq_right (not_lt.mpr hsmallN), eval_bind,
        cost_bind, eval_mapQ, cost_mapQ, hcutq, hI.quot_degree]
      obtain ⟨h16, hthr⟩ := thrN0_spec
      set N := Fintype.card (Cls st.r) with hNdef
      have hN16 : 16 ≤ N := h16.trans hsmallN
      have h7 := hthr N hsmallN
      have hdegq : ∀ c, (quot G st.r).degree c ≤ ((N : ℝ) - 1) * st.U := by
        intro c
        rcases hst with h0 | h0
        · linarith
        · rw [← congrFun hI.quot_degree c]; exact h0 c
      have hk2 : 2 ≤ kLog7 N := two_le_kLog7 N
      have hkN : kLog7 N ≤ 8 * N := by
        have := kLog7_le_sqrt (N := N) (Nat.le_sqrt.mpr (by omega))
        have := Nat.sqrt_le_self N
        omega
      set v0 : Cls st.r := Classical.choice (Fintype.card_pos_iff.mp (by omega))
      have hρf : ∀ M : ℕ, 1 ≤ (fun _ : ℕ => ρ0) M := fun _ => hρ0
      obtain ⟨hok, hpcost⟩ := phase_specG hb ha hma hρf
        (cap := (range (3 * N + 2)).sup h) (le_sup (mem_range.mpr (by omega)))
        (fun m hm => le_sup (mem_range.mpr (by omega)))
        (fun P hlc _ => Hier.ConstantCutGuard.guardFor hcg hlc) (quot G st.r) (by omega) hU hdegq hk2 hkN v0
      -- the phase costs at most `K N`
      have hPB : (Comp.cost (quot G st.r).cut
          (phaseG hb ha (fun _ => ρ0) hρf (quot G st.r).degree st.U (kLog7 N) v0) : ℝ) ≤
          phaseK A0 ρ0 (Fintype.card V) * N := by
        refine hpcost.trans ((phaseBound_log7 ha hρ0 hA hN16 h7).trans ?_)
        unfold phaseK
        have hs : (Nat.sqrt N : ℝ) ≤ Nat.sqrt (Fintype.card V) := by
          exact_mod_cast Nat.sqrt_le_sqrt hNle
        have hL : (logL N : ℝ) ≤ logL (Fintype.card V) := by exact_mod_cast logL_mono hNle
        have := cLog7_nonneg A0 ρ0
        have hL7 : (logL N : ℝ) ^ 7 ≤ (logL (Fintype.card V) : ℝ) ^ 7 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hL 7
        calc cLog7 A0 ρ0 * (N * Nat.sqrt N * (logL N : ℝ) ^ 7)
            ≤ cLog7 A0 ρ0 * (N * Nat.sqrt (Fintype.card V) * (logL (Fintype.card V) : ℝ) ^ 7) := by
              gcongr
          _ = cLog7 A0 ρ0 * (Nat.sqrt (Fintype.card V) * (logL (Fintype.card V) : ℝ) ^ 7) * N := by
              ring
      have hc0 : (0 : ℝ) ≤ ((2 * Nat.clog 2 (Fintype.card V) + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      have hFB : (0 : ℝ) ≤ ((thrN0 + thrN0 * thrN0 : ℕ) : ℝ) := Nat.cast_nonneg _
      rcases hout : (phaseG hb ha (fun _ => ρ0) hρf (quot G st.r).degree st.U (kLog7 N) v0).eval
          (quot G st.r).cut with H | ⟨S, val⟩
      · rw [hout] at hok
        simp only [PhaseOK] at hok
        simp only [eval_map, cost_map, eval_mapQ, cost_mapQ, hcutq]
        refine ⟨isMinCut_pull hI (@skeletonMinCut_correct _ _ _ (clsOrder st.r) (quot G st.r) H
          (by omega) hok), ?_⟩
        have hsk := @skeletonMinCut_cost _ _ _ (clsOrder st.r) (quot G st.r) H
        have hsk' : ((@skeletonMinCut _ _ _ (clsOrder st.r) H).cost (quot G st.r).cut : ℝ) ≤
            skelBound (Fintype.card V) := by
          exact_mod_cast hsk.trans (skelBound_mono hNle)
        push_cast
        have hFB' : (0 : ℝ) ≤ (thrN0 : ℝ) + thrN0 * thrN0 := by positivity
        have : (0 : ℝ) ≤ ((2 * Nat.clog 2 (Fintype.card V) + 1 : ℕ) : ℝ) * N := by positivity
        have : (0 : ℝ) ≤ phaseK A0 ρ0 (Fintype.card V) * N := by positivity
        nlinarith
      · rw [hout] at hok
        simp only [PhaseOK] at hok
        obtain ⟨hSp, hval, hvalU⟩ := hok
        simp only [eval_bind, cost_bind]
        set st1 : St V := ⟨st.r, st.deg, val, pull (proj st.r) S⟩ with hst1
        have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
        have hvalle : val ≤ st.U := by
          have : st.U / (4 * N) ≤ st.U := by
            have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN3
            rw [div_le_iff₀ (by positivity)]
            have : st.U * 1 ≤ st.U * (4 * N) := mul_le_mul_of_nonneg_left (by linarith) hU.le
            linarith
          linarith
        have hI1 : Inv G st1 := by
          refine ⟨hI.deg, sat_pull _ _, properShore_pull _ (proj_surjective _) hSp, ?_, ?_, hI.opt⟩
          · show G.cut (pull (proj st.r) S) = val
            rw [hval, cut_contract]
          · intro c; exact hvalle.trans (hI.U_le c)
        obtain ⟨hI2, hU2le, hst2, href2, hcard2, hncost⟩ :=
          normalize_spec G (Fintype.card V) st1 hI1 (by show N ≤ _; omega)
        set st2 := (normalize (Fintype.card V) st1).eval G.cut
        have hncostR : ((normalize (Fintype.card V) st1).cost G.cut : ℝ) +
            ((2 * Nat.clog 2 (Fintype.card V) + 1 : ℕ) : ℝ) * Fintype.card (Cls st2.r) ≤
            ((2 * Nat.clog 2 (Fintype.card V) + 1 : ℕ) : ℝ) * N := by
          exact_mod_cast hncost
        have hN2 : (0 : ℝ) ≤ Fintype.card (Cls st2.r) := Nat.cast_nonneg _
        by_cases hU2 : st2.U ≤ 0
        · -- the next call stops immediately
          obtain ⟨heval, hcost0⟩ := mainLoop7_of_U_le hb ha hρ0 G fuel hU2
          rw [heval, hcost0]
          refine ⟨isMinCut_zero hI2 hU2, ?_⟩
          push_cast at hncostR ⊢
          have hFB' : (0 : ℝ) ≤ (thrN0 : ℝ) + thrN0 * thrN0 := by positivity
          have : (0 : ℝ) ≤ phaseK A0 ρ0 (Fintype.card V) * N := by positivity
          have : (0 : ℝ) ≤ ((2 * Nat.clog 2 (Fintype.card V) + 1 : ℕ) : ℝ) *
              Fintype.card (Cls st2.r) := by positivity
          push_cast at this
          nlinarith
        · push Not at hU2
          have hstop2 : ∀ c : Cls st2.r,
              st2.deg c.val ≤ ((Fintype.card (Cls st2.r) : ℝ) - 1) * st2.U := by
            rcases hst2 with h0 | h0
            · linarith
            · exact h0
          have hhalf := halving G hI hI2 href2 hU hU2 hstop2 hU2le hvalU
          have hsmall2 : st2.U ≤ 0 ∨ Fintype.card (Cls st2.r) < 2 ^ fuel := by
            right
            have hlt : N < 2 ^ (fuel + 1) := by
              rcases hsmall with h0 | h0
              · linarith
              · exact h0
            rw [pow_succ] at hlt
            omega
          obtain ⟨hmin, hlcost⟩ := ih st2 hI2 hst2 hsmall2
          refine ⟨hmin, ?_⟩
          have hhalfR : 2 * (Fintype.card (Cls st2.r) : ℝ) ≤ N := by exact_mod_cast hhalf
          have hKhalf : 2 * phaseK A0 ρ0 (Fintype.card V) * Fintype.card (Cls st2.r) ≤
              phaseK A0 ρ0 (Fintype.card V) * N := by nlinarith
          push_cast at hncostR hlcost ⊢
          linarith

/-! ## The complete log-seven algorithm -/

/-- **The log-seven deterministic algorithm.** -/
noncomputable def detMinCut7 [Nonempty V] (hb : HierarchyBound a h) (ha : ∀ r, 1 ≤ a r)
    (ρ0 : ℝ) (hρ0 : 1 ≤ ρ0) : Comp (Finset V) ℝ (Finset V) :=
  (tabulate (fun v => ask ({v} : Finset V)) univ.toList).bind fun degs =>
    (normalize (Fintype.card V)
        (initSt (fun v => (degs v).getD 0) (argminOf fun v => (degs v).getD 0))).bind
      (mainLoop7 hb ha ρ0 hρ0 (Nat.log 2 (Fintype.card V) + 1))

/-- The query budget of the log-seven algorithm on `n` vertices. -/
noncomputable def detBudget7 (A0 ρ0 : ℝ) (n : ℕ) : ℕ :=
  ⌈(n : ℝ) + 2 * (((2 * Nat.clog 2 n + 1 : ℕ) : ℝ) * n) + 2 * phaseK A0 ρ0 n * n +
    skelBound n + (thrN0 + thrN0 * thrN0 : ℕ)⌉₊

/-- **Correctness and cost of the log-seven algorithm.** -/
theorem detMinCut7_spec [Nonempty V] (hb : HierarchyBound a h) (ha : ∀ r, 1 ≤ a r)
    (hma : Monotone a) {A0 ρ0 : ℝ} (hρ0 : 1 ≤ ρ0) (hcg : ConstantCutGuard ρ0)
    (hA : ∀ r, a r ≤ A0 * (logL r : ℝ) ^ 3) (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V) :
    IsMinCut G ((detMinCut7 hb ha ρ0 hρ0).eval G.cut) ∧
      (detMinCut7 hb ha ρ0 hρ0).cost G.cut ≤ detBudget7 A0 ρ0 (Fintype.card V) := by
  have hdegs : (fun v => ((tabulate (fun v => ask ({v} : Finset V)) univ.toList).eval G.cut v).getD 0)
      = G.degree := by
    funext v; simp [eval_tabulate, mem_toList, cut_singleton]
  simp only [detMinCut7, eval_bind, cost_bind, cost_tabulate, cost_ask, hdegs]
  set v0 := argminOf G.degree
  have hI0 := inv_initSt G hn (argminOf_spec G.degree)
  obtain ⟨hI1, -, hst1, -, hcard1, hncost⟩ := normalize_spec G (Fintype.card V) _ hI0
    (by show Fintype.card (Cls (id : V → V)) ≤ _; have := card_cls_le (id : V → V); omega)
  set st1 := (normalize (Fintype.card V) (initSt G.degree v0)).eval G.cut
  have hsmall : st1.U ≤ 0 ∨ Fintype.card (Cls st1.r) < 2 ^ (Nat.log 2 (Fintype.card V) + 1) :=
    Or.inr ((card_cls_le _).trans_lt (Nat.lt_pow_succ_log_self (by norm_num) _))
  obtain ⟨hmin, hcost⟩ := mainLoop7_spec hb ha hma hρ0 hcg hA G _ st1 hI1 hst1 hsmall
  refine ⟨hmin, ?_⟩
  have hn0 : Fintype.card (Cls (initSt G.degree v0).r) ≤ Fintype.card V := card_cls_le _
  have hncostR : ((normalize (Fintype.card V) (initSt G.degree v0)).cost G.cut : ℝ) +
      ((2 * Nat.clog 2 (Fintype.card V) + 1 : ℕ) : ℝ) * Fintype.card (Cls st1.r) ≤
      ((2 * Nat.clog 2 (Fintype.card V) + 1 : ℕ) : ℝ) * Fintype.card V := by
    have : (normalize (Fintype.card V) (initSt G.degree v0)).cost G.cut +
        (2 * Nat.clog 2 (Fintype.card V) + 1) * Fintype.card (Cls st1.r) ≤
        (2 * Nat.clog 2 (Fintype.card V) + 1) * Fintype.card V :=
      hncost.trans (Nat.mul_le_mul_left _ hn0)
    exact_mod_cast this
  have hlen : (List.map (fun _ => 1) (univ : Finset V).toList).sum = Fintype.card V := by simp
  have hK0 : 0 ≤ phaseK A0 ρ0 (Fintype.card V) := by
    unfold phaseK; have := cLog7_nonneg A0 ρ0; positivity
  have hN1 : (Fintype.card (Cls st1.r) : ℝ) ≤ Fintype.card V := by exact_mod_cast card_cls_le _
  have hKN : 2 * phaseK A0 ρ0 (Fintype.card V) * Fintype.card (Cls st1.r) ≤
      2 * phaseK A0 ρ0 (Fintype.card V) * Fintype.card V := by gcongr
  have hcN : ((2 * Nat.clog 2 (Fintype.card V) + 1 : ℕ) : ℝ) * Fintype.card (Cls st1.r) ≤
      ((2 * Nat.clog 2 (Fintype.card V) + 1 : ℕ) : ℝ) * Fintype.card V := by gcongr
  have hcn0 : (0 : ℝ) ≤ ((2 * Nat.clog 2 (Fintype.card V) + 1 : ℕ) : ℝ) * Fintype.card V := by
    positivity
  unfold detBudget7
  rw [hlen]
  refine Nat.cast_le.mp (le_trans ?_ (Nat.le_ceil _))
  push_cast at hncostR hcost hKN hcN hcn0 ⊢
  linarith

/-! ## The log-seven bound -/

/-- The budget is `O(n ⌊√n⌋ L(n)^7)`. -/
theorem detBudget7_le {A0 ρ0 : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    (detBudget7 A0 ρ0 n : ℝ) ≤
      (2 * cLog7 A0 ρ0 + 2909 + (thrN0 + thrN0 * thrN0 : ℕ)) *
        (n * Nat.sqrt n * (logL n : ℝ) ^ 7) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : (1 : ℝ) ≤ Nat.sqrt n := by exact_mod_cast Nat.sqrt_pos.mpr hn
  have hL : (1 : ℝ) ≤ logL n := by exact_mod_cast one_le_logL' n
  have hL7 : (1 : ℝ) ≤ (logL n : ℝ) ^ 7 := one_le_pow₀ hL
  set Z : ℝ := n * Nat.sqrt n * (logL n : ℝ) ^ 7 with hZ
  have hZ1 : 1 ≤ Z := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hn1 hs) hL7
  have hsL : 1 ≤ (Nat.sqrt n : ℝ) * (logL n : ℝ) ^ 7 := one_le_mul_of_one_le_of_one_le hs hL7
  have hnZ : (n : ℝ) ≤ Z := by
    calc (n : ℝ) = n * 1 := by ring
      _ ≤ n * ((Nat.sqrt n : ℝ) * (logL n : ℝ) ^ 7) := by gcongr
      _ = Z := by ring
  have hnL2 : (n : ℝ) * (logL n : ℝ) ^ 2 ≤ Z := by
    have : (logL n : ℝ) ^ 2 ≤ (Nat.sqrt n : ℝ) * (logL n : ℝ) ^ 7 := by
      calc (logL n : ℝ) ^ 2 ≤ (logL n : ℝ) ^ 7 := pow_le_pow_right₀ hL (by norm_num)
        _ ≤ (Nat.sqrt n : ℝ) * (logL n : ℝ) ^ 7 := le_mul_of_one_le_left (by positivity) hs
    calc (n : ℝ) * (logL n : ℝ) ^ 2 ≤ n * ((Nat.sqrt n : ℝ) * (logL n : ℝ) ^ 7) := by gcongr
      _ = Z := by ring
  have hc : (Nat.clog 2 n : ℝ) ≤ logL n := by exact_mod_cast clog_le_logL (le_refl n)
  have hcn : ((2 * Nat.clog 2 n + 1 : ℕ) : ℝ) * n ≤ 3 * Z := by
    push_cast
    have hL2 : (logL n : ℝ) ≤ (logL n : ℝ) ^ 2 := by nlinarith
    have h1 : 2 * (Nat.clog 2 n : ℝ) + 1 ≤ 3 * (logL n : ℝ) ^ 2 := by linarith
    have : (2 * (Nat.clog 2 n : ℝ) + 1) * n ≤ 3 * (n * (logL n : ℝ) ^ 2) := by
      calc (2 * (Nat.clog 2 n : ℝ) + 1) * n ≤ (3 * (logL n : ℝ) ^ 2) * n := by gcongr
        _ = 3 * (n * (logL n : ℝ) ^ 2) := by ring
    linarith
  have hsk : (skelBound n : ℝ) ≤ 2900 * Z := by
    unfold skelBound TwoRespecting.coverSize
    push_cast
    have : (5 : ℝ) * ((Nat.clog 2 n : ℝ) + 3) * (72 * n * ((Nat.clog 2 n : ℝ) + 1) + 1) ≤
        5 * (4 * logL n) * (145 * n * logL n) := by
      gcongr
      · linarith
      · nlinarith
    nlinarith
  have hK : 2 * phaseK A0 ρ0 n * n = 2 * cLog7 A0 ρ0 * Z := by
    unfold phaseK; simp only [hZ]; ring
  have hFB : ((thrN0 + thrN0 * thrN0 : ℕ) : ℝ) ≤ (thrN0 + thrN0 * thrN0 : ℕ) * Z :=
    le_mul_of_one_le_right (Nat.cast_nonneg _) hZ1
  have hX0 : (0 : ℝ) ≤ (n : ℝ) + 2 * (((2 * Nat.clog 2 n + 1 : ℕ) : ℝ) * n) +
      2 * phaseK A0 ρ0 n * n + skelBound n + (thrN0 + thrN0 * thrN0 : ℕ) := by
    have := cLog7_nonneg A0 ρ0
    unfold phaseK; positivity
  have hceil := Nat.ceil_lt_add_one hX0
  unfold detBudget7
  have := cLog7_nonneg A0 ρ0
  nlinarith

/-- **Theorem 1 with the paper's exponent, conditional on Lemmas 19 and 21.** Assume
`HierarchyBound a h` with `1 ≤ a`, `a` monotone and `a(r) ≤ A₀ L(r)³`, and a constant-quality
terminal cut guard `ConstantCutGuard ρ₀`. Then there is a constant `C` such that for every
vertex type with `n ≥ 2` one deterministic decision tree with at most
`C n (⌊√n⌋ + 1) L(n)^7` cut queries returns a minimum cut of every nonnegative weighted graph. -/
theorem deterministic_mincut_log7_of_hierarchyBound_of_constantGuard (hb : HierarchyBound a h)
    (ha : ∀ r, 1 ≤ a r) (hma : Monotone a) {A0 ρ0 : ℝ}
    (hA : ∀ r, a r ≤ A0 * (logL r : ℝ) ^ 3) (hρ0 : 1 ≤ ρ0) (hcg : ConstantCutGuard ρ0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Type) [Fintype V] [DecidableEq V], 2 ≤ Fintype.card V →
      ∃ q : ℕ, (q : ℝ) ≤ C * Fintype.card V * (Nat.sqrt (Fintype.card V) + 1) *
          (logL (Fintype.card V) : ℝ) ^ 7 ∧
        ∃ D : DTree (Finset V) ℝ (Option (Finset V)) q,
          ∀ G : WeightedGraph V, ∃ S, D.eval G.cut = some S ∧ IsMinCut G S := by
  set C := 2 * cLog7 A0 ρ0 + 2909 + ((thrN0 + thrN0 * thrN0 : ℕ) : ℝ)
  have hC : 0 < C := by have := cLog7_nonneg A0 ρ0; positivity
  refine ⟨C, hC, fun V _ _ hn => ⟨detBudget7 A0 ρ0 (Fintype.card V), ?_, ?_⟩⟩
  · refine (detBudget7_le (by omega)).trans ?_
    have hs : (Nat.sqrt (Fintype.card V) : ℝ) ≤ Nat.sqrt (Fintype.card V) + 1 := by linarith
    have : (0 : ℝ) ≤ (Fintype.card V : ℝ) * (logL (Fintype.card V) : ℝ) ^ 7 := by positivity
    calc C * ((Fintype.card V : ℝ) * Nat.sqrt (Fintype.card V) * (logL (Fintype.card V) : ℝ) ^ 7)
        ≤ C * ((Fintype.card V : ℝ) * (Nat.sqrt (Fintype.card V) + 1) *
            (logL (Fintype.card V) : ℝ) ^ 7) := by gcongr
      _ = _ := by ring
  · have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    refine ⟨(detMinCut7 hb ha ρ0 hρ0).toDTree _, fun G => ⟨_, ?_,
      (detMinCut7_spec hb ha hma hρ0 hcg hA G hn).1⟩⟩
    exact toDTree_eval _ _ (detMinCut7_spec hb ha hma hρ0 hcg hA G hn).2

/-- The log-seven statement on `Fin n`, in the target form of the roadmap. -/
theorem deterministic_mincut_log7_fin_of_hierarchyBound_of_constantGuard
    (hb : HierarchyBound a h) (ha : ∀ r, 1 ≤ a r) (hma : Monotone a) {A0 ρ0 : ℝ}
    (hA : ∀ r, a r ≤ A0 * (logL r : ℝ) ^ 3) (hρ0 : 1 ≤ ρ0) (hcg : ConstantCutGuard ρ0) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ q : ℕ, (q : ℝ) ≤ C * (n : ℝ) * (Nat.sqrt n + 1) * (logL n : ℝ) ^ 7 ∧
        ∃ D : DTree (Finset (Fin n)) ℝ (Option (Finset (Fin n))) q,
          ∀ G : WeightedGraph (Fin n), ∃ S, D.eval G.cut = some S ∧ IsMinCut G S := by
  obtain ⟨C, hC, hall⟩ :=
    deterministic_mincut_log7_of_hierarchyBound_of_constantGuard hb ha hma hA hρ0 hcg
  refine ⟨C, hC, fun n hn => ?_⟩
  have := hall (Fin n) (by simpa using hn)
  simpa using this

end DetMinCut
end CutQueryComplexity
