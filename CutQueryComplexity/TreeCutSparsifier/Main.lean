import CutQueryComplexity.TreeCutSparsifier.Normalization
import CutQueryComplexity.TreeCutSparsifier.Budget

/-! # Discovery on successive safe quotients -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace CutQueryComplexity.TreeCutSparsifier

open WeightedGraph Search Search.Comp Discovery Hierarchy DetMinCut Finset

variable {V : Type} [Fintype V] [DecidableEq V]

theorem contract_id (G : WeightedGraph V) : G.contract id = G := by
  have hf : ∀ v : V, fiber id v = {v} := by intro v; ext x; simp
  ext u v
  by_cases huv : u = v
  · subst v; simp [contract, G.diag]
  · simp [contract, huv, hf, cross]

/-- Reconstruct the current quotient and compute its tree without further queries. -/
noncomputable def finish (r : V → V) : Comp (Finset V) ℝ (Output V) :=
  (mapQ (pull (proj r)) (@learnContract (Cls r) _ (Cls r) _ (clsOrder r) id univ)).map
    fun Q => ⟨r, canonicalTree (hbPkg hierarchyBound Q) Q⟩

theorem finish_eval (G : WeightedGraph V) (r : V → V) :
    (finish r).eval G.cut = ⟨r, canonicalTree (hbPkg hierarchyBound (quot G r)) (quot G r)⟩ := by
  have hcutq : G.cut ∘ pull (proj r) = (quot G r).cut := by
    funext T; exact (cut_contract G (proj r) T).symm
  simp only [finish, eval_map, eval_mapQ, hcutq]
  rw [@learnContract_eval (Cls r) _ _ (Cls r) _ _ (clsOrder r) (quot G r) id univ
    (fun _ => mem_univ _), contract_id]

theorem finish_cost (G : WeightedGraph V) (r : V → V) :
    (finish r).cost G.cut ≤ Fintype.card (Cls r) + Fintype.card (Cls r)^2 := by
  have hcutq : G.cut ∘ pull (proj r) = (quot G r).cut := by
    funext T; exact (cut_contract G (proj r) T).symm
  simp only [finish, cost_map, cost_mapQ, hcutq]
  simpa [sq] using @learnContract_cost (Cls r) _ _ (Cls r) _ (clsOrder r) (quot G r) id univ

theorem finish_correct (G : WeightedGraph V) (r : V → V) {α : ℝ}
    (hs : SafePartition G r) (hN : 2 ≤ Fintype.card (Cls r))
    (hα : distortion (Fintype.card (Cls r)) ≤ α) : Correct G α ((finish r).eval G.cut) := by
  rw [finish_eval]
  refine ⟨hs, ?_⟩
  obtain ⟨hm, hl, _, hd⟩ := hbPkg_spec hierarchyBound (quot G r)
  exact (canonicalTree_good _ _ (by omega) hl hd).mono hα

/-- Fuel bounds the number of failed phases. The reconstruction branches also
make the program total on arbitrary answer functions. -/
noncomputable def mainLoop (α : ℝ) : ℕ → St V → Comp (Finset V) ℝ (Output V)
  | 0, st => finish st.r
  | fuel + 1, st =>
    if hstop : Fintype.card (Cls st.r) ≤ parameter (Fintype.card (Cls st.r)) α ∨ st.U ≤ 0 then
      finish st.r
    else
      (mapQ (pull (proj st.r)) (phase (fun c => st.deg c.val) st.U
        (parameter (Fintype.card (Cls st.r)) α)
        (Classical.choice (Fintype.card_pos_iff.mp (by omega))))).bind fun out =>
      match out with
      | .tree data => .pure ⟨st.r, data⟩
      | .halve S val =>
        (DetMinCut.normalize (Fintype.card V) ⟨st.r, st.deg, val, pull (proj st.r) S⟩).bind
          (mainLoop α fuel)

/-- Correctness and a linear potential for the remaining discovery work. -/
theorem mainLoop_spec {α : ℝ} (hα : Admissible (Fintype.card V) α)
    (G : WeightedGraph V) (hpos : 0 < mincutValue G) :
    ∀ (fuel : ℕ) (st : St V), SafeInv G st → Stopped st →
      Fintype.card (Cls st.r) < 2^fuel →
      Correct G α ((mainLoop α fuel st).eval G.cut) ∧
      ((mainLoop α fuel st).cost G.cut : ℝ) ≤
        2 * phaseK (Fintype.card V) α * Fintype.card (Cls st.r) +
          (2 * Nat.clog 2 (Fintype.card V) + 1 : ℕ) * Fintype.card (Cls st.r) := by
  have hK := phaseK_pos hα
  have hα1 := (admissible_bounds hα).1
  intro fuel
  induction fuel with
  | zero =>
      intro st hI _ hsmall
      have := hI.1.two_le
      simp only [pow_zero] at hsmall
      omega
  | succ fuel ih =>
      intro st hsafe hst hsmall
      obtain ⟨hI, hs⟩ := hsafe
      have hU : 0 < st.U := hpos.trans_le hI.lam_le
      have hNle := card_cls_le st.r
      have hN2 := hI.two_le
      have hc0 : (0 : ℝ) ≤ ((2 * Nat.clog 2 (Fintype.card V) + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      by_cases hstop : Fintype.card (Cls st.r) ≤ parameter (Fintype.card (Cls st.r)) α ∨ st.U ≤ 0
      · simp only [mainLoop, dite_eq_left hstop]
        refine ⟨finish_correct G st.r hs hN2 (offline_quality hα hNle), ?_⟩
        have hk : Fintype.card (Cls st.r) ≤ parameter (Fintype.card (Cls st.r)) α :=
          hstop.resolve_right (not_le.mpr hU)
        have hNα := reconstruct_size hα hNle hk
        have hcost : ((finish st.r).cost G.cut : ℝ) ≤
            (Fintype.card (Cls st.r) : ℝ) + (Fintype.card (Cls st.r) : ℝ)^2 := by
          exact_mod_cast finish_cost G st.r
        have hNK : (Fintype.card (Cls st.r) : ℝ) ≤ phaseK (Fintype.card V) α :=
          hNα.trans (phaseK_ge hα)
        have hK1 : 1 ≤ phaseK (Fintype.card V) α := hα1.trans (phaseK_ge hα)
        have hcn : 0 ≤ ((2 * Nat.clog 2 (Fintype.card V) + 1 : ℕ) : ℝ) *
            Fintype.card (Cls st.r) := by positivity
        have hN0 : (0 : ℝ) ≤ Fintype.card (Cls st.r) := Nat.cast_nonneg _
        nlinarith
      have hklt : parameter (Fintype.card (Cls st.r)) α < Fintype.card (Cls st.r) := by omega
      have hk2 := (parameter_spec hα hNle).1
      have hN3 : 3 ≤ Fintype.card (Cls st.r) := by omega
      have hcutq : G.cut ∘ pull (proj st.r) = (quot G st.r).cut := by
        funext T; exact (cut_contract G (proj st.r) T).symm
      have hdegq : ∀ c, (quot G st.r).degree c ≤
          ((Fintype.card (Cls st.r) : ℝ) - 1) * st.U := by
        intro c
        rcases hst with h0 | h0
        · linarith
        · rw [← congrFun hI.quot_degree c]; exact h0 c
      simp only [mainLoop, dite_eq_right hstop, eval_bind, cost_bind, eval_mapQ, cost_mapQ,
        hcutq, hI.quot_degree]
      set N := Fintype.card (Cls st.r) with hNdef
      set v0 : Cls st.r := Classical.choice (Fintype.card_pos_iff.mp (by omega))
      obtain ⟨hok, hpcost⟩ := phase_spec (quot G st.r) hN3 hU hdegq hk2 (by omega) v0
      have hPB : ((phase (quot G st.r).degree st.U (parameter N α) v0).cost
          (quot G st.r).cut : ℝ) ≤ phaseK (Fintype.card V) α * N := by
        have hcR : ((phase (quot G st.r).degree st.U (parameter N α) v0).cost
            (quot G st.r).cut : ℝ) ≤ phaseBudget N (parameter N α) := by exact_mod_cast hpcost
        exact hcR.trans (phaseBudget_le hα (by omega) hNle)
      rcases hout : (phase (quot G st.r).degree st.U (parameter N α) v0).eval
          (quot G st.r).cut with data | ⟨S, val⟩
      · rw [hout] at hok
        simp only [PhaseOK] at hok
        simp only [eval_pure, cost_pure, Nat.add_zero]
        refine ⟨⟨hs, hok.mono (parameter_quality hα (by omega) hNle)⟩, ?_⟩
        have : 0 ≤ ((2 * Nat.clog 2 (Fintype.card V) + 1 : ℕ) : ℝ) * N := by positivity
        have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
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
            have := mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ 4 * N) hU.le
            linarith
          linarith
        have hI1 : Inv G st1 := by
          refine ⟨hI.deg, sat_pull _ _, properShore_pull _ (proj_surjective _) hSp, ?_, ?_, hI.opt⟩
          · show G.cut (pull (proj st.r) S) = val
            rw [hval, cut_contract]
          · intro c; exact hvalle.trans (hI.U_le c)
        obtain ⟨hI2, hU2le, hst2, href2, _, hncost⟩ :=
          normalize_spec G (Fintype.card V) st1 hI1 (by show N ≤ _; omega)
        set st2 := (DetMinCut.normalize (Fintype.card V) st1).eval G.cut
        have hs2 : SafePartition G st2.r := normalize_safe G _ st1 hI1 hs
        have hU2 : 0 < st2.U := hpos.trans_le hI2.lam_le
        have hstop2 : ∀ c : Cls st2.r,
            st2.deg c.val ≤ ((Fintype.card (Cls st2.r) : ℝ) - 1) * st2.U := by
          rcases hst2 with h0 | h0
          · linarith
          · exact h0
        have hhalf := halving G hI hI2 href2 hU hU2 hstop2 hU2le hvalU
        have hsmall2 : Fintype.card (Cls st2.r) < 2^fuel := by
          rw [pow_succ] at hsmall
          omega
        obtain ⟨hcorrect, hlcost⟩ := ih st2 ⟨hI2, hs2⟩ hst2 hsmall2
        refine ⟨hcorrect, ?_⟩
        have hncostR : ((DetMinCut.normalize (Fintype.card V) st1).cost G.cut : ℝ) +
            ((2 * Nat.clog 2 (Fintype.card V) + 1 : ℕ) : ℝ) * Fintype.card (Cls st2.r) ≤
            ((2 * Nat.clog 2 (Fintype.card V) + 1 : ℕ) : ℝ) * N := by
          exact_mod_cast hncost
        have hhalfR : 2 * (Fintype.card (Cls st2.r) : ℝ) ≤ N := by exact_mod_cast hhalf
        have hKhalf : 2 * phaseK (Fintype.card V) α * Fintype.card (Cls st2.r) ≤
            phaseK (Fintype.card V) α * N := by nlinarith
        push_cast at hncostR hlcost ⊢
        linarith

/-- One deterministic computation, chosen before seeing the hidden graph. -/
noncomputable def learn [Nonempty V] (α : ℝ) : Comp (Finset V) ℝ (Output V) :=
  (tabulate (fun v => ask ({v} : Finset V)) univ.toList).bind fun degs =>
    (DetMinCut.normalize (Fintype.card V)
      (initSt (fun v => (degs v).getD 0) (argminOf fun v => (degs v).getD 0))).bind
      (mainLoop α (Nat.log 2 (Fintype.card V) + 1))

noncomputable def budget (n : ℕ) (α : ℝ) : ℕ :=
  ⌈(n : ℝ) + ((2 * Nat.clog 2 n + 1 : ℕ) : ℝ) * n + 2 * phaseK n α * n⌉₊

theorem learn_spec [Nonempty V] {α : ℝ} (hα : Admissible (Fintype.card V) α)
    (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V) (hpos : 0 < mincutValue G) :
    Correct G α ((learn α).eval G.cut) ∧ (learn α).cost G.cut ≤ budget (Fintype.card V) α := by
  have hdegs : (fun v => ((tabulate (fun v => ask ({v} : Finset V)) univ.toList).eval G.cut v).getD 0)
      = G.degree := by
    funext v; simp [eval_tabulate, mem_toList, cut_singleton]
  simp only [learn, eval_bind, cost_bind, cost_tabulate, cost_ask, hdegs]
  set v0 := argminOf G.degree
  have hI0 := inv_initSt G hn (argminOf_spec G.degree)
  obtain ⟨hI1, _, hst1, _, _, hncost⟩ := normalize_spec G (Fintype.card V) _ hI0
    (by show Fintype.card (Cls (id : V → V)) ≤ _; have := card_cls_le (id : V → V); omega)
  set st1 := (DetMinCut.normalize (Fintype.card V) (initSt G.degree v0)).eval G.cut
  have hs1 : SafePartition G st1.r := normalize_safe G _ _ hI0 (safePartition_id G)
  have hsmall : Fintype.card (Cls st1.r) < 2^(Nat.log 2 (Fintype.card V) + 1) :=
    (card_cls_le _).trans_lt (Nat.lt_pow_succ_log_self (by norm_num) _)
  obtain ⟨hcorrect, hcost⟩ := mainLoop_spec hα G hpos _ st1 ⟨hI1, hs1⟩ hst1 hsmall
  refine ⟨hcorrect, ?_⟩
  have hn0 : Fintype.card (Cls (initSt G.degree v0).r) ≤ Fintype.card V := card_cls_le _
  have hncostR : ((DetMinCut.normalize (Fintype.card V) (initSt G.degree v0)).cost G.cut : ℝ) +
      ((2 * Nat.clog 2 (Fintype.card V) + 1 : ℕ) : ℝ) * Fintype.card (Cls st1.r) ≤
      ((2 * Nat.clog 2 (Fintype.card V) + 1 : ℕ) : ℝ) * Fintype.card V := by
    exact_mod_cast hncost.trans (Nat.mul_le_mul_left _ hn0)
  have hlen : (List.map (fun _ => 1) (univ : Finset V).toList).sum = Fintype.card V := by simp
  have hN1 : (Fintype.card (Cls st1.r) : ℝ) ≤ Fintype.card V := by exact_mod_cast card_cls_le _
  have hK := phaseK_pos hα
  have hKN : 2 * phaseK (Fintype.card V) α * Fintype.card (Cls st1.r) ≤
      2 * phaseK (Fintype.card V) α * Fintype.card V := by gcongr
  unfold budget
  rw [hlen]
  refine Nat.cast_le.mp (le_trans ?_ (Nat.le_ceil _))
  push_cast at hncostR hcost hKN ⊢
  linarith

end CutQueryComplexity.TreeCutSparsifier
