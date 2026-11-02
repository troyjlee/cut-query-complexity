import CutQueryComplexity.DetMinCut.Phase
import CutQueryComplexity.DetMinCut.Normalize

/-! # Deterministic weighted minimum cut, conditional on `HierarchyBound` (Theorem 1, §6.7)

The algorithm queries all singleton degrees, starts from a minimum-degree singleton as the
witness, and normalizes. Each round on the current quotient with `N` classes:

* if `U ≤ 0`, the witness is a zero cut, hence a minimum cut;
* if `N ≤ 2`, the witness is a minimum cut, since every proper union of two classes is one
  class or the other;
* otherwise one phase runs with `k = ⌊√N⌋ + 1`. A weak skeleton of the quotient is turned into
  a minimum cut by the tree cover and the two-respecting search (`skeletonMinCut`). A smaller
  witnessed bound is followed by normalization, which halves `N` (Lemma 28).

Every query to the quotient is one original query on a union of classes, and every minimum
cut of the input survives as a union of classes, so a minimum cut of the quotient pulls back
to a minimum cut of the input.

`deterministic_mincut_of_hierarchyBound` is Theorem 1 conditional on `HierarchyBound a h`
with `1 ≤ a` and `a`, `h` monotone: one decision tree with budget `detBudget a h n` returns a
minimum cut of every nonnegative weighted graph on `n ≥ 2` vertices.
-/

namespace CutQueryComplexity
namespace DetMinCut

open TwoRespecting WeightedGraph Search Search.Comp Discovery Hierarchy Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## Pulling minimum cuts back from the quotient -/

theorem isMinCut_of_sat {G : WeightedGraph V} {S : Finset V} (hS : IsMinCut G S) :
    G.cut S = mincutValue G := by
  refine le_antisymm ?_ (mincutValue_le G hS.1)
  rw [mincutValue, dite_eq_left ⟨S, (mem_properShores S).mpr hS.1⟩]
  exact le_inf' _ _ fun T hT => hS.2 T ((mem_properShores T).mp hT)

/-- A minimum cut of the quotient pulls back to a minimum cut of the input. -/
theorem isMinCut_pull {G : WeightedGraph V} {st : St V} (hI : Inv G st) {T : Finset (Cls st.r)}
    (hT : IsMinCut (quot G st.r) T) : IsMinCut G (pull (proj st.r) T) := by
  refine ⟨properShore_pull _ (proj_surjective _) hT.1, fun S hS => ?_⟩
  obtain ⟨Sopt, hSopt, hsat⟩ := hI.opt
  set Topt := Sopt.image (proj st.r)
  have hpull : pull (proj st.r) Topt = Sopt := pull_image_of_sat hsat
  have hTopt : ProperShore Topt := by
    refine ⟨?_, ?_⟩
    · obtain ⟨x, hx⟩ := hSopt.1.1; exact ⟨_, mem_image_of_mem _ hx⟩
    · intro h; apply hSopt.1.2; rw [← hpull, h]; ext; simp
  calc G.cut (pull (proj st.r) T) = (quot G st.r).cut T := (cut_contract _ _ _).symm
    _ ≤ (quot G st.r).cut Topt := hT.2 _ hTopt
    _ = G.cut Sopt := by rw [cut_contract, hpull]
    _ ≤ G.cut S := hSopt.2 S hS

/-- With two classes, every proper union of classes is a minimum cut. -/
theorem isMinCut_two {G : WeightedGraph V} {st : St V} (hI : Inv G st)
    (h2 : Fintype.card (Cls st.r) ≤ 2) : IsMinCut G st.wit := by
  obtain ⟨Sopt, hSopt, hsat⟩ := hI.opt
  have key : ∀ {S : Finset V}, Sat st.r S → ProperShore S →
      ∃ c, S = pull (proj st.r) {c} := by
    intro S hS hp
    set T := S.image (proj st.r)
    have hpull : pull (proj st.r) T = S := pull_image_of_sat hS
    have hT1 : T.Nonempty := by obtain ⟨x, hx⟩ := hp.1; exact ⟨_, mem_image_of_mem _ hx⟩
    have hT2 : T ≠ univ := by intro h; apply hp.2; rw [← hpull, h]; ext; simp
    have hcard : T.card = 1 := by
      have h1 : T.card < Fintype.card (Cls st.r) := by
        rw [← card_univ]; exact card_lt_card (ssubset_univ_iff.mpr hT2)
      have := hT1.card_pos; omega
    obtain ⟨c, hc⟩ := card_eq_one.mp hcard
    exact ⟨c, by rw [← hpull, hc]⟩
  obtain ⟨c, hc⟩ := key hI.wit_sat hI.wit_proper
  obtain ⟨c', hc'⟩ := key hsat hSopt.1
  have hval : G.cut st.wit = G.cut Sopt := by
    by_cases hcc : c = c'
    · rw [hc, hc', hcc]
    · have huniv : ({c, c'} : Finset (Cls st.r)) = univ :=
        eq_of_subset_of_card_le (subset_univ _) (by rw [card_pair hcc, card_univ]; omega)
      have hcompl : ({c'} : Finset (Cls st.r)) = {c}ᶜ := by
        ext x; simp only [mem_singleton, mem_compl]
        constructor
        · rintro rfl; exact Ne.symm hcc
        · intro hx
          have : x ∈ ({c, c'} : Finset (Cls st.r)) := huniv ▸ mem_univ x
          simp only [mem_insert, mem_singleton] at this
          tauto
      rw [hc, hc', hcompl, pull_compl, cut_compl]
  exact ⟨hI.wit_proper, fun T hT => hval ▸ hSopt.2 T hT⟩

/-- A witness of value at most zero is a minimum cut. -/
theorem isMinCut_zero {G : WeightedGraph V} {st : St V} (hI : Inv G st) (hU : st.U ≤ 0) :
    IsMinCut G st.wit :=
  ⟨hI.wit_proper, fun T _ => by rw [hI.wit_val]; exact hU.trans (G.cut_nonneg T)⟩

/-! ## The main loop -/

variable {a : ℕ → ℝ} {h : ℕ → ℕ}

/-- A linear order on the classes, used only by the two-respecting search. -/
@[instance_reducible]
noncomputable def clsOrder (r : V → V) : LinearOrder (Cls r) :=
  LinearOrder.lift' (Fintype.equivFin (Cls r)) (Fintype.equivFin (Cls r)).injective

/-- The center parameter `k = ⌊√N⌋ + 1`. -/
def kOf (N : ℕ) : ℕ := Nat.sqrt N + 1

/-- **The main loop** over phases. -/
noncomputable def mainLoop (hb : HierarchyBound a h) (ha : ∀ r, 1 ≤ a r) :
    ℕ → St V → Comp (Finset V) ℝ (Finset V)
  | 0, st => .pure st.wit
  | fuel + 1, st =>
    if hstop : st.U ≤ 0 ∨ Fintype.card (Cls st.r) ≤ 2 then .pure st.wit
    else
      (mapQ (pull (proj st.r)) (phase hb ha (fun c => st.deg c.val) st.U
        (kOf (Fintype.card (Cls st.r)))
        (Classical.choice (Fintype.card_pos_iff.mp (by omega))))).bind fun out =>
        match out with
        | .skel H => (mapQ (pull (proj st.r)) (@skeletonMinCut _ _ _ (clsOrder st.r) H)).map
            (pull (proj st.r))
        | .halve S val =>
            (normalize (Fintype.card V) ⟨st.r, st.deg, val, pull (proj st.r) S⟩).bind
              (mainLoop hb ha fuel)

/-! ## Lemma 28 on the current quotient -/

/-- **Lemma 28.** If normalization after a phase ends with a positive bound, at most half of
the classes remain. -/
theorem halving (G : WeightedGraph V) {st st2 : St V} (hI : Inv G st) (hI2 : Inv G st2)
    (href : ∀ x y, st.r x = st.r y → st2.r x = st2.r y) (hU : 0 < st.U) (hU2 : 0 < st2.U)
    (hstop2 : ∀ c : Cls st2.r, st2.deg c.val ≤ ((Fintype.card (Cls st2.r) : ℝ) - 1) * st2.U)
    {u : ℝ} (hU2u : st2.U ≤ u) (hu : u < st.U / (4 * Fintype.card (Cls st.r))) :
    2 * Fintype.card (Cls st2.r) ≤ Fintype.card (Cls st.r) := by
  classical
  let pre : Cls st.r → V := fun c => Classical.choose (mem_image.mp c.2)
  have hpre : ∀ c : Cls st.r, st.r (pre c) = c.val := fun c =>
    (Classical.choose_spec (mem_image.mp c.2)).2
  let π : Cls st.r → Cls st2.r := fun c => proj st2.r (pre c)
  have hπ : ∀ x, π (proj st.r x) = proj st2.r x := fun x =>
    proj_eq_iff.mpr (href _ _ (hpre (proj st.r x)))
  have hsurj : Function.Surjective π := fun c2 => by
    obtain ⟨x, rfl⟩ := proj_surjective st2.r c2
    exact ⟨proj st.r x, hπ x⟩
  have hdeg : ∀ c, st.U ≤ (quot G st.r).degree c := fun c => by
    rw [← congrFun hI.quot_degree c]; exact hI.U_le c
  have hstop : ∀ b, ((quot G st.r).contract π).degree b ≤
      ((Fintype.card (Cls st2.r) : ℝ) - 1) * st2.U := by
    intro b
    rw [contract_degree, cut_contract]
    have hset : pull (proj st.r) (fiber π b) = univ.filter fun x => st2.r x = b.val := by
      ext x
      simp only [mem_pull, mem_fiber, mem_filter, mem_univ, true_and]
      rw [hπ]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [hset, ← hI2.deg b]
    exact hstop2 b
  exact (normalization_halves (quot G st.r) π hsurj hU hdeg hU2.le hU2u hu hstop).2

/-! ## Correctness and cost of the main loop -/

/-- The largest phase bound over quotients with at most `n` classes. -/
noncomputable def phaseMax (a : ℕ → ℝ) (h : ℕ → ℕ) (n : ℕ) : ℝ :=
  (range (n + 1)).sup' nonempty_range_add_one fun N => phaseBound a h N (kOf N)

/-- The query bound of the tree cover and two-respecting search on `n` vertices. -/
def skelBound (n : ℕ) : ℕ := coverSize n * (72 * n * (Nat.clog 2 n + 1) + 1)

theorem phaseBoundR_nonneg (ha : ∀ r, 1 ≤ a r) {ρf : ℕ → ℝ} (hρf : ∀ N, 1 ≤ ρf N) (N k : ℕ) :
    0 ≤ phaseBoundR a ρf N k := by
  have h1 := ha (3 * N + 1); have h2 := ha N
  have hγ := gammaR_pos ha hρf N
  unfold phaseBoundR; positivity

theorem phaseBound_nonneg (ha : ∀ r, 1 ≤ a r) (N k : ℕ) : 0 ≤ phaseBound a h N k :=
  phaseBoundR_nonneg ha (one_le_rhoOf h) N k

theorem le_phaseMax {N n : ℕ} (hNn : N ≤ n) :
    phaseBound a h N (kOf N) ≤ phaseMax a h n :=
  le_sup' (fun N => phaseBound a h N (kOf N)) (mem_range.mpr (by omega))

theorem phaseMax_nonneg (ha : ∀ r, 1 ≤ a r) (n : ℕ) : 0 ≤ phaseMax a h n :=
  (phaseBound_nonneg ha 0 (kOf 0)).trans (le_phaseMax (Nat.zero_le n))

theorem skelBound_mono {N n : ℕ} (h : N ≤ n) : skelBound N ≤ skelBound n := by
  unfold skelBound coverSize
  have := Nat.clog_mono_right 2 h
  gcongr

theorem card_cls_le (r : V → V) : Fintype.card (Cls r) ≤ Fintype.card V := by
  rw [card_cls]; exact card_image_le.trans (by simp)

/-- **The main loop.** From a stopped state with `U ≤ 0` or fewer than `2^fuel` classes, the
output is a minimum cut, using at most `fuel · phaseMax + (2⌈log₂ n⌉ + 1) N + skelBound n`
queries. -/
theorem mainLoop_spec (hb : HierarchyBound a h) (ha : ∀ r, 1 ≤ a r) (hma : Monotone a)
    (hh : Monotone h) (G : WeightedGraph V) :
    ∀ (fuel : ℕ) (st : St V), Inv G st → Stopped st →
      (st.U ≤ 0 ∨ Fintype.card (Cls st.r) < 2 ^ fuel) →
      IsMinCut G ((mainLoop hb ha fuel st).eval G.cut) ∧
      ((mainLoop hb ha fuel st).cost G.cut : ℝ) ≤
        fuel * phaseMax a h (Fintype.card V) +
          (2 * Nat.clog 2 (Fintype.card V) + 1 : ℕ) * Fintype.card (Cls st.r) +
          skelBound (Fintype.card V) := by
  have hPM := phaseMax_nonneg (h := h) ha (Fintype.card V)
  intro fuel
  induction fuel with
  | zero =>
      intro st hI _ hsmall
      have hU : st.U ≤ 0 := by
        rcases hsmall with h0 | h0
        · exact h0
        · have := hI.two_le; rw [pow_zero] at h0; omega
      simp only [mainLoop, eval_pure, cost_pure, Nat.cast_zero]
      exact ⟨isMinCut_zero hI hU, by positivity⟩
  | succ fuel ih =>
      intro st hI hst hsmall
      by_cases hstop : st.U ≤ 0 ∨ Fintype.card (Cls st.r) ≤ 2
      · simp only [mainLoop, dite_eq_left hstop, eval_pure, cost_pure, Nat.cast_zero]
        refine ⟨?_, by positivity⟩
        rcases hstop with h0 | h0
        · exact isMinCut_zero hI h0
        · exact isMinCut_two hI h0
      have hnot := hstop
      push Not at hstop
      obtain ⟨hU, hN3⟩ := hstop
      have hNle := card_cls_le st.r
      have hcutq : G.cut ∘ pull (proj st.r) = (quot G st.r).cut := by
        funext T; exact (cut_contract G (proj st.r) T).symm
      have hdegq : ∀ c, (quot G st.r).degree c ≤
          ((Fintype.card (Cls st.r) : ℝ) - 1) * st.U := by
        intro c
        rcases hst with h0 | h0
        · linarith
        · rw [← congrFun hI.quot_degree c]; exact h0 c
      have hk2 : 2 ≤ kOf (Fintype.card (Cls st.r)) := by
        unfold kOf; have := Nat.sqrt_pos.mpr (by omega : 0 < Fintype.card (Cls st.r)); omega
      have hkN : kOf (Fintype.card (Cls st.r)) ≤ 8 * Fintype.card (Cls st.r) := by
        unfold kOf; have := Nat.sqrt_le_self (Fintype.card (Cls st.r)); omega
      simp only [mainLoop, dite_eq_right hnot, eval_bind, cost_bind, eval_mapQ, cost_mapQ, hcutq,
        hI.quot_degree]
      set v0 : Cls st.r := Classical.choice (Fintype.card_pos_iff.mp (by omega))
      obtain ⟨hok, hpcost⟩ := phase_spec hb ha hma hh (quot G st.r) (by omega) hU hdegq hk2 hkN v0
      have hPB : (Comp.cost (quot G st.r).cut
          (phase hb ha (quot G st.r).degree st.U (kOf (Fintype.card (Cls st.r))) v0) : ℝ) ≤
          phaseMax a h (Fintype.card V) := hpcost.trans (le_phaseMax hNle)
      have hc0 : (0 : ℝ) ≤ ((2 * Nat.clog 2 (Fintype.card V) + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      rcases hout : (phase hb ha (quot G st.r).degree st.U (kOf (Fintype.card (Cls st.r))) v0).eval
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
        have : (0 : ℝ) ≤ fuel * phaseMax a h (Fintype.card V) := by positivity
        have : (0 : ℝ) ≤ ((2 * Nat.clog 2 (Fintype.card V) + 1 : ℕ) : ℝ) * Fintype.card (Cls st.r) :=
          by positivity
        push_cast at this
        nlinarith
      · rw [hout] at hok
        simp only [PhaseOK] at hok
        obtain ⟨hSp, hval, hvalU⟩ := hok
        simp only [eval_bind, cost_bind]
        set st1 : St V := ⟨st.r, st.deg, val, pull (proj st.r) S⟩ with hst1
        have hN0 : (0 : ℝ) < Fintype.card (Cls st.r) := by exact_mod_cast (by omega : 0 < _)
        have hvalle : val ≤ st.U := by
          have : st.U / (4 * Fintype.card (Cls st.r)) ≤ st.U := by
            have h3 : (3 : ℝ) ≤ Fintype.card (Cls st.r) := by exact_mod_cast hN3
            rw [div_le_iff₀ (by positivity)]
            have : st.U * 1 ≤ st.U * (4 * Fintype.card (Cls st.r)) :=
              mul_le_mul_of_nonneg_left (by linarith) hU.le
            linarith
          linarith
        have hI1 : Inv G st1 := by
          refine ⟨hI.deg, sat_pull _ _, properShore_pull _ (proj_surjective _) hSp, ?_, ?_, hI.opt⟩
          · show G.cut (pull (proj st.r) S) = val
            rw [hval, cut_contract]
          · intro c; exact hvalle.trans (hI.U_le c)
        obtain ⟨hI2, hU2le, hst2, href2, hcard2, hncost⟩ :=
          normalize_spec G (Fintype.card V) st1 hI1 (by show Fintype.card (Cls st.r) ≤ _; omega)
        set st2 := (normalize (Fintype.card V) st1).eval G.cut
        have hsmall2 : st2.U ≤ 0 ∨ Fintype.card (Cls st2.r) < 2 ^ fuel := by
          by_cases hU2 : st2.U ≤ 0
          · exact Or.inl hU2
          · right
            push Not at hU2
            have hstop2 : ∀ c : Cls st2.r,
                st2.deg c.val ≤ ((Fintype.card (Cls st2.r) : ℝ) - 1) * st2.U := by
              rcases hst2 with h0 | h0
              · linarith
              · exact h0
            have hhalf := halving G hI hI2 href2 hU hU2 hstop2 hU2le hvalU
            have hlt : Fintype.card (Cls st.r) < 2 ^ (fuel + 1) := by
              rcases hsmall with h0 | h0
              · linarith
              · exact h0
            rw [pow_succ] at hlt
            omega
        obtain ⟨hmin, hlcost⟩ := ih st2 hI2 hst2 hsmall2
        refine ⟨hmin, ?_⟩
        have hncostR : ((normalize (Fintype.card V) st1).cost G.cut : ℝ) +
            ((2 * Nat.clog 2 (Fintype.card V) + 1 : ℕ) : ℝ) * Fintype.card (Cls st2.r) ≤
            ((2 * Nat.clog 2 (Fintype.card V) + 1 : ℕ) : ℝ) * Fintype.card (Cls st.r) := by
          exact_mod_cast hncost
        push_cast at hncostR hlcost ⊢
        linarith

/-! ## The complete algorithm -/

/-- The initial state: singleton classes and a minimum-degree singleton witness. -/
def initSt (d : V → ℝ) (v0 : V) : St V := ⟨id, d, d v0, {v0}⟩

/-- A vertex of minimum value, chosen offline. -/
noncomputable def argminOf [Nonempty V] (d : V → ℝ) : V :=
  Classical.choose (exists_min_image univ d univ_nonempty)

omit [DecidableEq V] in
theorem argminOf_spec [Nonempty V] (d : V → ℝ) (v : V) : d (argminOf d) ≤ d v :=
  (Classical.choose_spec (exists_min_image univ d univ_nonempty)).2 v (mem_univ v)

/-- **The deterministic algorithm.** Query all degrees, normalize, and run the main loop. -/
noncomputable def detMinCut [Nonempty V] (hb : HierarchyBound a h) (ha : ∀ r, 1 ≤ a r) :
    Comp (Finset V) ℝ (Finset V) :=
  (tabulate (fun v => ask ({v} : Finset V)) univ.toList).bind fun degs =>
    (normalize (Fintype.card V)
        (initSt (fun v => (degs v).getD 0) (argminOf fun v => (degs v).getD 0))).bind
      (mainLoop hb ha (Nat.log 2 (Fintype.card V) + 1))

/-- The query budget of the conditional deterministic algorithm on `n` vertices. -/
noncomputable def detBudget (a : ℕ → ℝ) (h : ℕ → ℕ) (n : ℕ) : ℕ :=
  ⌈(n : ℝ) + ((2 * Nat.clog 2 n + 1 : ℕ) : ℝ) * n + (Nat.log 2 n + 1 : ℕ) * phaseMax a h n +
    skelBound n⌉₊

theorem inv_initSt (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V) {v0 : V}
    (hv0 : ∀ v, G.degree v0 ≤ G.degree v) : Inv G (initSt G.degree v0) := by
  have hfil : ∀ c : V, (univ.filter fun x : V => id x = c) = {c} := fun c => by
    ext x; simp
  refine ⟨fun c => ?_, fun x y hxy => by simp only [initSt, id] at hxy; rw [hxy], ?_, ?_, ?_, ?_⟩
  · change G.degree c.val = G.cut (univ.filter fun x => id x = c.val)
    rw [hfil, cut_singleton]
  · exact properShore_singleton v0 hn
  · simp only [initSt]; exact cut_singleton G v0
  · intro c; exact hv0 c.val
  · have hne : (properShores V).Nonempty := ⟨{v0}, (mem_properShores _).mpr
      (properShore_singleton v0 hn)⟩
    obtain ⟨S, hS, heq⟩ := exists_mem_eq_inf' hne G.cut
    refine ⟨S, ⟨(mem_properShores _).mp hS, fun T hT => ?_⟩, fun x y hxy => ?_⟩
    · rw [← heq]; exact inf'_le _ ((mem_properShores _).mpr hT)
    · simp only [initSt, id] at hxy; rw [hxy]

/-- **Correctness and cost of the algorithm.** -/
theorem detMinCut_spec [Nonempty V] (hb : HierarchyBound a h) (ha : ∀ r, 1 ≤ a r)
    (hma : Monotone a) (hh : Monotone h) (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V) :
    IsMinCut G ((detMinCut hb ha).eval G.cut) ∧
      (detMinCut hb ha).cost G.cut ≤ detBudget a h (Fintype.card V) := by
  have hdegs : (fun v => ((tabulate (fun v => ask ({v} : Finset V)) univ.toList).eval G.cut v).getD 0)
      = G.degree := by
    funext v; simp [eval_tabulate, mem_toList, cut_singleton]
  simp only [detMinCut, eval_bind, cost_bind, cost_tabulate, cost_ask, hdegs]
  set v0 := argminOf G.degree
  have hv0 : ∀ v, G.degree v0 ≤ G.degree v := argminOf_spec G.degree
  have hI0 := inv_initSt G hn hv0
  obtain ⟨hI1, -, hst1, -, hcard1, hncost⟩ := normalize_spec G (Fintype.card V) _ hI0
    (by show Fintype.card (Cls (id : V → V)) ≤ _; have := card_cls_le (id : V → V); omega)
  set st1 := (normalize (Fintype.card V) (initSt G.degree v0)).eval G.cut
  have hsmall : st1.U ≤ 0 ∨ Fintype.card (Cls st1.r) < 2 ^ (Nat.log 2 (Fintype.card V) + 1) :=
    Or.inr ((card_cls_le _).trans_lt (Nat.lt_pow_succ_log_self (by norm_num) _))
  obtain ⟨hmin, hcost⟩ := mainLoop_spec hb ha hma hh G _ st1 hI1 hst1 hsmall
  refine ⟨hmin, ?_⟩
  have hn0 : (Fintype.card (Cls (initSt G.degree v0).r)) ≤ Fintype.card V := card_cls_le _
  have hncostR : ((normalize (Fintype.card V) (initSt G.degree v0)).cost G.cut : ℝ) +
      ((2 * Nat.clog 2 (Fintype.card V) + 1 : ℕ) : ℝ) * Fintype.card (Cls st1.r) ≤
      ((2 * Nat.clog 2 (Fintype.card V) + 1 : ℕ) : ℝ) * Fintype.card V := by
    have : (normalize (Fintype.card V) (initSt G.degree v0)).cost G.cut +
        (2 * Nat.clog 2 (Fintype.card V) + 1) * Fintype.card (Cls st1.r) ≤
        (2 * Nat.clog 2 (Fintype.card V) + 1) * Fintype.card V :=
      hncost.trans (Nat.mul_le_mul_left _ hn0)
    exact_mod_cast this
  have hlen : (List.map (fun _ => 1) (univ : Finset V).toList).sum = Fintype.card V := by
    simp
  unfold detBudget
  rw [hlen]
  refine Nat.cast_le.mp (le_trans ?_ (Nat.le_ceil _))
  push_cast at hncostR hcost ⊢
  linarith

/-- **Theorem 1, conditional on `HierarchyBound`.** If every explicit graph on `r` vertices
has a hierarchy with at most `2r + 1` nodes, childless leaves, height at most `h r` and
distortion at most `a r`, with `1 ≤ a` and `a`, `h` monotone, then one deterministic
cut-query decision tree with `detBudget a h n` queries returns a minimum cut of every
nonnegative weighted graph on `n ≥ 2` vertices. -/
theorem deterministic_mincut_of_hierarchyBound (hb : HierarchyBound a h) (ha : ∀ r, 1 ≤ a r)
    (hma : Monotone a) (hh : Monotone h) (hn : 2 ≤ Fintype.card V) :
    ∃ D : DTree (Finset V) ℝ (Option (Finset V)) (detBudget a h (Fintype.card V)),
      ∀ G : WeightedGraph V, ∃ S, D.eval G.cut = some S ∧ IsMinCut G S := by
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  refine ⟨(detMinCut hb ha).toDTree _, fun G => ⟨_, ?_, (detMinCut_spec hb ha hma hh G hn).1⟩⟩
  exact toDTree_eval _ _ (detMinCut_spec hb ha hma hh G hn).2

end DetMinCut
end CutQueryComplexity
