import CutQueryComplexity.DirectedMincut.SmallShore
import Mathlib.Probability.Distributions.Uniform

/-! # From terminal cuts to the global minimum cut (D5; source `thm:global-reduction`)

A candidate is a shore with a claimed value. It is `Valid` when the shore is nonempty and proper
and the value is its outgoing cut, and `Opt` when, in addition, the cut is a global minimum
(`globalMin`).

The terminal routine is abstract: for every ordered pair `a ≠ b`, a randomized program `T a b`
whose every output is an `a`–`b` shore with its true value (`TermSpec.valid`), and whose output
is a minimum `a`–`b` cut with probability at least `1 − ζ` (`TermSpec.exact`). It runs on the
original graph.

`global`: run the small-shore procedure (`smallShore`). Fix a root `a` and draw `K` vertices
uniformly with replacement. For every sample `v ≠ a`, run `T a v` and `T v a`, keeping the least
candidate (`chain`).

`global_solves`: the output is optimal with probability at least `1 − (1 − h/n)^K − ζ`. Fix one
global minimum cut `S*`. If a shore of `S*` has size at most `h`, the small-shore candidate is
already optimal. Otherwise each sample lands on the side away from `a` with probability greater
than `h/n`. One terminal call across `S*` then has value `λ*` with probability at least
`1 − ζ`, and every other candidate is a valid cut. Only that one call needs to succeed, so no
union bound over the calls is used.
-/

namespace CutQueryComplexity
namespace DirectedMincut

open Finset Probability
open scoped ENNReal

noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]

/-! ## Candidates -/

/-- The global minimum over nonempty proper shores. -/
def globalMin (G : DiGraph V) : ℕ := sInf {k | ∃ S : Finset V, S.Nonempty ∧ S ≠ univ ∧ G.out S = k}

omit [LinearOrder V] in
theorem globalMin_le (G : DiGraph V) {S : Finset V} (h1 : S.Nonempty) (h2 : S ≠ univ) :
    globalMin G ≤ G.out S := Nat.sInf_le ⟨S, h1, h2, rfl⟩

omit [LinearOrder V] in
theorem exists_globalMin (G : DiGraph V) (hn : 2 ≤ Fintype.card V) :
    ∃ S : Finset V, S.Nonempty ∧ S ≠ univ ∧ G.out S = globalMin G := by
  obtain ⟨v⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hne : ({v} : Finset V) ≠ univ := fun h => by
    have := congrArg card h; simp at this; omega
  exact Nat.sInf_mem (s := {k | ∃ S : Finset V, S.Nonempty ∧ S ≠ univ ∧ G.out S = k})
    ⟨_, {v}, singleton_nonempty v, hne, rfl⟩

/-- A valid candidate: a nonempty proper shore with its true value. -/
def Valid (G : DiGraph V) (r : Finset V × ℕ) : Prop :=
  r.1.Nonempty ∧ r.1 ≠ univ ∧ r.2 = G.out r.1

/-- An optimal candidate. -/
def Opt (G : DiGraph V) (r : Finset V × ℕ) : Prop := Valid G r ∧ G.out r.1 = globalMin G

/-- Keep the better candidate. -/
def better (best r : Finset V × ℕ) : Finset V × ℕ := if r.2 < best.2 then r else best

omit [LinearOrder V] in
theorem better_valid {G : DiGraph V} {best r : Finset V × ℕ} (hb : Valid G best)
    (hr : Valid G r) : Valid G (better best r) := by
  unfold better; split_ifs <;> assumption

omit [LinearOrder V] in
theorem better_opt_left {G : DiGraph V} {best r : Finset V × ℕ} (hb : Opt G best)
    (hr : Valid G r) : Opt G (better best r) := by
  unfold better
  split_ifs with h
  · exfalso
    have := globalMin_le G hr.1 hr.2.1
    rw [hr.2.2, hb.1.2.2, hb.2] at h
    omega
  · exact hb

omit [LinearOrder V] in
theorem better_opt_right {G : DiGraph V} {best r : Finset V × ℕ} (hb : Valid G best)
    (hr : Opt G r) : Opt G (better best r) := by
  unfold better
  split_ifs with h
  · exact hr
  · refine ⟨hb, le_antisymm ?_ (globalMin_le G hb.1 hb.2.1)⟩
    rw [← hb.2.2, ← hr.2]
    rw [hr.1.2.2] at h
    omega

/-! ## The terminal routine -/

/-- The contract of an abstract terminal routine on one graph. -/
structure TermSpec (G : DiGraph V) {qst : ℕ}
    (T : V → V → RTree (Finset V) ℕ (Finset V × ℕ) qst) (ζ : ℝ) : Prop where
  valid : ∀ a b, a ≠ b → ∀ r ∈ ((T a b).eval G.out).support,
    a ∈ r.1 ∧ b ∉ r.1 ∧ r.2 = G.out r.1
  exact : ∀ a b, a ≠ b →
    mass ((T a b).eval G.out) (fun r => ¬ G.out r.1 = stMin G a b) ≤ ENNReal.ofReal ζ

theorem mass_eq_zero_of_support {α : Type} {p : PMF α} {P : α → Prop}
    (h : ∀ x ∈ p.support, P x) : mass p (fun x => ¬ P x) = 0 := by
  rw [mass_eq_tsum]
  refine ENNReal.tsum_eq_zero.mpr fun x => ?_
  by_cases hx : P x
  · simp [hx]
  · simp only [hx, not_false_eq_true, ite_true]
    by_contra hne
    exact hx (h x ((PMF.mem_support_iff p x).mpr hne))

/-- Run the terminal routine on each listed pair, keeping the best candidate. -/
def chain {qst : ℕ} (T : V → V → RTree (Finset V) ℕ (Finset V × ℕ) qst) :
    (ps : List (V × V)) → Finset V × ℕ → RTree (Finset V) ℕ (Finset V × ℕ) (ps.length * qst)
  | [], best => RTree.pure (PMF.pure best)
  | p :: ps, best => ((T p.1 p.2).bind fun r => chain T ps (better best r)).cast
      (by simp only [List.length_cons]; ring)

variable {G : DiGraph V} {qst : ℕ} {T : V → V → RTree (Finset V) ℕ (Finset V × ℕ) qst} {ζ : ℝ}

omit [LinearOrder V] in
theorem valid_of_term (hT : TermSpec G T ζ) {a b : V} (hab : a ≠ b) {r : Finset V × ℕ}
    (hr : r ∈ ((T a b).eval G.out).support) : Valid G r := by
  obtain ⟨ha, hb, hv⟩ := hT.valid a b hab r hr
  exact ⟨⟨a, ha⟩, fun h => hb (h ▸ mem_univ b), hv⟩

omit [LinearOrder V] in
/-- An optimal best candidate stays optimal. -/
theorem chain_opt_of_opt (hT : TermSpec G T ζ) :
    ∀ (ps : List (V × V)), (∀ p ∈ ps, p.1 ≠ p.2) → ∀ best, Opt G best →
      mass ((chain T ps best).eval G.out) (fun r => ¬ Opt G r) = 0 := by
  intro ps
  induction ps with
  | nil => intro _ best hb; simp [chain, hb]
  | cons p ps ih =>
      intro hps best hb
      simp only [chain, RTree.eval_cast, RTree.eval_bind]
      have hp := hps p (List.mem_cons_self ..)
      have := mass_bind_le_add ((T p.1 p.2).eval G.out) (fun r => (chain T ps (better best r)).eval G.out)
        (fun r => ¬ Valid G r) (fun r => ¬ Opt G r) (δ := 0) (ε := 0)
        (le_of_eq (mass_eq_zero_of_support fun r hr => valid_of_term hT hp hr))
        (fun r hr => le_of_eq (ih (fun q hq => hps q (List.mem_cons_of_mem _ hq)) _
          (better_opt_left hb (not_not.mp hr))))
      simpa using this

omit [LinearOrder V] in
/-- **One designated good pair suffices.** -/
theorem chain_opt (hT : TermSpec G T ζ) :
    ∀ (ps : List (V × V)), (∀ p ∈ ps, p.1 ≠ p.2) →
      (∃ p ∈ ps, stMin G p.1 p.2 = globalMin G) → ∀ best, Valid G best →
      mass ((chain T ps best).eval G.out) (fun r => ¬ Opt G r) ≤ ENNReal.ofReal ζ := by
  intro ps
  induction ps with
  | nil => intro _ ⟨p, hp, _⟩; simp at hp
  | cons p ps ih =>
      intro hps hgood best hb
      have hp := hps p (List.mem_cons_self ..)
      have hps' : ∀ q ∈ ps, q.1 ≠ q.2 := fun q hq => hps q (List.mem_cons_of_mem _ hq)
      simp only [chain, RTree.eval_cast, RTree.eval_bind]
      by_cases hhead : stMin G p.1 p.2 = globalMin G
      · -- the head call is the designated one
        have hbad : mass ((T p.1 p.2).eval G.out)
            (fun r => ¬ (Valid G r ∧ G.out r.1 = stMin G p.1 p.2)) ≤ ENNReal.ofReal ζ := by
          calc _ ≤ mass ((T p.1 p.2).eval G.out) (fun r => ¬ Valid G r) +
                mass ((T p.1 p.2).eval G.out) (fun r => ¬ G.out r.1 = stMin G p.1 p.2) := by
                rw [mass, mass, mass]
                refine le_trans (MeasureTheory.measure_mono fun r hr => ?_) (MeasureTheory.measure_union_le _ _)
                simp only [Set.mem_ofPred_eq, not_and_or] at hr
                rcases hr with h | h
                · exact Or.inl h
                · exact Or.inr h
            _ ≤ 0 + ENNReal.ofReal ζ := add_le_add
                (le_of_eq (mass_eq_zero_of_support fun r hr => valid_of_term hT hp hr))
                (hT.exact _ _ hp)
            _ = _ := zero_add _
        have := mass_bind_le_add ((T p.1 p.2).eval G.out)
          (fun r => (chain T ps (better best r)).eval G.out)
          (fun r => ¬ (Valid G r ∧ G.out r.1 = stMin G p.1 p.2)) (fun r => ¬ Opt G r)
          (ε := 0) hbad (fun r hr => by
            obtain ⟨hv, he⟩ := not_not.mp hr
            exact le_of_eq (chain_opt_of_opt hT ps hps' _
              (better_opt_right hb ⟨hv, he.trans hhead⟩)))
        simpa using this
      · -- the designated pair is later
        obtain ⟨q, hq, hqgood⟩ := hgood
        have hq' : q ∈ ps := by
          rcases List.mem_cons.mp hq with rfl | hq
          · exact absurd hqgood hhead
          · exact hq
        have := mass_bind_le_add ((T p.1 p.2).eval G.out)
          (fun r => (chain T ps (better best r)).eval G.out)
          (fun r => ¬ Valid G r) (fun r => ¬ Opt G r) (δ := 0)
          (le_of_eq (mass_eq_zero_of_support fun r hr => valid_of_term hT hp hr))
          (fun r hr => ih hps' ⟨q, hq', hqgood⟩ _ (better_valid hb (not_not.mp hr)))
        simpa using this

omit [LinearOrder V] in
theorem chain_valid (hT : TermSpec G T ζ) :
    ∀ (ps : List (V × V)), (∀ p ∈ ps, p.1 ≠ p.2) → ∀ best, Valid G best →
      mass ((chain T ps best).eval G.out) (fun r => ¬ Valid G r) = 0 := by
  intro ps
  induction ps with
  | nil => intro _ best hb; simp [chain, hb]
  | cons p ps ih =>
      intro hps best hb
      simp only [chain, RTree.eval_cast, RTree.eval_bind]
      have hp := hps p (List.mem_cons_self ..)
      have := mass_bind_le_add ((T p.1 p.2).eval G.out) (fun r => (chain T ps (better best r)).eval G.out)
        (fun r => ¬ Valid G r) (fun r => ¬ Valid G r) (δ := 0) (ε := 0)
        (le_of_eq (mass_eq_zero_of_support fun r hr => valid_of_term hT hp hr))
        (fun r hr => le_of_eq (ih (fun q hq => hps q (List.mem_cons_of_mem _ hq)) _
          (better_valid hb (not_not.mp hr))))
      simpa using this

/-! ## Sampling and the global procedure -/

/-- The ordered terminal pairs for the samples `σ`, with root `a`. -/
def pairsOf (a : V) {K : ℕ} (σ : Fin K → V) : List (V × V) :=
  ((List.ofFn σ).filter fun v => v ≠ a).flatMap fun v => [(a, v), (v, a)]

omit [Fintype V] [LinearOrder V] in
theorem pairsOf_length (a : V) {K : ℕ} (σ : Fin K → V) : (pairsOf a σ).length ≤ 2 * K := by
  have hlen : ∀ l : List V, (l.flatMap fun v => [(a, v), (v, a)]).length = 2 * l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons x l ih => simp [List.flatMap_cons, ih]; ring
  unfold pairsOf
  rw [hlen]
  exact Nat.mul_le_mul_left 2 ((List.length_filter_le _ _).trans (by simp))

omit [Fintype V] [LinearOrder V] in
theorem pairsOf_ne (a : V) {K : ℕ} (σ : Fin K → V) : ∀ p ∈ pairsOf a σ, p.1 ≠ p.2 := by
  intro p hp
  simp only [pairsOf, List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  obtain ⟨v, ⟨-, hva⟩, rfl | rfl⟩ := hp
  · exact Ne.symm hva
  · exact hva

/-- The sampling phase from a starting candidate. -/
def samplePhase [Nonempty V] (a : V) (K : ℕ) (T : V → V → RTree (Finset V) ℕ (Finset V × ℕ) qst)
    (best : Finset V × ℕ) : RTree (Finset V) ℕ (Finset V × ℕ) (2 * K * qst) :=
  RTree.mix ((PMF.uniformOfFintype (Fin K → V)).map fun σ =>
    (chain T (pairsOf a σ) best).weaken (Nat.mul_le_mul_right qst (pairsOf_length a σ)))

/-- **The global procedure.** -/
def global [Nonempty V] (k h K : ℕ) (a : V) (T : V → V → RTree (Finset V) ℕ (Finset V × ℕ) qst) :
    RTree (Finset V) ℕ (Finset V × ℕ) (2 * Fintype.card V + (learnFuel (V := V) h * (3 + 3 * k) +
      (learnFuel (V := V) h * (3 + 3 * k) + 1)) + 2 * K * qst) :=
  (RTree.ofDeterministic (smallShore k h)).bind fun r0 => samplePhase a K T r0

omit [DecidableEq V] [LinearOrder V] in
/-- The probability that all `K` uniform samples land in `A`. -/
theorem mass_all_mem [Nonempty V] (A : Finset V) (K : ℕ) :
    (mass (PMF.uniformOfFintype (Fin K → V)) (fun σ => ∀ i, σ i ∈ A)).toReal =
      ((A.card : ℝ) / Fintype.card V) ^ K := by
  have hset : {σ : Fin K → V | ∀ i, σ i ∈ A} = ↑(Fintype.piFinset fun _ : Fin K => A) := by
    ext σ; simp
  rw [mass, hset, PMF.toOuterMeasure_uniformOfFintype_apply, ENNReal.toReal_div]
  simp [Fintype.card_piFinset, div_pow]

/-- **The global reduction** (source `thm:global-reduction`). -/
theorem global_solves [Nonempty V] {X : Type} (graph : X → DiGraph V) (hsimple : ∀ x, (graph x).Simple)
    (hn : 2 ≤ Fintype.card V) {k : ℕ} (hk : Fintype.card V ≤ 2 ^ k) (h K : ℕ)
    (hh : h ≤ Fintype.card V) (a : V)
    (hT : ∀ x, TermSpec (graph x) T ζ) (hζ : 0 ≤ ζ) :
    (global k h K a T).SolvesWithError (fun x => (graph x).out) (fun x => Opt (graph x))
      ((1 - (h : ℝ) / Fintype.card V) ^ K + ζ) := by
  intro x
  set G := graph x
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
  have hbase0 : 0 ≤ 1 - (h : ℝ) / Fintype.card V := by
    rw [sub_nonneg, div_le_one hnR]; exact_mod_cast hh
  have hmiss0 : 0 ≤ (1 - (h : ℝ) / Fintype.card V) ^ K := pow_nonneg hbase0 K
  rw [RTree.successProb_eq]
  apply success_of_failure_le _ _ (add_nonneg hmiss0 hζ)
  rw [global, RTree.eval_bind]
  -- the deterministic small-shore candidate
  set r0 := (smallShore k h).eval G.out
  have hdet : (RTree.ofDeterministic (smallShore k h)).eval G.out = PMF.pure r0 := by
    rw [RTree.eval, RTree.run_ofDeterministic, PMF.pure_map]; rfl
  rw [hdet, PMF.pure_bind]
  obtain ⟨hr0ne, hr0pr, hr0v, -, hr0small⟩ := smallShore_correct (hsimple x) hn hk h
  have hr0 : Valid G r0 := ⟨hr0ne, hr0pr, hr0v⟩
  obtain ⟨S, hS1, hS2, hSmin⟩ := exists_globalMin G hn
  simp only [samplePhase, RTree.eval_mix, PMF.bind_map, Function.comp_def, RTree.eval_weaken]
  by_cases hsmall : S.card ≤ h ∨ Sᶜ.card ≤ h
  · -- the small-shore candidate is already optimal
    have hopt : Opt G r0 := ⟨hr0, le_antisymm (by rw [← hSmin]; exact hr0small S hS1 hS2 hsmall)
      (globalMin_le G hr0ne hr0pr)⟩
    have := mass_bind_le_add (PMF.uniformOfFintype (Fin K → V))
      (fun σ => (chain T (pairsOf a σ) r0).eval G.out) (fun _ => False) (fun r => ¬ Opt G r)
      (δ := 0) (ε := 0) (by simp) (fun σ _ => le_of_eq
        (chain_opt_of_opt (hT x) _ (pairsOf_ne a σ) r0 hopt))
    refine this.trans ?_
    simp only [add_zero]
    exact bot_le
  · push Not at hsmall
    obtain ⟨hbig1, hbig2⟩ := hsmall
    -- the side of the root
    set A := if a ∈ S then S else Sᶜ
    have hAc : h + 1 ≤ Aᶜ.card := by
      by_cases ha : a ∈ S
      · show h + 1 ≤ (if a ∈ S then S else Sᶜ)ᶜ.card
        simp only [ha, ↓reduceIte]; omega
      · show h + 1 ≤ (if a ∈ S then S else Sᶜ)ᶜ.card
        simp only [ha, ↓reduceIte, compl_compl]; omega
    have hmiss : mass (PMF.uniformOfFintype (Fin K → V)) (fun σ => ∀ i, σ i ∈ A) ≤
        ENNReal.ofReal ((1 - (h : ℝ) / Fintype.card V) ^ K) := by
      rw [← ENNReal.ofReal_toReal (mass_ne_top _ _), mass_all_mem]
      have hAcard : A.card + Aᶜ.card = Fintype.card V := card_add_card_compl A
      refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) ?_ K)
      rw [div_le_iff₀ hnR, sub_mul, div_mul_cancel₀ _ hnR.ne', one_mul]
      have : (A.card : ℝ) + Aᶜ.card = Fintype.card V := by exact_mod_cast hAcard
      have : (h : ℝ) + 1 ≤ Aᶜ.card := by exact_mod_cast hAc
      linarith
    have := mass_bind_le_add (PMF.uniformOfFintype (Fin K → V))
      (fun σ => (chain T (pairsOf a σ) r0).eval G.out) (fun σ => ∀ i, σ i ∈ A)
      (fun r => ¬ Opt G r) hmiss (fun σ hσ => by
        push Not at hσ
        obtain ⟨i, hi⟩ := hσ
        have hvA : σ i ≠ a := fun he => by
          apply hi; rw [he]
          show a ∈ (if a ∈ S then S else Sᶜ)
          by_cases ha : a ∈ S
          · simp only [ha, ↓reduceIte]
          · simp only [ha, ↓reduceIte, mem_compl, not_false_eq_true]
        refine chain_opt (hT x) _ (pairsOf_ne a σ) ?_ r0 hr0
        -- the designated pair across `S`
        have hmem : σ i ∈ (List.ofFn σ).filter fun v => v ≠ a := by
          simp only [List.mem_filter, List.mem_ofFn, decide_eq_true_eq]
          exact ⟨⟨i, rfl⟩, hvA⟩
        by_cases ha : a ∈ S
        · refine ⟨(a, σ i), ?_, ?_⟩
          · simp only [pairsOf, List.mem_flatMap]; exact ⟨σ i, hmem, by simp⟩
          · have hiS : σ i ∉ S := fun h' => hi (by
              show σ i ∈ (if a ∈ S then S else Sᶜ); simp only [ha, ↓reduceIte]; exact h')
            refine le_antisymm ?_ ?_
            · rw [← hSmin]; exact stMin_le G ha hiS
            · obtain ⟨S', hs', ht', hS'⟩ := exists_stMin G (Ne.symm hvA)
              rw [← hS']
              exact globalMin_le G ⟨a, hs'⟩ fun hu => ht' (hu ▸ mem_univ _)
        · refine ⟨(σ i, a), ?_, ?_⟩
          · simp only [pairsOf, List.mem_flatMap]; exact ⟨σ i, hmem, by simp⟩
          · have hiS : σ i ∈ S := by
              by_contra h'
              exact hi (by show σ i ∈ (if a ∈ S then S else Sᶜ); simp only [ha, ↓reduceIte]; exact mem_compl.mpr h')
            refine le_antisymm ?_ ?_
            · rw [← hSmin]; exact stMin_le G hiS ha
            · obtain ⟨S', hs', ht', hS'⟩ := exists_stMin G hvA
              rw [← hS']
              exact globalMin_le G ⟨σ i, hs'⟩ fun hu => ht' (hu ▸ mem_univ _))
    rw [ENNReal.ofReal_add hmiss0 hζ]
    exact this

/-! ## Instantiation with the LP-based terminal routine -/

/-- Extraction always returns an `s`–`t` shore with its queried value, for every LP point. -/
theorem extract_valid (G : DiGraph V) {s t : V} (hst : s ≠ t) {k : ℕ}
    (hk : Fintype.card V ≤ 2 ^ k) (τ : ℝ) (p : LPPoint V) :
    let r := (extract s t k τ p).eval G.out
    s ∈ r.1 ∧ t ∉ r.1 ∧ r.2 = G.out r.1 := by
  have hI : BfsInv G (okOf p τ) s {s} ∅ :=
    ⟨mem_singleton_self s, empty_subset _, fun w hw => by
      rw [mem_singleton.mp hw], fun u hu => absurd hu (Finset.notMem_empty u)⟩
  obtain ⟨hsW, -, -⟩ := bfs_correct G (okOf p τ) s hk (2 * Fintype.card V) {s} ∅ hI (by simp)
  simp only [extract, DTree.eval_bind, DTree.eval_query, DTree.eval_pure]
  by_cases htW : t ∈ (bfs k (okOf p τ) (2 * Fintype.card V) {s} ∅).eval G.out
  · simp only [htW, ↓reduceIte, mem_singleton, true_and]
    exact ⟨Ne.symm hst, trivial⟩
  · simp only [htW, ↓reduceIte, not_false_eq_true, true_and]
    exact ⟨hsW, trivial⟩

/-- The terminal routine: an LP solver followed by extraction. -/
def lpTerminal {qLP : ℕ} (lp : V → V → RTree (Finset V) ℕ (LPPoint V) qLP) (k : ℕ) (τ : ℝ)
    (a b : V) : RTree (Finset V) ℕ (Finset V × ℕ) (qLP + (2 * Fintype.card V * (3 + 3 * k) + 1)) :=
  (lp a b).bind fun p => RTree.ofDeterministic (extract a b k τ p)

/-- **The LP-based terminal routine meets the terminal contract.** -/
theorem termSpec_lpTerminal (hG : G.Simple) {k : ℕ} (hk : Fintype.card V ≤ 2 ^ k)
    {τ ε : ℝ} (hτ : 0 < τ) (hn : 8 * (Fintype.card V : ℝ) ^ 2 * τ ≤ 1) (hε : ε ≤ τ / 16)
    (hζ : 0 ≤ ζ) {qLP : ℕ} (lp : V → V → RTree (Finset V) ℕ (LPPoint V) qLP)
    (hlp : ∀ a b, a ≠ b → 1 - ζ ≤ (lp a b).successProb G.out (LPGood a b ε G)) :
    TermSpec G (lpTerminal lp k τ) ζ := by
  refine ⟨fun a b hab r hr => ?_, fun a b hab => ?_⟩
  · simp only [lpTerminal, RTree.eval_bind, PMF.mem_support_bind_iff] at hr
    obtain ⟨p, -, hr⟩ := hr
    have hdet : (RTree.ofDeterministic (extract a b k τ p)).eval G.out =
        PMF.pure ((extract a b k τ p).eval G.out) := by
      rw [RTree.eval, RTree.run_ofDeterministic, PMF.pure_map]; rfl
    rw [hdet, PMF.support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact extract_valid G hab hk τ p
  · have hsol := terminal_solves (X := Unit) (fun _ => G) (fun _ => hG) hab hk hτ hn hε hζ
      (lp a b) (fun _ => hlp a b hab) ()
    rw [RTree.successProb_eq] at hsol
    have hfail := failure_le_of_success _ _ hζ (by simpa only [mass] using hsol)
    refine le_trans (mass_mono _ fun r (hr : ¬ G.out r.1 = stMin G a b)
      (hgood : STGood a b G r) => hr hgood.2.2.1) ?_
    simpa [lpTerminal] using hfail

end

end DirectedMincut
end CutQueryComplexity
