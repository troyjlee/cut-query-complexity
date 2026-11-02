import CutQueryComplexity.GlobalSTReduction.Isolating
import CutQueryComplexity.GlobalSTReduction.Calls
import CutQueryComplexity.GlobalSTReduction.Sampling
import CutQueryComplexity.GlobalSTReduction.Budget
import CutQueryComplexity.GHReduction.GuideSampling

/-! # The global program and its two guarantees

The program `globalTree P r levels trials B`, with a public root `r`:

1. query `{r}` once; `({r}, value)` is the fallback candidate;
2. draw `trials` fresh threshold seeds (`independentSamples`);
3. for every seed and every level `i = 0, …, levels`, take the terminal sample
   `R = levelSample univ r i seed` (it always contains `r`); if `|R| ≥ 2`, run the
   isolating program `isolatingValuesCall R`, which also queries every returned
   shore's value (`levelCall`, `candidatesCall`);
4. return the proper candidate of least queried value (`select`), starting from
   the fallback.

Step 3 is one call program, compiled once at budget `B` and run with the family
`P` (`CallTree.interpRand`), so every call gets fresh randomness. The hidden
graph never enters a constructor; the minimum cut used below is a proof device.

* `globalTree_valid`: on every graph, every output is a proper shore with its
  exact value, for arbitrary s-t replies, including truncated runs.
* `globalTree_failure`: if each call misses a minimum shore with probability at
  most `δ`, `levels ≥ ⌈log₂(2|V|)⌉` and `B` covers the charged cost, the output
  fails to be a global minimum cut with probability at most
  `(7/8)^trials + δ · trials (levels + 1) (⌈log₂ |V|⌉ + |V|)`. The first term
  bounds "no trial isolates a vertex of a fixed optimum"; the second bounds "some
  call returned a non-minimum shore" (`mass_interpRand_compile_le`).
-/

set_option autoImplicit false

namespace CutQueryComplexity.GlobalSTReduction
noncomputable section
open scoped Classical ENNReal
open WeightedGraph Probability GHReduction GHReduction.Randomized

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Candidates of one level and of a list of levels -/

/-- Every isolating shore of `R` with its value, or nothing if `|R| < 2`. -/
def levelCall (R : Finset V) : CallProg V (List (Finset V × ℝ)) :=
  if 2 ≤ R.card then
    (CallProg.isolatingValuesCall R).map (fun table => (Finset.univ : Finset R).toList.map table)
  else CallProg.pure []

theorem holds_levelCall_any (read : Finset V → ℝ) (R : Finset V) :
    Holds read (anyReply V) (fun cs => ∀ c ∈ cs, c.2 = read c.1) (levelCall R) := by
  unfold levelCall
  split_ifs
  · rw [holds_map]
    refine (holds_isolatingValuesCall_any read R).mono (fun table h c hc => ?_)
    obtain ⟨v, -, rfl⟩ := List.mem_map.mp hc
    exact h v
  · intro c hc
    simp at hc

theorem holds_levelCall_opt (G : WeightedGraph V) (R : Finset V) :
    Holds G.cut (optReply G)
      (fun cs => 2 ≤ R.card → ∀ v ∈ R, ∃ c ∈ cs, IsMinTraceCut G R {v} c.1 ∧ c.2 = G.cut c.1)
      (levelCall R) := by
  unfold levelCall
  split_ifs with hR
  · rw [holds_map]
    refine (holds_isolatingValuesCall G R hR).mono (fun table h _ v hv => ?_)
    exact ⟨table ⟨v, hv⟩,
      List.mem_map.mpr ⟨⟨v, hv⟩, Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩, h ⟨v, hv⟩⟩
  · intro h
    omega

theorem cost_levelCall {Q : ℕ → ℕ} (R : Finset V) (hn : 0 < Fintype.card V)
    (hQ : SizeRegular (Fintype.card V) Q) :
    CostWithin Q (levelCall R) (levelBudget (Fintype.card V) Q) := by
  unfold levelCall levelBudget
  split_ifs
  · refine within_map _ ((cost_isolatingValuesCall R hn hQ).mono ?_)
    have h1 : Nat.clog 2 R.card ≤ Nat.clog 2 (Fintype.card V) :=
      Nat.clog_mono_right _ (Finset.card_le_univ R)
    have h2 := Finset.card_le_univ R
    have h3 := Nat.mul_le_mul_right (Q (Fintype.card V)) (Nat.add_le_add_right h1 2)
    omega
  · trivial

theorem calls_levelCall (R : Finset V) :
    CallsWithin (levelCall R) (Nat.clog 2 (Fintype.card V) + Fintype.card V) := by
  unfold levelCall
  split_ifs
  · refine within_map _ ((calls_isolatingValuesCall R).mono ?_)
    have h1 : Nat.clog 2 R.card ≤ Nat.clog 2 (Fintype.card V) :=
      Nat.clog_mono_right _ (Finset.card_le_univ R)
    have h2 := Finset.card_le_univ R
    omega
  · trivial

/-- The candidates of all listed terminal sets, in order. -/
def candidatesCall : List (Finset V) → CallProg V (List (Finset V × ℝ))
  | [] => CallProg.pure []
  | R :: Rs => (levelCall R).bind (fun c => (candidatesCall Rs).map (fun cs => c ++ cs))

theorem holds_candidatesCall_any (read : Finset V → ℝ) (Rs : List (Finset V)) :
    Holds read (anyReply V) (fun cs => ∀ c ∈ cs, c.2 = read c.1) (candidatesCall Rs) := by
  induction Rs with
  | nil => intro c hc; simp at hc
  | cons R Rs ih =>
      rw [candidatesCall, holds_bind]
      refine (holds_levelCall_any read R).mono (fun c hc => ?_)
      rw [holds_map]
      exact ih.mono (fun cs hcs x hx => (List.mem_append.mp hx).elim (hc x) (hcs x))

/-- Each listed terminal set with at least two terminals contributes, for each of
its terminals, a minimum isolating shore with its exact value. -/
def Covers (G : WeightedGraph V) (Rs : List (Finset V)) (cs : List (Finset V × ℝ)) : Prop :=
  ∀ R ∈ Rs, 2 ≤ R.card → ∀ v ∈ R, ∃ c ∈ cs, IsMinTraceCut G R {v} c.1 ∧ c.2 = G.cut c.1

theorem holds_candidatesCall_opt (G : WeightedGraph V) (Rs : List (Finset V)) :
    Holds G.cut (optReply G) (Covers G Rs) (candidatesCall Rs) := by
  induction Rs with
  | nil => intro R hR; simp at hR
  | cons R Rs ih =>
      rw [candidatesCall, holds_bind]
      refine (holds_levelCall_opt G R).mono (fun c hc => ?_)
      rw [holds_map]
      refine ih.mono (fun cs hcs R' hR' h2 v hv => ?_)
      rcases List.mem_cons.mp hR' with rfl | hR'
      · obtain ⟨x, hx, hxv⟩ := hc h2 v hv
        exact ⟨x, List.mem_append_left _ hx, hxv⟩
      · obtain ⟨x, hx, hxv⟩ := hcs R' hR' h2 v hv
        exact ⟨x, List.mem_append_right _ hx, hxv⟩

theorem cost_candidatesCall {Q : ℕ → ℕ} (Rs : List (Finset V)) (hn : 0 < Fintype.card V)
    (hQ : SizeRegular (Fintype.card V) Q) :
    CostWithin Q (candidatesCall Rs) (Rs.length * levelBudget (Fintype.card V) Q) := by
  induction Rs with
  | nil => trivial
  | cons R Rs ih =>
      rw [candidatesCall, List.length_cons, Nat.succ_mul, Nat.add_comm]
      exact within_bind (cost_levelCall R hn hQ) (fun c => within_map _ ih)

theorem calls_candidatesCall (Rs : List (Finset V)) :
    CallsWithin (candidatesCall Rs)
      (Rs.length * (Nat.clog 2 (Fintype.card V) + Fintype.card V)) := by
  induction Rs with
  | nil => trivial
  | cons R Rs ih =>
      rw [candidatesCall, List.length_cons, Nat.succ_mul, Nat.add_comm]
      exact within_bind (calls_levelCall R) (fun c => within_map _ ih)

/-! ### Terminal samples -/

/-- The terminal samples of all trials and all levels `0, …, levels`. -/
def terminalSets {levels : ℕ} (r : V) (seeds : List (ThresholdSeed V levels)) :
    List (Finset V) :=
  seeds.flatMap (fun seed =>
    (List.range (levels + 1)).map (fun i => levelSample Finset.univ r i seed))

theorem terminalSets_length {levels : ℕ} (r : V) (seeds : List (ThresholdSeed V levels)) :
    (terminalSets r seeds).length = seeds.length * (levels + 1) := by
  induction seeds with
  | nil => simp [terminalSets]
  | cons seed seeds ih =>
      simp only [terminalSets, List.flatMap_cons, List.length_append, List.length_map,
        List.length_range, List.length_cons] at ih ⊢
      rw [ih]
      ring

theorem mem_terminalSets {levels : ℕ} (r : V) {seeds : List (ThresholdSeed V levels)}
    {seed : ThresholdSeed V levels} (hseed : seed ∈ seeds) {i : ℕ} (hi : i ≤ levels) :
    levelSample Finset.univ r i seed ∈ terminalSets r seeds :=
  List.mem_flatMap.mpr ⟨seed, hseed, List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega), rfl⟩⟩

/-! ### Selecting the best proper candidate -/

/-- Replace the current candidate by a proper one of strictly smaller reported value. -/
def better (best c : Finset V × ℝ) : Finset V × ℝ :=
  if ProperShore c.1 ∧ c.2 < best.2 then c else best

/-- The proper candidate of least reported value, starting from `start`. -/
def select (start : Finset V × ℝ) (cs : List (Finset V × ℝ)) : Finset V × ℝ :=
  cs.foldl better start

theorem select_valid (G : WeightedGraph V) {start : Finset V × ℝ} {cs : List (Finset V × ℝ)}
    (hs : ValidOutput G start) (hcs : ∀ c ∈ cs, c.2 = G.cut c.1) :
    ValidOutput G (select start cs) := by
  induction cs generalizing start with
  | nil => exact hs
  | cons c cs ih =>
      rw [select, List.foldl_cons]
      refine ih ?_ (fun x hx => hcs x (List.mem_cons_of_mem c hx))
      unfold better
      split_ifs with h
      · exact ⟨h.1, hcs c List.mem_cons_self⟩
      · exact hs

omit [DecidableEq V] in
theorem select_le_start (start : Finset V × ℝ) (cs : List (Finset V × ℝ)) :
    (select start cs).2 ≤ start.2 := by
  induction cs generalizing start with
  | nil => exact le_rfl
  | cons c cs ih =>
      rw [select, List.foldl_cons]
      refine (ih _).trans ?_
      unfold better
      split_ifs with h
      · exact h.2.le
      · exact le_rfl

omit [DecidableEq V] in
theorem select_le {start : Finset V × ℝ} {cs : List (Finset V × ℝ)} {c : Finset V × ℝ}
    (hc : c ∈ cs) (hp : ProperShore c.1) : (select start cs).2 ≤ c.2 := by
  induction cs generalizing start with
  | nil => simp at hc
  | cons c' cs ih =>
      rw [select, List.foldl_cons]
      rcases List.mem_cons.mp hc with rfl | hc
      · refine (select_le_start _ _).trans ?_
        unfold better
        split_ifs with h
        · exact le_rfl
        · push Not at h
          exact h hp
      · exact ih hc

/-- If every candidate carries its exact value and one is a global optimum, the
selection is a global optimum with its exact value. -/
theorem select_globalSuccess (G : WeightedGraph V) {start : Finset V × ℝ}
    {cs : List (Finset V × ℝ)} (hs : ValidOutput G start) (hcs : ∀ c ∈ cs, c.2 = G.cut c.1)
    {c : Finset V × ℝ} (hc : c ∈ cs) (hmin : IsMinCut G c.1) :
    GlobalSuccess G (select start cs) := by
  have hv := select_valid G hs hcs
  refine ⟨⟨hv.1, fun T hT => ?_⟩, hv.2⟩
  calc
    G.cut (select start cs).1 = (select start cs).2 := hv.2.symm
    _ ≤ c.2 := select_le hc hmin.1
    _ = G.cut c.1 := hcs c hc
    _ ≤ G.cut T := hmin.2 T hT

/-! ### The program -/

variable {Q : ℕ → ℕ}

/-- After the fallback value `x₀` of `{r}`: draw the seeds, run all levels as one
compiled call program, and select. -/
def searchTree (P : STPrograms Q) (r : V) (levels trials B : ℕ) (x₀ : ℝ) :
    RTree (Finset V) ℝ (Finset V × ℝ) B :=
  RTree.mix ((independentSamples (thresholdSeedPMF V levels) trials).map (fun seeds =>
    (CallTree.interpRand P (CallProg.compile Q (candidatesCall (terminalSets r seeds)) B)).map
      (fun o => select ({r}, x₀) (o.getD []))))

/-- The global program: one fallback query, then the search. -/
def globalTree (P : STPrograms Q) (r : V) (levels trials B : ℕ) :
    RTree (Finset V) ℝ (Finset V × ℝ) (1 + B) :=
  (RTree.query {r} (fun x₀ => searchTree P r levels trials B x₀)).cast (Nat.add_comm _ _)

theorem globalTree_eval (P : STPrograms Q) (r : V) (levels trials B : ℕ)
    (read : Finset V → ℝ) :
    (globalTree P r levels trials B).eval read =
      (independentSamples (thresholdSeedPMF V levels) trials).bind (fun seeds =>
        ((CallTree.interpRand P (CallProg.compile Q (candidatesCall (terminalSets r seeds)) B)).eval
          read).map (fun o => select ({r}, read {r}) (o.getD []))) := by
  simp only [globalTree, searchTree, RTree.eval_cast, RTree.eval_query, RTree.eval_mix,
    PMF.bind_map, RTree.eval_map, Function.comp_def]

/-- Every output on every graph is a proper shore with its exact value. -/
theorem globalTree_valid (P : STPrograms Q) (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V)
    (r : V) (levels trials B : ℕ) :
    ∀ out ∈ ((globalTree P r levels trials B).eval G.cut).support, ValidOutput G out := by
  intro out hout
  rw [globalTree_eval] at hout
  obtain ⟨seeds, _, hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  obtain ⟨o, ho, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
  apply select_valid G ⟨properShore_singleton r hn, rfl⟩
  cases o with
  | none => intro c hc; simp at hc
  | some cs =>
      exact support_interpRand_compile_some P G.cut _ B
        (holds_candidatesCall_any G.cut (terminalSets r seeds)) _ ho cs rfl

/-- The failure bound of the global program. -/
theorem globalTree_failure (P : STPrograms Q) {δ : ℝ≥0∞} (hP : OptFailsAtMost P δ)
    (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V) (hQ : SizeRegular (Fintype.card V) Q)
    (r : V) {levels trials B : ℕ} (hlevels : thresholdLevels (Fintype.card V) ≤ levels)
    (hB : trials * (levels + 1) * levelBudget (Fintype.card V) Q ≤ B) :
    mass ((globalTree P r levels trials B).eval G.cut) (fun out => ¬GlobalSuccess G out) ≤
      (7 / 8 : ℝ≥0∞) ^ trials +
        δ * ((trials * (levels + 1) * (Nat.clog 2 (Fintype.card V) + Fintype.card V) : ℕ) :
          ℝ≥0∞) := by
  have hpos : 0 < Fintype.card V := by omega
  obtain ⟨S, hS, hrS⟩ := exists_minCut_avoiding G hn r
  have hhit : hitLevel S.card ≤ levels := (hitLevel_le (Finset.card_le_univ S)).trans hlevels
  rw [globalTree_eval]
  refine mass_bind_le_add _ _
    (fun seeds => seeds.length ≠ trials ∨ ∀ seed ∈ seeds, ¬Hit S seed) _ ?_ ?_
  · refine (mass_or_le _ _ _).trans ?_
    have h0 : mass (independentSamples (thresholdSeedPMF V levels) trials)
        (fun seeds => seeds.length ≠ trials) = 0 := by
      refine le_antisymm ((mass_mono_on_support _ (Q := fun _ => False)
        (fun seeds hs h => h (independentSamples_length _ _ hs))).trans_eq (mass_false _)) bot_le
    rw [h0, zero_add]
    exact mass_all_independentSamples_le _ _ (mass_not_hit_le S hS.1.1 hhit) trials
  · intro seeds hgood
    push Not at hgood
    obtain ⟨hlen, seed, hseed, hHit⟩ := hgood
    obtain ⟨v, hvS, hRS⟩ := hit_trace hrS hHit
    set R := levelSample Finset.univ r (hitLevel S.card) seed with hRdef
    have hrR : r ∈ R := source_mem_levelSample (Finset.mem_univ r) _ _
    have hvR : v ∈ R := by
      have : v ∈ R ∩ S := by rw [hRS]; simp
      exact (Finset.mem_inter.mp this).1
    have hR2 : 2 ≤ R.card := by
      have hrv : r ≠ v := fun h => hrS (h ▸ hvS)
      have hsub : ({r, v} : Finset V) ⊆ R := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hrR
        · rw [Finset.mem_singleton.mp hx]
          exact hvR
      calc
        2 = ({r, v} : Finset V).card := (Finset.card_pair hrv).symm
        _ ≤ R.card := Finset.card_le_card hsub
    have hRmem : R ∈ terminalSets r seeds := mem_terminalSets r hseed hhit
    have hlenRs : (terminalSets r seeds).length = trials * (levels + 1) := by
      rw [terminalSets_length, hlen]
    have hpost : Holds G.cut (optReply G)
        (fun cs => (∀ c ∈ cs, c.2 = G.cut c.1) ∧ Covers G (terminalSets r seeds) cs)
        (candidatesCall (terminalSets r seeds)) :=
      holds_and ((holds_candidatesCall_any G.cut _).mono_ok (fun _ _ _ _ _ _ => trivial))
        (holds_candidatesCall_opt G _)
    have hcost := (cost_candidatesCall (Q := Q) (terminalSets r seeds) hpos hQ).mono
      (show (terminalSets r seeds).length * levelBudget (Fintype.card V) Q ≤ B by
        rw [hlenRs]; exact hB)
    have hmass := mass_interpRand_compile_le P hP G _ hcost
      (calls_candidatesCall (terminalSets r seeds)) hpost
    rw [hlenRs] at hmass
    rw [mass_map]
    refine (mass_mono _ (fun o ho => ?_)).trans hmass
    rintro ⟨cs, rfl, hvals, hcov⟩
    obtain ⟨c, hc, hX, -⟩ := hcov R hRmem hR2 v hvR
    exact ho (select_globalSuccess G ⟨properShore_singleton r hn, rfl⟩ hvals hc
      (isMinCut_of_isolating G hS hRS hrR hrS hX))

end
end CutQueryComplexity.GlobalSTReduction
