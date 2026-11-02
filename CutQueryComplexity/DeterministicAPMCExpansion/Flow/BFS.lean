import CutQueryComplexity.DeterministicAPMCExpansion.Flow.QueryProg

/-!
# Concrete BFS in the symmetric two-star residual network

The public state has a queue, unseen vertices and levels. It contains no graph
or realization witness. Every row is searched by `neighborProg`, whose queries
were defined before the hidden graph. Queue fuel counts discoveries and row
exhaustions, including the last failed search. Combinatorial queue invariants
adapt the existing directed BFS proof, without its public-orientation state.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.Flow

open Finset DirectedCertificate Certificate Prog
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

abbrev residualNetwork (G : WeightedGraph V) (a z : V → ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ)
    (hf : (directed (twoStar G a z)).Feasible f) : WeightedDiGraph (NetworkVertex V) :=
  DirectedUnitST.Repair.residual (directed (twoStar G a z)) f hf

theorem neighborProg_residual_spec (G : WeightedGraph V) (a z : V → ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ)
    (hf : (directed (twoStar G a z)).Feasible f)
    (u : NetworkVertex V) (U : Finset (NetworkVertex V)) :
    PositiveResult ((residualNetwork G a z f hf).c u) U
      ((neighborProg a z f u U).eval G.cut) :=
  neighborProg_correct G a z f hf u U

structure BFSData (V : Type) where
  queue : List (NetworkVertex V)
  unseen : Finset (NetworkVertex V)
  level : NetworkVertex V → ℕ

namespace BFSData

def work (data : BFSData V) : ℕ := 2 * data.unseen.card + data.queue.length

def drop (data : BFSData V) : BFSData V := { data with queue := data.queue.tail }

def discover (data : BFSData V) (u v : NetworkVertex V) : BFSData V :=
  { queue := data.queue ++ [v]
    unseen := data.unseen.erase v
    level := Function.update data.level v (data.level u + 1) }

theorem work_drop (data : BFSData V) {u : NetworkVertex V}
    {xs : List (NetworkVertex V)} (hq : data.queue = u :: xs) :
    data.drop.work + 1 = data.work := by
  simp only [work, drop, hq, List.tail_cons, List.length_cons]
  omega

theorem work_discover (data : BFSData V) (u v : NetworkVertex V)
    (hv : v ∈ data.unseen) : (data.discover u v).work + 1 = data.work := by
  have hn : 0 < data.unseen.card := card_pos.mpr ⟨v, hv⟩
  simp only [work, discover, card_erase_of_mem hv, List.length_append,
    List.length_singleton]
  omega

end BFSData

def bfsRun (a z : V → ℕ) (f : NetworkVertex V → NetworkVertex V → ℝ) :
    ℕ → BFSData V → Prog (Finset V) ℝ (BFSData V)
  | 0, data => .pure data
  | fuel + 1, data => match data.queue with
    | [] => .pure data
    | u :: _ => (neighborProg a z f u data.unseen).bind fun answer =>
        match answer with
        | none => bfsRun a z f fuel data.drop
        | some v =>
            if v ∈ data.unseen then bfsRun a z f fuel (data.discover u v)
            else .pure data

theorem bfsRun_cost (read : Finset V → ℝ) (a z : V → ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ) (fuel : ℕ) (data : BFSData V) :
    (bfsRun a z f fuel data).cost read ≤ fuel * neighborBudget V := by
  induction fuel generalizing data with
  | zero => simp [bfsRun]
  | succ fuel ih =>
      rw [bfsRun]
      cases hq : data.queue with
      | nil => simp
      | cons u xs =>
          simp only [Prog.cost_bind]
          have hc := neighborProg_cost read a z f u data.unseen
          cases hr : (neighborProg a z f u data.unseen).eval read with
          | none =>
              change (neighborProg a z f u data.unseen).cost read +
                (bfsRun a z f fuel data.drop).cost read ≤ (fuel + 1) * neighborBudget V
              have hi := ih data.drop
              rw [Nat.succ_mul]
              omega
          | some v =>
              change (neighborProg a z f u data.unseen).cost read +
                (if v ∈ data.unseen then bfsRun a z f fuel (data.discover u v)
                  else Prog.pure data).cost read ≤ (fuel + 1) * neighborBudget V
              split_ifs
              · have hi := ih (data.discover u v)
                rw [Nat.succ_mul]
                omega
              · simp only [Prog.cost_pure, Nat.add_zero]
                rw [Nat.succ_mul]
                omega

theorem bfsRun_complete (G : WeightedGraph V) (a z : V → ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ)
    (hf : (directed (twoStar G a z)).Feasible f)
    (fuel : ℕ) (data : BFSData V) (hwork : data.work ≤ fuel) :
    ((bfsRun a z f fuel data).eval G.cut).queue = [] := by
  induction fuel generalizing data with
  | zero =>
      apply List.eq_nil_of_length_eq_zero
      change data.queue.length = 0
      unfold BFSData.work at hwork
      omega
  | succ fuel ih =>
      rw [bfsRun]
      cases hq : data.queue with
      | nil => exact hq
      | cons u xs =>
          simp only [Prog.eval_bind]
          have hs := neighborProg_correct G a z f hf u data.unseen
          cases hr : (neighborProg a z f u data.unseen).eval G.cut with
          | none =>
              apply ih data.drop
              have hw := data.work_drop hq
              omega
          | some v =>
              rw [hr] at hs
              have hv : v ∈ data.unseen := hs.1
              simp only [hv, ↓reduceIte]
              apply ih (data.discover u v)
              have hw := data.work_discover u v hv
              omega

def initialBFS (s : NetworkVertex V) : BFSData V where
  queue := [s]
  unseen := univ.erase s
  level := fun _ => 0

theorem initialBFS_work (s : NetworkVertex V) :
    (initialBFS s).work ≤ 2 * Fintype.card (NetworkVertex V) := by
  simp only [BFSData.work, initialBFS, card_erase_of_mem (mem_univ s),
    card_univ, List.length_singleton]
  have hn : 0 < Fintype.card (NetworkVertex V) := Fintype.card_pos_iff.mpr ⟨s⟩
  omega

def bfsProg (a z : V → ℕ) (f : NetworkVertex V → NetworkVertex V → ℝ)
    (s : NetworkVertex V) : Prog (Finset V) ℝ (BFSData V) :=
  bfsRun a z f (2 * Fintype.card (NetworkVertex V)) (initialBFS s)

theorem bfsProg_complete (G : WeightedGraph V) (a z : V → ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ)
    (hf : (directed (twoStar G a z)).Feasible f) (s : NetworkVertex V) :
    ((bfsProg a z f s).eval G.cut).queue = [] :=
  bfsRun_complete G a z f hf _ _ (initialBFS_work s)

theorem bfsProg_cost (read : Finset V → ℝ) (a z : V → ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ) (s : NetworkVertex V) :
    (bfsProg a z f s).cost read ≤
      2 * Fintype.card (NetworkVertex V) * neighborBudget V := bfsRun_cost read a z f _ _

/-- A mathematical positive-residual walk, used to prove the computed levels. -/
inductive PathAt (H : WeightedDiGraph (NetworkVertex V)) (s : NetworkVertex V) :
    NetworkVertex V → ℕ → Prop
  | nil : PathAt H s s 0
  | snoc {u v : NetworkVertex V} {d : ℕ} :
      PathAt H s u d → 0 < H.c u v → PathAt H s v (d + 1)

structure BFSInvariant (H : WeightedDiGraph (NetworkVertex V))
    (s : NetworkVertex V) (data : BFSData V) : Prop where
  source_seen : s ∉ data.unseen
  source_level : data.level s = 0
  queue_seen : ∀ v ∈ data.queue, v ∉ data.unseen
  queue_sorted : data.queue.Pairwise fun u v => data.level u ≤ data.level v
  seen_bound : ∀ u ∈ data.queue, ∀ v, v ∉ data.unseen → data.level v ≤ data.level u + 1
  processed : ∀ u, u ∉ data.unseen → u ∉ data.queue →
    ∀ v, 0 < H.c u v → v ∉ data.unseen ∧ data.level v ≤ data.level u + 1
  witness : ∀ v, v ∉ data.unseen → PathAt H s v (data.level v)
  level_bound : ∀ v, v ∉ data.unseen →
    data.level v < Fintype.card (NetworkVertex V) - data.unseen.card

theorem BFSInvariant.drop {H : WeightedDiGraph (NetworkVertex V)} {s : NetworkVertex V} {data : BFSData V}
    (h : BFSInvariant H s data)
    {u : NetworkVertex V} {xs : List (NetworkVertex V)} (hq : data.queue = u :: xs)
    (hzero : ∀ v ∈ data.unseen, H.c u v = 0) : BFSInvariant H s (data.drop) := by
  have htail (v : NetworkVertex V) (hv : v ∈ data.queue.tail) : v ∈ data.queue :=
    List.mem_of_mem_tail hv
  refine ⟨h.source_seen, h.source_level, ?_, h.queue_sorted.tail, ?_, ?_, h.witness,
    h.level_bound⟩
  · intro v hv
    exact h.queue_seen v (htail v hv)
  · intro a ha v hv
    exact h.seen_bound a (htail a ha) v hv
  · intro a ha hqueue v hpos
    by_cases hau : a = u
    · subst a
      have hv : v ∉ data.unseen := by
        intro hv
        rw [hzero v hv] at hpos
        exact (lt_irrefl 0) hpos
      exact ⟨hv, h.seen_bound u (by rw [hq]; simp) v hv⟩
    · apply h.processed a ha _ v hpos
      intro hm
      rw [hq] at hm
      rcases List.mem_cons.mp hm with he | he
      · exact hau he
      · apply hqueue
        simpa only [BFSData.drop, hq, List.tail_cons] using he

theorem BFSInvariant.discover {H : WeightedDiGraph (NetworkVertex V)} {s : NetworkVertex V}
    {data : BFSData V} (h : BFSInvariant H s data)
    {u v : NetworkVertex V} {xs : List (NetworkVertex V)} (hq : data.queue = u :: xs)
    (hv : v ∈ data.unseen) (hpos : 0 < H.c u v) :
    BFSInvariant H s (data.discover u v) := by
  let next := data.discover u v
  have hum : u ∈ data.queue := by rw [hq]; simp
  have hu : u ∉ data.unseen := h.queue_seen u hum
  have hsame (x : NetworkVertex V) (hx : x ∉ data.unseen) : next.level x = data.level x := by
    have hxv : x ≠ v := fun he => hx (he.symm ▸ hv)
    simp [next, BFSData.discover, Function.update_of_ne hxv]
  have hnew : next.level v = data.level u + 1 := by simp [next, BFSData.discover]
  have hseen (x : NetworkVertex V) (hx : x ∉ next.unseen) : x = v ∨ x ∉ data.unseen := by
    by_cases he : x = v
    · exact Or.inl he
    · exact Or.inr (fun hm => hx (mem_erase.mpr ⟨he, hm⟩))
  have hold (x : NetworkVertex V) (hx : x ∉ data.unseen) : x ∉ next.unseen :=
    fun hm => hx (mem_of_mem_erase hm)
  have hcount : Fintype.card (NetworkVertex V) - next.unseen.card =
      Fintype.card (NetworkVertex V) - data.unseen.card + 1 := by
    have hc := card_le_univ data.unseen
    have hp : 0 < data.unseen.card := card_pos.mpr ⟨v, hv⟩
    dsimp [next, BFSData.discover]
    rw [card_erase_of_mem hv]
    omega
  have hhead (x : NetworkVertex V) (hx : x ∈ data.queue) : data.level u ≤ data.level x := by
    rw [hq] at hx
    rcases List.mem_cons.mp hx with he | he
    · subst x; exact le_rfl
    · have hsorted := h.queue_sorted
      rw [hq, List.pairwise_cons] at hsorted
      exact hsorted.1 x he
  refine ⟨hold s h.source_seen, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsame s h.source_seen]
    exact h.source_level
  · intro x hx
    change x ∈ data.queue ++ [v] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hold x (h.queue_seen x hx)
    · have he : x = v := List.mem_singleton.mp hx
      subst x
      exact notMem_erase _ _
  · change (data.queue ++ [v]).Pairwise (fun a b => next.level a ≤ next.level b)
    apply List.pairwise_append.mpr
    refine ⟨?_, by simp, ?_⟩
    · apply List.Pairwise.imp_of_mem _ h.queue_sorted
      intro a b ha hb hab
      rw [hsame a (h.queue_seen a ha), hsame b (h.queue_seen b hb)]
      exact hab
    · intro a ha b hb
      have he : b = v := List.mem_singleton.mp hb
      subst b
      rw [hsame a (h.queue_seen a ha), hnew]
      exact h.seen_bound u hum a (h.queue_seen a ha)
  · intro a ha b hb
    change a ∈ data.queue ++ [v] at ha
    rcases List.mem_append.mp ha with haq | hav
    · rw [hsame a (h.queue_seen a haq)]
      rcases hseen b hb with hbeq | hbold
      · rw [hbeq, hnew]
        exact Nat.add_le_add_right (hhead a haq) 1
      · rw [hsame b hbold]
        exact h.seen_bound a haq b hbold
    · have he : a = v := List.mem_singleton.mp hav
      subst a
      rw [hnew]
      rcases hseen b hb with rfl | hb
      · rw [hnew]; omega
      · rw [hsame b hb]
        have ht := h.seen_bound u hum b hb
        omega
  · intro a ha hqa b hpos
    have hav : a ≠ v := by
      intro he
      subst a
      exact hqa (by simp [BFSData.discover])
    have hao : a ∉ data.unseen := (hseen a ha).resolve_left hav
    have hqao : a ∉ data.queue := fun hm => hqa (List.mem_append_left _ hm)
    obtain ⟨hbo, hstep⟩ := h.processed a hao hqao b hpos
    exact ⟨hold b hbo, by rwa [hsame a hao, hsame b hbo]⟩
  · intro x hx
    rcases hseen x hx with rfl | hx
    · rw [hnew]
      exact PathAt.snoc (h.witness u hu) hpos
    · rw [hsame x hx]
      exact h.witness x hx
  · intro x hx
    rw [hcount]
    rcases hseen x hx with rfl | hx
    · rw [hnew]
      exact Nat.add_lt_add_right (h.level_bound u hu) 1
    · rw [hsame x hx]
      exact (h.level_bound x hx).trans (Nat.lt_succ_self _)

theorem initialBFS_invariant (H : WeightedDiGraph (NetworkVertex V))
    (s : NetworkVertex V) : BFSInvariant H s (initialBFS s) := by
  have hseen (v : NetworkVertex V) (hv : v ∉ (univ : Finset (NetworkVertex V)).erase s) : v = s := by
    by_contra hne
    exact hv (mem_erase.mpr ⟨hne, mem_univ v⟩)
  have hn : 0 < Fintype.card (NetworkVertex V) := Fintype.card_pos_iff.mpr ⟨s⟩
  refine ⟨notMem_erase _ _, rfl, ?_, by simp [initialBFS], ?_, ?_, ?_, ?_⟩
  · intro v hv
    have he : v = s := List.mem_singleton.mp hv
    subst v
    exact notMem_erase _ _
  · intro u hu v hv
    change 0 ≤ 0 + 1
    omega
  · intro u hu hq v hpos
    have he := hseen u hu
    subst u
    exact False.elim (hq (by simp [initialBFS]))
  · intro v hv
    have he := hseen v hv
    subst v
    exact PathAt.nil
  · intro v hv
    simp only [initialBFS, card_erase_of_mem (mem_univ s), card_univ]
    omega


/-- Preservation through the concrete row-query loop. The search contract
is discharged here by `neighborProg_residual_spec`, not a solver premise. -/
theorem bfsRun_invariant (G : WeightedGraph V) (a z : V → ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ)
    (hf : (directed (twoStar G a z)).Feasible f)
    (s : NetworkVertex V) (fuel : ℕ) (data : BFSData V)
    (hi : BFSInvariant (residualNetwork G a z f hf) s data) :
    BFSInvariant (residualNetwork G a z f hf) s ((bfsRun a z f fuel data).eval G.cut) := by
  induction fuel generalizing data with
  | zero => exact hi
  | succ fuel ih =>
      rw [bfsRun]
      cases hq : data.queue with
      | nil => exact hi
      | cons u xs =>
          simp only [Prog.eval_bind]
          have hs := neighborProg_residual_spec G a z f hf u data.unseen
          cases he : (neighborProg a z f u data.unseen).eval G.cut with
          | none =>
              rw [he] at hs
              exact ih _ (hi.drop hq hs)
          | some v =>
              rw [he] at hs
              have hv : v ∈ data.unseen := hs.1
              simp only [hv, ↓reduceIte]
              exact ih _ (hi.discover hq hv hs.2)

/-- Unreachable vertices get the public sentinel `card V + 2`. -/
def bfsLevel (data : BFSData V) (v : NetworkVertex V) : ℕ :=
  if v ∈ data.unseen then Fintype.card (NetworkVertex V) else data.level v

theorem BFSInvariant.full_level_rise {H : WeightedDiGraph (NetworkVertex V)}
    {s : NetworkVertex V} {data : BFSData V} (h : BFSInvariant H s data)
    (hq : data.queue = []) (u v : NetworkVertex V) (hpos : 0 < H.c u v) :
    bfsLevel data v ≤ bfsLevel data u + 1 := by
  by_cases hu : u ∈ data.unseen
  · simp only [bfsLevel, hu, ↓reduceIte]
    split_ifs with hv
    · omega
    · have hl := h.level_bound v hv
      omega
  · obtain ⟨hv, hstep⟩ := h.processed u hu (by simp [hq]) v hpos
    simpa only [bfsLevel, hu, hv, ↓reduceIte] using hstep

theorem bfsProg_invariant (G : WeightedGraph V) (a z : V → ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ)
    (hf : (directed (twoStar G a z)).Feasible f) (s : NetworkVertex V) :
    BFSInvariant (residualNetwork G a z f hf) s ((bfsProg a z f s).eval G.cut) :=
  bfsRun_invariant G a z f hf s _ _ (initialBFS_invariant _ s)

theorem bfsProg_level_rise (G : WeightedGraph V) (a z : V → ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ)
    (hf : (directed (twoStar G a z)).Feasible f) (s : NetworkVertex V) :
    let data := (bfsProg a z f s).eval G.cut
    bfsLevel data s = 0 ∧
      (∀ u v, 0 < (residualNetwork G a z f hf).c u v →
        bfsLevel data v ≤ bfsLevel data u + 1) ∧
      (∀ v, v ∉ data.unseen →
        PathAt (residualNetwork G a z f hf) s v (bfsLevel data v)) := by
  have hi := bfsProg_invariant G a z f hf s
  have hc := bfsProg_complete G a z f hf s
  refine ⟨?_, hi.full_level_rise hc, ?_⟩
  · simp only [bfsLevel, hi.source_seen, ↓reduceIte, hi.source_level]
  · intro v hv
    simpa only [bfsLevel, hv, ↓reduceIte] using hi.witness v hv

theorem PathAt.level_le {H : WeightedDiGraph (NetworkVertex V)}
    {s v : NetworkVertex V} {d : ℕ} (path : PathAt H s v d)
    (level : NetworkVertex V → ℕ) (hs : level s = 0)
    (hstep : ∀ u v, 0 < H.c u v → level v ≤ level u + 1) : level v ≤ d := by
  induction path with
  | nil => omega
  | @snoc u v d hp he ih =>
      have hr := hstep u v he
      omega

theorem bfsProg_shortest (G : WeightedGraph V) (a z : V → ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ)
    (hf : (directed (twoStar G a z)).Feasible f) (s : NetworkVertex V) :
    let data := (bfsProg a z f s).eval G.cut
    ∀ v, v ∉ data.unseen →
      PathAt (residualNetwork G a z f hf) s v (bfsLevel data v) ∧
      ∀ d, PathAt (residualNetwork G a z f hf) s v d → bfsLevel data v ≤ d := by
  dsimp only
  obtain ⟨hs, hrise, hpath⟩ := bfsProg_level_rise G a z f hf s
  intro v hv
  exact ⟨hpath v hv, fun _ path => path.level_le _ hs hrise⟩

theorem bfsProg_reachable (G : WeightedGraph V) (a z : V → ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ)
    (hf : (directed (twoStar G a z)).Feasible f) (s v : NetworkVertex V) :
    (∃ d, PathAt (residualNetwork G a z f hf) s v d) ↔
      v ∉ ((bfsProg a z f s).eval G.cut).unseen := by
  have hi := bfsProg_invariant G a z f hf s
  have hc := bfsProg_complete G a z f hf s
  constructor
  · rintro ⟨d, path⟩
    induction path with
    | nil => exact hi.source_seen
    | @snoc u v d hp he ih => exact (hi.processed u ih (by simp [hc]) v he).1
  · intro hv
    exact ⟨_, hi.witness v hv⟩

/-- The returned reachable shore has zero outgoing residual capacity. -/
theorem bfsProg_out_zero (G : WeightedGraph V) (a z : V → ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ)
    (hf : (directed (twoStar G a z)).Feasible f) (s : NetworkVertex V) :
    (residualNetwork G a z f hf).out ((bfsProg a z f s).eval G.cut).unseenᶜ = 0 := by
  have hi := bfsProg_invariant G a z f hf s
  have hc := bfsProg_complete G a z f hf s
  apply sum_eq_zero
  intro u hu
  apply sum_eq_zero
  intro v hv
  have hum := mem_compl.mp hu
  have hvm : v ∈ ((bfsProg a z f s).eval G.cut).unseen := by simpa using hv
  apply le_antisymm _ ((residualNetwork G a z f hf).nonneg u v)
  by_contra hp
  exact (hi.processed u hum (by simp [hc]) v (lt_of_not_ge hp)).1 hvm

def bfsBudget (V : Type) [Fintype V] : ℕ :=
  2 * Fintype.card (NetworkVertex V) * neighborBudget V

/-- A hard-capped tree, including inconsistent transcripts. Its fallback is
unreachable even on those transcripts, by the all-answer program cost bound. -/
def bfsTree (a z : V → ℕ) (f : NetworkVertex V → NetworkVertex V → ℝ)
    (s : NetworkVertex V) : DTree (Finset V) ℝ (BFSData V) (bfsBudget V) :=
  ((bfsProg a z f s).toDTree (bfsBudget V)).map (fun result => result.getD (initialBFS s))

theorem bfsTree_eval (read : Finset V → ℝ) (a z : V → ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ) (s : NetworkVertex V) :
    (bfsTree a z f s).eval read = (bfsProg a z f s).eval read := by
  have hc : (bfsProg a z f s).cost read ≤ bfsBudget V := bfsProg_cost read a z f s
  rw [bfsTree, DTree.eval_map,
    Prog.toDTree_eval read _ (bfsBudget V) hc, Option.getD_some]

theorem bfsTree_cost (read : Finset V → ℝ) (a z : V → ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ) (s : NetworkVertex V) :
    (bfsTree a z f s).cost read ≤ bfsBudget V := DTree.cost_le _ _

theorem bfsBudget_eq : bfsBudget V =
    2 * (Fintype.card V + 2) * ((Nat.clog 2 (Fintype.card V + 2) + 1) * 3) := by
  simp only [bfsBudget, network_card, neighborBudget_eq]

end
end CutQueryComplexity.DeterministicAPMCExpansion.Flow

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.bfsProg_complete
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.bfsProg_cost
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.bfsProg_level_rise
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.bfsProg_reachable
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.bfsProg_out_zero
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.bfsTree_eval
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.bfsTree_cost
