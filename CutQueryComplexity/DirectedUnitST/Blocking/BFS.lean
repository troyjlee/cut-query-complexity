import CutQueryComplexity.DirectedUnitST.Blocking.State
import CutQueryComplexity.DirectedUnitST.Repair.ResidualSearch
import Mathlib.Data.Finset.Sum

/-!
# Original-cut access to the full residual network and breadth-first search

Internal unknown pairs use the outgoing-cut residual search. Every known arc,
including arbitrary-capacity terminal arcs, is inspected for free. All choices
use public state; the hidden graphs occur only in correctness theorems.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DirectedUnitST.Blocking

open Finset DirectedCertificate Certificate Prog
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A public predicate whose witnesses can be selected without oracle access. -/
def KnownPositive (st : NetworkState V) (u : Node V) (eligible : Finset (Node V)) : Prop :=
  ∃ v ∈ eligible, st.Known u v ∧ 0 < st.knownCapacity u v

/-- Actual neighbor search in the full residual network, using only internal
original cuts. Heavy auxiliary arcs are always checked offline. -/
def networkEdgeProg (st : NetworkState V) (u : Node V) (eligible : Finset (Node V)) :
    Prog (Finset V) ℝ (Option (Node V × ℝ)) :=
  if h : KnownPositive st u eligible then
    .pure (some (Classical.choose h, st.knownCapacity u (Classical.choose h)))
  else match u with
    | .inr _ => .pure none
    | .inl v =>
        (Repair.residualEdgeProg v (st.internal.singletonValue v) eligible.toLeft
          (st.internal.knownNeighbors v) (st.internal.outward v)
          (st.internal.knownResidual v)).map (Option.map fun a => (.inl a.1, a.2))

/-- Exact positive neighbor, or exact absence throughout the eligible set. -/
def EdgeAnswer (H : WeightedDiGraph (Node V)) (u : Node V)
    (eligible : Finset (Node V)) : Option (Node V × ℝ) → Prop
  | none => ∀ v ∈ eligible, H.c u v = 0
  | some (v, c) => v ∈ eligible ∧ 0 < c ∧ H.c u v = c

theorem networkEdgeProg_spec (G : WeightedDiGraph V) (H : WeightedDiGraph (Node V))
    (st : NetworkState V) (h : st.Realizes G H) (u : Node V)
    (eligible : Finset (Node V)) :
    EdgeAnswer H u eligible ((networkEdgeProg st u eligible).eval G.out) := by
  unfold networkEdgeProg
  split_ifs with hk
  · have hc := Classical.choose_spec hk
    exact ⟨hc.1, hc.2.2, h.known u _ hc.2.1⟩
  · have hzero (v : Node V) (hv : v ∈ eligible) (hkv : st.Known u v) : H.c u v = 0 := by
      apply le_antisymm _ (H.nonneg u v)
      by_contra hp
      apply hk
      refine ⟨v, hv, hkv, ?_⟩
      rw [← h.known u v hkv]
      exact lt_of_not_ge hp
    cases u with
    | inr i =>
        exact fun v hv => hzero v hv (by trivial)
    | inl v =>
        obtain ⟨hknown, hunknown⟩ := h.internal.row v eligible.toLeft
        simp only [Prog.eval_map, h.internal.singleton v]
        by_cases hp : ∃ w ∈ eligible.toLeft, 0 < (internalGraph H).c v w
        · obtain ⟨w, hw, hpos, he⟩ := Repair.residualEdgeProg_spec G v eligible.toLeft
            (st.internal.knownNeighbors v) (st.internal.outward v)
            (st.internal.knownResidual v) ((internalGraph H).c v) hknown hunknown hp
          rw [he]
          exact ⟨mem_toLeft.mp hw, hpos, rfl⟩
        · have hz : ∀ w ∈ eligible.toLeft, (internalGraph H).c v w ≤ 0 := by
            intro w hw
            exact le_of_not_gt (fun hpos => hp ⟨w, hw, hpos⟩)
          have he := (Repair.residualEdgeProg_none_iff G v eligible.toLeft
            (st.internal.knownNeighbors v) (st.internal.outward v)
            (st.internal.knownResidual v) ((internalGraph H).c v) hknown hunknown).mpr hz
          rw [he]
          intro w hw
          cases w with
          | inl a => exact le_antisymm (hz a (mem_toLeft.mpr hw)) (H.nonneg _ _)
          | inr j => exact hzero (.inr j) hw (by trivial)

/-- Known positive arcs, including every usable heavy arc, cost zero queries. -/
theorem networkEdgeProg_cost_of_known (read : Finset V → ℝ)
    (st : NetworkState V) (u : Node V) (eligible : Finset (Node V))
    (hk : KnownPositive st u eligible) :
    (networkEdgeProg st u eligible).cost read = 0 := by
  simp [networkEdgeProg, hk]

/-- Uniform all-answer cap; the vertex count is the internal oracle's count. -/
theorem networkEdgeProg_cost (read : Finset V → ℝ) (st : NetworkState V)
    (u : Node V) (eligible : Finset (Node V)) :
    (networkEdgeProg st u eligible).cost read ≤ 2 * Nat.clog 2 (Fintype.card V) + 4 := by
  unfold networkEdgeProg
  split_ifs
  · simp
  · cases u with
    | inr i => simp
    | inl v =>
        rw [Prog.cost_map]
        have hc := Repair.residualEdgeProg_cost read v (st.internal.singletonValue v)
          eligible.toLeft (st.internal.knownNeighbors v) (st.internal.outward v)
          (st.internal.knownResidual v)
        have hl := Nat.clog_mono_right 2 (card_le_univ eligible.toLeft)
        omega

/-- Search and store the newly learned pair before returning its answer. -/
def networkSearch (st : NetworkState V) (u : Node V) (eligible : Finset (Node V)) :
    Prog (Finset V) ℝ (NetworkState V × Option (Node V × ℝ)) :=
  (networkEdgeProg st u eligible).map fun answer =>
    let learned := match answer with
      | none => st
      | some (v, c) => st.learn u v c
    (learned, answer)

theorem networkSearch_spec (G : WeightedDiGraph V) (H : WeightedDiGraph (Node V))
    (st : NetworkState V) (h : st.Realizes G H) (u : Node V)
    (eligible : Finset (Node V)) :
    let result := (networkSearch st u eligible).eval G.out
    result.1.Realizes G H ∧ EdgeAnswer H u eligible result.2 ∧
      (∀ a b, st.Known a b → result.1.Known a b) ∧
      (∀ v c, result.2 = some (v, c) → result.1.Known u v) := by
  have hs := networkEdgeProg_spec G H st h u eligible
  simp only [networkSearch, Prog.eval_map]
  cases he : (networkEdgeProg st u eligible).eval G.out with
  | none =>
      rw [he] at hs
      exact ⟨h, hs, fun _ _ hx => hx, by simp⟩
  | some answer =>
      obtain ⟨v, c⟩ := answer
      rw [he] at hs
      refine ⟨h.learn hs.2.2 hs.2.1, hs, ?_, ?_⟩
      · exact NetworkState.known_mono_learn st u v c
      · intro w a heq
        cases heq
        exact NetworkState.known_learn st u v c

theorem networkSearch_cost (read : Finset V → ℝ) (st : NetworkState V)
    (u : Node V) (eligible : Finset (Node V)) :
    (networkSearch st u eligible).cost read ≤ 2 * Nat.clog 2 (Fintype.card V) + 4 := by
  rw [networkSearch, Prog.cost_map]
  exact networkEdgeProg_cost read st u eligible

/-- Returning an already known usable arc costs no queries. This is the
operational distinction used by the first-discovery accounting in DFS. -/
theorem networkSearch_cost_of_known_answer (G : WeightedDiGraph V)
    (H : WeightedDiGraph (Node V)) (st : NetworkState V) (hr : st.Realizes G H)
    (u : Node V) (eligible : Finset (Node V)) {v : Node V} {c : ℝ}
    (he : ((networkSearch st u eligible).eval G.out).2 = some (v, c))
    (hk : st.Known u v) : (networkSearch st u eligible).cost G.out = 0 := by
  have hs := (networkSearch_spec G H st hr u eligible).2.1
  rw [he] at hs
  have hp : KnownPositive st u eligible := by
    refine ⟨v, hs.1, hk, ?_⟩
    rw [← hr.known u v hk, hs.2.2]
    exact hs.2.1
  rw [networkSearch, Prog.cost_map]
  exact networkEdgeProg_cost_of_known G.out st u eligible hp

/-- The whole BFS configuration is public and updated only from query answers. -/
structure BFSData (V : Type) where
  network : NetworkState V
  queue : List (Node V)
  unseen : Finset (Node V)
  level : Node V → ℕ

namespace BFSData

def work (data : BFSData V) : ℕ := 2 * data.unseen.card + data.queue.length

def drop (data : BFSData V) (st : NetworkState V) : BFSData V :=
  { data with network := st, queue := data.queue.tail }

def discover (data : BFSData V) (st : NetworkState V) (u v : Node V) : BFSData V :=
  { network := st
    queue := data.queue ++ [v]
    unseen := data.unseen.erase v
    level := Function.update data.level v (data.level u + 1) }

omit [Fintype V] [DecidableEq V] in
theorem work_drop (data : BFSData V) (st : NetworkState V)
    {u : Node V} {xs : List (Node V)} (hq : data.queue = u :: xs) :
    (data.drop st).work + 1 = data.work := by
  simp only [work, drop, hq, List.tail_cons, List.length_cons]
  omega

omit [Fintype V] in
theorem work_discover (data : BFSData V) (st : NetworkState V) (u v : Node V)
    (hv : v ∈ data.unseen) :
    (data.discover st u v).work + 1 = data.work := by
  have hn : 0 < data.unseen.card := card_pos.mpr ⟨v, hv⟩
  simp only [work, discover, card_erase_of_mem hv, List.length_append,
    List.length_singleton]
  omega

end BFSData

/-- A complete row search keeps its head in the queue until no unseen neighbor
remains. A discovery appends a new vertex, preserving breadth-first order.
Fuel and a membership guard make the program total for arbitrary answers. -/
def bfsRun : ℕ → BFSData V → Prog (Finset V) ℝ (BFSData V)
  | 0, data => .pure data
  | fuel + 1, data => match data.queue with
    | [] => .pure data
    | u :: _ => (networkSearch data.network u data.unseen).bind fun result =>
        match result.2 with
        | none => bfsRun fuel (data.drop result.1)
        | some (v, _) =>
            if v ∈ data.unseen then bfsRun fuel (data.discover result.1 u v)
            else .pure { data with network := result.1 }

abbrev edgeQueryBound (V : Type) [Fintype V] : ℕ :=
  2 * Nat.clog 2 (Fintype.card V) + 4

/-- The BFS program's cap is valid for every sequence of outgoing-cut answers. -/
theorem bfsRun_cost (read : Finset V → ℝ) (fuel : ℕ) (data : BFSData V) :
    (bfsRun fuel data).cost read ≤ fuel * edgeQueryBound V := by
  induction fuel generalizing data with
  | zero => simp [bfsRun]
  | succ fuel ih =>
      rw [bfsRun]
      cases hq : data.queue with
      | nil => simp
      | cons u xs =>
          simp only [Prog.cost_bind]
          have hc := networkSearch_cost read data.network u data.unseen
          cases hr : (networkSearch data.network u data.unseen).eval read with
          | mk st answer =>
              cases answer with
              | none =>
                  have hi := ih (data.drop st)
                  simp only [edgeQueryBound, Nat.succ_mul] at hi ⊢
                  omega
              | some answer =>
                  obtain ⟨v, c⟩ := answer
                  dsimp only
                  split_ifs
                  · have hi := ih (data.discover st u v)
                    simp only [edgeQueryBound, Nat.succ_mul] at hi ⊢
                    omega
                  · simp only [Prog.cost_pure, Nat.add_zero]
                    simp only [edgeQueryBound, Nat.succ_mul]
                    omega

/-- On an actual residual graph, enough public work fuel always empties the
queue, and the learned state still represents that entire residual graph. -/
theorem bfsRun_complete (G : WeightedDiGraph V) (H : WeightedDiGraph (Node V))
    (fuel : ℕ) (data : BFSData V) (h : data.network.Realizes G H)
    (hwork : data.work ≤ fuel) :
    let result := (bfsRun fuel data).eval G.out
    result.network.Realizes G H ∧ result.queue = [] := by
  induction fuel generalizing data with
  | zero =>
      have hq : data.queue = [] := by
        apply List.eq_nil_of_length_eq_zero
        unfold BFSData.work at hwork
        omega
      exact ⟨h, hq⟩
  | succ fuel ih =>
      rw [bfsRun]
      cases hq : data.queue with
      | nil => exact ⟨h, hq⟩
      | cons u xs =>
          simp only [Prog.eval_bind]
          have hs := networkSearch_spec G H data.network h u data.unseen
          cases hr : (networkSearch data.network u data.unseen).eval G.out with
          | mk st answer =>
              rw [hr] at hs
              cases answer with
              | none =>
                  apply ih (data.drop st) hs.1
                  have hw := data.work_drop st hq
                  omega
              | some answer =>
                  obtain ⟨v, c⟩ := answer
                  have hv : v ∈ data.unseen := hs.2.1.1
                  simp only [hv, ↓reduceIte]
                  apply ih (data.discover st u v) hs.1
                  have hw := data.work_discover st u v hv
                  omega

def initialBFS (st : NetworkState V) (s : Node V) : BFSData V where
  network := st
  queue := [s]
  unseen := univ.erase s
  level := fun _ => 0

theorem initialBFS_work (st : NetworkState V) (s : Node V) :
    (initialBFS st s).work ≤ 2 * Fintype.card (Node V) := by
  simp only [BFSData.work, initialBFS, card_erase_of_mem (mem_univ s),
    card_univ, List.length_singleton]
  have hn : 0 < Fintype.card (Node V) := Fintype.card_pos_iff.mpr ⟨s⟩
  omega

/-- An actual complete BFS, with at most two row events per network vertex. -/
def bfsProg (st : NetworkState V) (s : Node V) : Prog (Finset V) ℝ (BFSData V) :=
  bfsRun (2 * Fintype.card (Node V)) (initialBFS st s)

theorem bfsProg_complete (G : WeightedDiGraph V) (H : WeightedDiGraph (Node V))
    (st : NetworkState V) (h : st.Realizes G H) (s : Node V) :
    let result := (bfsProg st s).eval G.out
    result.network.Realizes G H ∧ result.queue = [] :=
  bfsRun_complete G H _ _ h (initialBFS_work st s)

theorem bfsProg_cost (read : Finset V → ℝ) (st : NetworkState V) (s : Node V) :
    (bfsProg st s).cost read ≤
      2 * Fintype.card (Node V) * (2 * Nat.clog 2 (Fintype.card V) + 4) :=
  bfsRun_cost read _ _

/-- A proof-only directed positive-capacity walk, with its exact length. -/
inductive PathAt (H : WeightedDiGraph (Node V)) (s : Node V) : Node V → ℕ → Prop
  | nil : PathAt H s s 0
  | snoc {u v : Node V} {d : ℕ} : PathAt H s u d → 0 < H.c u v → PathAt H s v (d + 1)

/-- BFS's invariant includes all completed rows, the ordered queue, and actual
path witnesses. No level or search property is supplied by an external oracle. -/
structure BFSInvariant (H : WeightedDiGraph (Node V)) (s : Node V) (data : BFSData V) : Prop where
  source_seen : s ∉ data.unseen
  source_level : data.level s = 0
  queue_seen : ∀ v ∈ data.queue, v ∉ data.unseen
  queue_sorted : data.queue.Pairwise fun u v => data.level u ≤ data.level v
  seen_bound : ∀ u ∈ data.queue, ∀ v, v ∉ data.unseen → data.level v ≤ data.level u + 1
  processed : ∀ u, u ∉ data.unseen → u ∉ data.queue →
    ∀ v, 0 < H.c u v → v ∉ data.unseen ∧ data.level v ≤ data.level u + 1
  witness : ∀ v, v ∉ data.unseen → PathAt H s v (data.level v)
  level_bound : ∀ v, v ∉ data.unseen →
    data.level v < Fintype.card (Node V) - data.unseen.card

theorem BFSInvariant.drop {H : WeightedDiGraph (Node V)} {s : Node V} {data : BFSData V}
    (h : BFSInvariant H s data) (st : NetworkState V)
    {u : Node V} {xs : List (Node V)} (hq : data.queue = u :: xs)
    (hzero : ∀ v ∈ data.unseen, H.c u v = 0) : BFSInvariant H s (data.drop st) := by
  have htail (v : Node V) (hv : v ∈ data.queue.tail) : v ∈ data.queue :=
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

theorem BFSInvariant.discover {H : WeightedDiGraph (Node V)} {s : Node V}
    {data : BFSData V} (h : BFSInvariant H s data) (st : NetworkState V)
    {u v : Node V} {xs : List (Node V)} (hq : data.queue = u :: xs)
    (hv : v ∈ data.unseen) (hpos : 0 < H.c u v) :
    BFSInvariant H s (data.discover st u v) := by
  let next := data.discover st u v
  have hum : u ∈ data.queue := by rw [hq]; simp
  have hu : u ∉ data.unseen := h.queue_seen u hum
  have hsame (x : Node V) (hx : x ∉ data.unseen) : next.level x = data.level x := by
    have hxv : x ≠ v := fun he => hx (he.symm ▸ hv)
    simp [next, BFSData.discover, Function.update_of_ne hxv]
  have hnew : next.level v = data.level u + 1 := by simp [next, BFSData.discover]
  have hseen (x : Node V) (hx : x ∉ next.unseen) : x = v ∨ x ∉ data.unseen := by
    by_cases he : x = v
    · exact Or.inl he
    · exact Or.inr (fun hm => hx (mem_erase.mpr ⟨he, hm⟩))
  have hold (x : Node V) (hx : x ∉ data.unseen) : x ∉ next.unseen :=
    fun hm => hx (mem_of_mem_erase hm)
  have hcount : Fintype.card (Node V) - next.unseen.card =
      Fintype.card (Node V) - data.unseen.card + 1 := by
    have hc := card_le_univ data.unseen
    have hp : 0 < data.unseen.card := card_pos.mpr ⟨v, hv⟩
    dsimp [next, BFSData.discover]
    rw [card_erase_of_mem hv]
    omega
  have hhead (x : Node V) (hx : x ∈ data.queue) : data.level u ≤ data.level x := by
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

theorem initialBFS_invariant (H : WeightedDiGraph (Node V)) (st : NetworkState V)
    (s : Node V) : BFSInvariant H s (initialBFS st s) := by
  have hseen (v : Node V) (hv : v ∉ (univ : Finset (Node V)).erase s) : v = s := by
    by_contra hne
    exact hv (mem_erase.mpr ⟨hne, mem_univ v⟩)
  have hn : 0 < Fintype.card (Node V) := Fintype.card_pos_iff.mpr ⟨s⟩
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

/-- Preservation of the shortest-level invariant through the actual query loop. -/
theorem bfsRun_invariant (G : WeightedDiGraph V) (H : WeightedDiGraph (Node V))
    (s : Node V) (fuel : ℕ) (data : BFSData V) (hr : data.network.Realizes G H)
    (hi : BFSInvariant H s data) :
    BFSInvariant H s ((bfsRun fuel data).eval G.out) := by
  induction fuel generalizing data with
  | zero => exact hi
  | succ fuel ih =>
      rw [bfsRun]
      cases hq : data.queue with
      | nil => exact hi
      | cons u xs =>
          simp only [Prog.eval_bind]
          have hs := networkSearch_spec G H data.network hr u data.unseen
          cases he : (networkSearch data.network u data.unseen).eval G.out with
          | mk st answer =>
              rw [he] at hs
              cases answer with
              | none => exact ih _ hs.1 (hi.drop st hq hs.2.1)
              | some answer =>
                  obtain ⟨v, c⟩ := answer
                  have hv : v ∈ data.unseen := hs.2.1.1
                  have hpos : 0 < H.c u v := by rw [hs.2.1.2.2]; exact hs.2.1.2.1
                  simp only [hv, ↓reduceIte]
                  exact ih _ hs.1 (hi.discover st hq hv hpos)

/-- Unreached vertices receive the public sentinel level N. This extends the
all-arc rise guarantee to the whole graph, including its unreachable part. -/
def bfsLevel (data : BFSData V) (v : Node V) : ℕ :=
  if v ∈ data.unseen then Fintype.card (Node V) else data.level v

theorem BFSInvariant.full_level_rise {H : WeightedDiGraph (Node V)} {s : Node V}
    {data : BFSData V} (h : BFSInvariant H s data) (hq : data.queue = [])
    (u v : Node V) (hpos : 0 < H.c u v) : bfsLevel data v ≤ bfsLevel data u + 1 := by
  by_cases hu : u ∈ data.unseen
  · simp only [bfsLevel, hu, ↓reduceIte]
    split_ifs with hv
    · omega
    · have hl := h.level_bound v hv
      omega
  · obtain ⟨hv, hstep⟩ := h.processed u hu (by simp [hq]) v hpos
    simpa only [bfsLevel, hu, hv, ↓reduceIte] using hstep

/-- The computed levels, not externally supplied levels, satisfy the premise
of Repair's heavy-terminal middle-layer and Dinic distance lemmas. -/
theorem bfsProg_level_rise (G : WeightedDiGraph V) (H : WeightedDiGraph (Node V))
    (st : NetworkState V) (h : st.Realizes G H) (s : Node V) :
    let result := (bfsProg st s).eval G.out
    bfsLevel result s = 0 ∧
      (∀ u v, 0 < H.c u v → bfsLevel result v ≤ bfsLevel result u + 1) ∧
      (∀ v, v ∉ result.unseen → PathAt H s v (bfsLevel result v)) := by
  have hi := bfsRun_invariant G H s (2 * Fintype.card (Node V))
    (initialBFS st s) h (initialBFS_invariant H st s)
  have hc := bfsProg_complete G H st h s
  change BFSInvariant H s ((bfsProg st s).eval G.out) at hi
  refine ⟨?_, hi.full_level_rise hc.2, ?_⟩
  · simp only [bfsLevel, hi.source_seen, ↓reduceIte, hi.source_level]
  · intro v hv
    simpa only [bfsLevel, hv, ↓reduceIte] using hi.witness v hv

omit [Fintype V] [DecidableEq V] in
theorem PathAt.level_le {H : WeightedDiGraph (Node V)} {s v : Node V} {d : ℕ}
    (path : PathAt H s v d) (level : Node V → ℕ) (hs : level s = 0)
    (hstep : ∀ u v, 0 < H.c u v → level v ≤ level u + 1) : level v ≤ d := by
  induction path with
  | nil => omega
  | @snoc u v d hp he ih =>
      have hr := hstep u v he
      omega

/-- Every reached vertex has its exact shortest positive-residual distance. -/
theorem bfsProg_shortest (G : WeightedDiGraph V) (H : WeightedDiGraph (Node V))
    (st : NetworkState V) (h : st.Realizes G H) (s : Node V) :
    let result := (bfsProg st s).eval G.out
    ∀ v, v ∉ result.unseen →
      PathAt H s v (bfsLevel result v) ∧
        ∀ d, PathAt H s v d → bfsLevel result v ≤ d := by
  dsimp only
  obtain ⟨hs, hrise, hpath⟩ := bfsProg_level_rise G H st h s
  intro v hv
  exact ⟨hpath v hv, fun _ path => path.level_le _ hs hrise⟩

/-- A completed BFS discovers precisely the vertices reachable in the full
residual graph, including paths through the explicit heavy terminal arcs. -/
theorem bfsProg_reachable (G : WeightedDiGraph V) (H : WeightedDiGraph (Node V))
    (st : NetworkState V) (h : st.Realizes G H) (s v : Node V) :
    let result := (bfsProg st s).eval G.out
    (∃ d, PathAt H s v d) ↔ v ∉ result.unseen := by
  have hi := bfsRun_invariant G H s (2 * Fintype.card (Node V))
    (initialBFS st s) h (initialBFS_invariant H st s)
  have hc := bfsProg_complete G H st h s
  change BFSInvariant H s ((bfsProg st s).eval G.out) at hi
  constructor
  · rintro ⟨d, path⟩
    induction path with
    | nil => exact hi.source_seen
    | @snoc a b d hp he ih =>
        exact (hi.processed a ih (by simp [hc.2]) b he).1
  · intro hv
    exact ⟨_, hi.witness v hv⟩

/-- The discovered shore has no outgoing residual capacity. This is the
operational certificate used when the terminal solve's last BFS misses t. -/
theorem bfsProg_out_zero (G : WeightedDiGraph V) (H : WeightedDiGraph (Node V))
    (st : NetworkState V) (h : st.Realizes G H) (s : Node V) :
    H.out ((bfsProg st s).eval G.out).unseenᶜ = 0 := by
  have hi := bfsRun_invariant G H s (2 * Fintype.card (Node V))
    (initialBFS st s) h (initialBFS_invariant H st s)
  have hc := bfsProg_complete G H st h s
  change BFSInvariant H s ((bfsProg st s).eval G.out) at hi
  apply sum_eq_zero
  intro u hu
  apply sum_eq_zero
  intro v hv
  have hum := mem_compl.mp hu
  have hvm : v ∈ ((bfsProg st s).eval G.out).unseen := by simpa using hv
  apply le_antisymm _ (H.nonneg u v)
  by_contra hp
  exact (hi.processed u hum (by simp [hc.2]) v (lt_of_not_ge hp)).1 hvm

end
end CutQueryComplexity.DirectedUnitST.Blocking

#print axioms CutQueryComplexity.DirectedUnitST.Blocking.networkEdgeProg_spec
#print axioms CutQueryComplexity.DirectedUnitST.Blocking.networkEdgeProg_cost
#print axioms CutQueryComplexity.DirectedUnitST.Blocking.networkSearch_spec
#print axioms CutQueryComplexity.DirectedUnitST.Blocking.bfsProg_complete
#print axioms CutQueryComplexity.DirectedUnitST.Blocking.bfsProg_cost
#print axioms CutQueryComplexity.DirectedUnitST.Blocking.bfsProg_level_rise
#print axioms CutQueryComplexity.DirectedUnitST.Blocking.bfsProg_shortest
#print axioms CutQueryComplexity.DirectedUnitST.Blocking.bfsProg_reachable
#print axioms CutQueryComplexity.DirectedUnitST.Blocking.bfsProg_out_zero
