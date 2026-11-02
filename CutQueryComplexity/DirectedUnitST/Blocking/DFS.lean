import CutQueryComplexity.DirectedUnitST.Blocking.BFS
import CutQueryComplexity.DirectedUnitST.Repair.Dinic

/-!
# Complete-path depth-first search in frozen levels

The stack holds a complete source prefix; it is extended using learned/query
answers, and it is returned only after its head reaches the target. No flow
is pushed during this search. A failed row permanently kills its vertex.
The fresh bit records whether a frame's entering pair was first learned by
that traversal; it is later charged to a dead destination or to the returned
whole path's next augmentation.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DirectedUnitST.Blocking

open Finset DirectedCertificate Certificate Prog
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

structure Frame (V : Type) where
  vertex : Node V
  fresh : Bool
  deriving DecidableEq

def freshCount (stack : List (Frame V)) : ℕ := (stack.filter fun f => f.fresh).length

omit [Fintype V] [DecidableEq V] in
theorem freshCount_cons (head : Frame V) (tail : List (Frame V)) :
    freshCount (head :: tail) = (if head.fresh then 1 else 0) + freshCount tail := by
  cases hf : head.fresh <;> simp [freshCount, hf, Nat.add_comm]

/-- A proof-only certificate for the actual public stack, in reverse path order. -/
inductive StackPath (H : WeightedDiGraph (Node V)) (level : Node V → ℕ) (s : Node V) :
    List (Frame V) → Prop
  | root : StackPath H level s [⟨s, false⟩]
  | push {head : Frame V} {tail : List (Frame V)}
      (path : StackPath H level s (head :: tail)) (v : Node V) (fresh : Bool)
      (positive : 0 < H.c head.vertex v) (forward : level v = level head.vertex + 1) :
      StackPath H level s (⟨v, fresh⟩ :: head :: tail)

omit [Fintype V] [DecidableEq V] in
theorem StackPath.nonempty {H : WeightedDiGraph (Node V)} {level : Node V → ℕ}
    {s : Node V} {stack : List (Frame V)} (h : StackPath H level s stack) : stack ≠ [] := by
  cases h <;> simp

omit [Fintype V] [DecidableEq V] in
theorem StackPath.level_le_head {H : WeightedDiGraph (Node V)} {level : Node V → ℕ}
    {s : Node V} {stack : List (Frame V)} (h : StackPath H level s stack) :
    ∀ head tail, stack = head :: tail → ∀ f ∈ stack, level f.vertex ≤ level head.vertex := by
  induction h with
  | root =>
      intro head tail he f hf
      cases he
      have heq : f = ⟨s, false⟩ := List.mem_singleton.mp hf
      subst f
      exact le_rfl
  | @push head tail path v fresh positive forward ih =>
      intro top rest he f hf
      cases he
      rcases List.mem_cons.mp hf with hf | hf
      · subst f; exact le_rfl
      · have hi := ih head tail rfl f hf
        dsimp
        omega

omit [Fintype V] [DecidableEq V] in
theorem StackPath.vertices_nodup {H : WeightedDiGraph (Node V)} {level : Node V → ℕ}
    {s : Node V} {stack : List (Frame V)} (h : StackPath H level s stack) :
    (stack.map Frame.vertex).Nodup := by
  induction h with
  | root => simp
  | @push head tail path v fresh positive forward ih =>
      rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, ih⟩
      intro hm
      obtain ⟨f, hf, he⟩ := List.mem_map.mp hm
      have hl := path.level_le_head head tail rfl f hf
      rw [he] at hl
      change level v ≤ level head.vertex at hl
      rw [forward] at hl
      omega

omit [Fintype V] [DecidableEq V] in
theorem StackPath.tail {H : WeightedDiGraph (Node V)} {level : Node V → ℕ}
    {s : Node V} {head : Frame V} {tail : List (Frame V)}
    (h : StackPath H level s (head :: tail)) : tail = [] ∨ StackPath H level s tail := by
  cases h with
  | root => exact Or.inl rfl
  | push path _ _ _ _ => exact Or.inr path

/-- All dead vertices are unable to reach t using a remaining frozen-forward
path. The closure condition is preserved as further vertices become dead. -/
def DeadClosed (H : WeightedDiGraph (Node V)) (level : Node V → ℕ)
    (t : Node V) (dead : Finset (Node V)) : Prop :=
  t ∉ dead ∧ ∀ u ∈ dead, ∀ v, level v = level u + 1 → 0 < H.c u v → v ∈ dead

def eligibleNext (level : Node V → ℕ) (dead : Finset (Node V)) (u : Node V) :
    Finset (Node V) := univ.filter fun v => level v = level u + 1 ∧ v ∉ dead

@[simp] theorem mem_eligibleNext (level : Node V → ℕ) (dead : Finset (Node V))
    (u v : Node V) :
    v ∈ eligibleNext level dead u ↔ level v = level u + 1 ∧ v ∉ dead := by
  simp [eligibleNext]

theorem deadClosed_insert {H : WeightedDiGraph (Node V)} {level : Node V → ℕ}
    {t u : Node V} {dead : Finset (Node V)} (h : DeadClosed H level t dead)
    (hut : u ≠ t) (hz : ∀ v ∈ eligibleNext level dead u, H.c u v = 0) :
    DeadClosed H level t (insert u dead) := by
  refine ⟨by simp [h.1, Ne.symm hut], ?_⟩
  intro a ha v hlevel hpos
  rcases mem_insert.mp ha with ha | ha
  · subst a
    by_cases hv : v ∈ dead
    · exact mem_insert_of_mem hv
    · have he := hz v ((mem_eligibleNext level dead u v).mpr ⟨hlevel, hv⟩)
      rw [he] at hpos
      exact False.elim ((lt_irrefl 0) hpos)
  · exact mem_insert_of_mem (h.2 a ha v hlevel hpos)

/-- Public DFS state. Accounting counters are updated from public event flags. -/
structure DFSData (V : Type) where
  network : NetworkState V
  dead : Finset (Node V)
  stack : List (Frame V)
  failedFresh : ℕ
  failedRows : ℕ

namespace DFSData

def work (data : DFSData V) : ℕ :=
  2 * (Fintype.card (Node V) - data.dead.card) - data.stack.length

def charge (data : DFSData V) : ℕ :=
  data.failedRows + data.failedFresh + freshCount data.stack

def push (data : DFSData V) (st : NetworkState V) (u v : Node V) : DFSData V :=
  { data with
    network := st
    stack := ⟨v, decide (¬data.network.Known u v)⟩ :: data.stack }

def pop (data : DFSData V) (st : NetworkState V) (head : Frame V) : DFSData V :=
  { network := st
    dead := insert head.vertex data.dead
    stack := data.stack.tail
    failedFresh := data.failedFresh + if head.fresh then 1 else 0
    failedRows := data.failedRows + 1 }

end DFSData

/-- Search returns either an empty exhausted stack or a complete s-to-t path.
It never applies a prefix flow. A public guard and fuel ensure totality even
for inconsistent answer sequences. -/
def dfsRun (level : Node V → ℕ) (t : Node V) :
    ℕ → DFSData V → Prog (Finset V) ℝ (DFSData V)
  | 0, data => .pure data
  | fuel + 1, data => match data.stack with
    | [] => .pure data
    | head :: _ =>
        if head.vertex = t then .pure data else
          (networkSearch data.network head.vertex
            (eligibleNext level data.dead head.vertex)).bind fun result =>
            match result.2 with
            | none => dfsRun level t fuel (data.pop result.1 head)
            | some (v, _) =>
                if v ∈ eligibleNext level data.dead head.vertex then
                  dfsRun level t fuel (data.push result.1 head.vertex v)
                else .pure { data with network := result.1 }

/-- Per-search fuel gives a public all-answer cap. The sharper phase bound
will count first discoveries and failed rows, not repeated known traversals. -/
theorem dfsRun_cost (read : Finset V → ℝ) (level : Node V → ℕ) (t : Node V)
    (fuel : ℕ) (data : DFSData V) :
    (dfsRun level t fuel data).cost read ≤ fuel * edgeQueryBound V := by
  induction fuel generalizing data with
  | zero => simp [dfsRun]
  | succ fuel ih =>
      rw [dfsRun]
      cases hstack : data.stack with
      | nil => simp
      | cons head tail =>
          dsimp only
          split_ifs
          · simp
          · simp only [Prog.cost_bind]
            have hc := networkSearch_cost read data.network head.vertex
              (eligibleNext level data.dead head.vertex)
            cases hr : (networkSearch data.network head.vertex
                (eligibleNext level data.dead head.vertex)).eval read with
            | mk st answer =>
                cases answer with
                | none =>
                    have hi := ih (data.pop st head)
                    simp only [edgeQueryBound, Nat.succ_mul] at hi ⊢
                    omega
                | some answer =>
                    obtain ⟨v, c⟩ := answer
                    dsimp only
                    split_ifs
                    · have hi := ih (data.push st head.vertex v)
                      simp only [edgeQueryBound, Nat.succ_mul] at hi ⊢
                      omega
                    · simp only [Prog.cost_pure, Nat.add_zero, edgeQueryBound, Nat.succ_mul]
                      omega

def StackKnown (st : NetworkState V) : List (Frame V) → Prop
  | [] => True
  | [_] => True
  | child :: parent :: tail => st.Known parent.vertex child.vertex ∧ StackKnown st (parent :: tail)

omit [Fintype V] [DecidableEq V] in
theorem stackKnown_mono {st st' : NetworkState V}
    (hm : ∀ u v, st.Known u v → st'.Known u v) (stack : List (Frame V))
    (hs : StackKnown st stack) : StackKnown st' stack := by
  induction stack with
  | nil => trivial
  | cons head tail ih =>
      cases tail with
      | nil => trivial
      | cons parent rest => exact ⟨hm _ _ hs.1, ih hs.2⟩

omit [Fintype V] [DecidableEq V] in
theorem stackKnown_tail (st : NetworkState V) (head : Frame V) (tail : List (Frame V))
    (h : StackKnown st (head :: tail)) : StackKnown st tail := by
  cases tail with
  | nil => trivial
  | cons parent rest => exact h.2

structure DFSInvariant (H : WeightedDiGraph (Node V)) (level : Node V → ℕ)
    (s t : Node V) (data : DFSData V) : Prop where
  path : data.stack = [] ∨ StackPath H level s data.stack
  live : ∀ f ∈ data.stack, f.vertex ∉ data.dead
  closed : DeadClosed H level t data.dead
  exhausted : data.stack = [] → s ∈ data.dead
  learned : StackKnown data.network data.stack
  failed_le_rows : data.failedFresh ≤ data.failedRows

theorem DFSInvariant.live_bound {H : WeightedDiGraph (Node V)} {level : Node V → ℕ}
    {s t : Node V} {data : DFSData V} (h : DFSInvariant H level s t data) :
    data.stack.length ≤ Fintype.card (Node V) - data.dead.card := by
  rcases h.path with he | hp
  · simp [he]
  · have hsub : (data.stack.map Frame.vertex).toFinset ⊆ data.deadᶜ := by
      intro v hv
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
      exact mem_compl.mpr (h.live f hf)
    have hc := card_le_card hsub
    rw [List.toFinset_card_of_nodup hp.vertices_nodup, List.length_map,
      card_compl] at hc
    exact hc

theorem DFSInvariant.push {H : WeightedDiGraph (Node V)} {level : Node V → ℕ}
    {s t : Node V} {data : DFSData V} (h : DFSInvariant H level s t data)
    (st : NetworkState V) {head : Frame V} {tail : List (Frame V)} {v : Node V}
    (hstack : data.stack = head :: tail) (hv : v ∈ eligibleNext level data.dead head.vertex)
    (hpos : 0 < H.c head.vertex v)
    (hknown : st.Known head.vertex v)
    (hmono : ∀ u v, data.network.Known u v → st.Known u v) :
    DFSInvariant H level s t (data.push st head.vertex v) := by
  have hp : StackPath H level s (head :: tail) := by
    rcases h.path with he | hp
    · rw [hstack] at he; contradiction
    · simpa only [hstack] using hp
  obtain ⟨hlevel, hvdead⟩ := (mem_eligibleNext _ _ _ _).mp hv
  refine ⟨Or.inr ?_, ?_, h.closed, ?_, ?_, h.failed_le_rows⟩
  · simpa only [DFSData.push, hstack] using
      StackPath.push hp v (decide (¬data.network.Known head.vertex v)) hpos hlevel
  · intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact hvdead
    · exact h.live f hf
  · intro he
    simp [DFSData.push] at he
  · change StackKnown st (⟨v, decide (¬data.network.Known head.vertex v)⟩ :: data.stack)
    rw [hstack]
    change st.Known head.vertex v ∧ StackKnown st (head :: tail)
    refine ⟨hknown, stackKnown_mono hmono _ ?_⟩
    simpa only [hstack] using h.learned

theorem DFSInvariant.pop {H : WeightedDiGraph (Node V)} {level : Node V → ℕ}
    {s t : Node V} {data : DFSData V} (h : DFSInvariant H level s t data)
    (st : NetworkState V) {head : Frame V} {tail : List (Frame V)}
    (hstack : data.stack = head :: tail) (ht : head.vertex ≠ t)
    (hz : ∀ v ∈ eligibleNext level data.dead head.vertex, H.c head.vertex v = 0)
    (hmono : ∀ u v, data.network.Known u v → st.Known u v) :
    DFSInvariant H level s t (data.pop st head) := by
  have hp : StackPath H level s (head :: tail) := by
    rcases h.path with he | hp
    · rw [hstack] at he; contradiction
    · simpa only [hstack] using hp
  have hnd := hp.vertices_nodup
  simp only [List.map_cons, List.nodup_cons] at hnd
  refine ⟨?_, ?_, deadClosed_insert h.closed ht hz, ?_, ?_, ?_⟩
  · simpa only [DFSData.pop, hstack, List.tail_cons] using hp.tail
  · intro f hf
    change f ∈ data.stack.tail at hf
    rw [hstack, List.tail_cons] at hf
    change f.vertex ∉ insert head.vertex data.dead
    rw [mem_insert, not_or]
    refine ⟨?_, h.live f (by rw [hstack]; exact List.mem_cons_of_mem _ hf)⟩
    intro he
    apply hnd.1
    exact List.mem_map.mpr ⟨f, hf, he⟩
  · intro he
    change data.stack.tail = [] at he
    rw [hstack, List.tail_cons] at he
    subst tail
    cases hp with
    | root => exact mem_insert_self _ _
  · have hk := stackKnown_tail data.network head tail (by simpa only [hstack] using h.learned)
    simpa only [DFSData.pop, hstack, List.tail_cons] using stackKnown_mono hmono _ hk
  · change data.failedFresh + (if head.fresh then 1 else 0) ≤ data.failedRows + 1
    have hc := h.failed_le_rows
    split <;> omega

theorem DFSInvariant.work_push {H : WeightedDiGraph (Node V)} {level : Node V → ℕ}
    {s t : Node V} {data : DFSData V} (_h : DFSInvariant H level s t data)
    (st : NetworkState V) (u v : Node V)
    (hnext : DFSInvariant H level s t (data.push st u v)) :
    (data.push st u v).work + 1 = data.work := by
  have hn := hnext.live_bound
  simp only [DFSData.push, List.length_cons] at hn
  simp only [DFSData.work, DFSData.push, List.length_cons]
  omega

theorem DFSInvariant.work_pop {H : WeightedDiGraph (Node V)} {level : Node V → ℕ}
    {s t : Node V} {data : DFSData V} (h : DFSInvariant H level s t data)
    (st : NetworkState V) {head : Frame V} {tail : List (Frame V)}
    (hstack : data.stack = head :: tail) :
    (data.pop st head).work + 1 = data.work := by
  have hl := h.live_bound
  have hhd : head.vertex ∉ data.dead := h.live head (by rw [hstack]; simp)
  have hc := card_le_univ data.dead
  simp only [DFSData.work, DFSData.pop, card_insert_of_notMem hhd,
    hstack, List.tail_cons, List.length_cons] at hl ⊢
  omega

/-- The final stack is exhausted or is a complete path reaching the target. -/
def DFSFinished (t : Node V) (data : DFSData V) : Prop :=
  data.stack = [] ∨ ∃ head tail, data.stack = head :: tail ∧ head.vertex = t

/-- Query-driven DFS terminates with a real complete path or with its source
proved dead; the residual graph is unchanged until the caller augments. -/
theorem dfsRun_complete (G : WeightedDiGraph V) (H : WeightedDiGraph (Node V))
    (level : Node V → ℕ) (s t : Node V) (fuel : ℕ) (data : DFSData V)
    (hr : data.network.Realizes G H) (hi : DFSInvariant H level s t data)
    (hwork : data.work ≤ fuel) :
    let result := (dfsRun level t fuel data).eval G.out
    result.network.Realizes G H ∧ DFSInvariant H level s t result ∧ DFSFinished t result := by
  induction fuel generalizing data with
  | zero =>
      have hl := hi.live_bound
      have he : data.stack = [] := by
        apply List.eq_nil_of_length_eq_zero
        unfold DFSData.work at hwork
        omega
      exact ⟨hr, hi, Or.inl he⟩
  | succ fuel ih =>
      rw [dfsRun]
      cases hstack : data.stack with
      | nil => exact ⟨hr, hi, Or.inl hstack⟩
      | cons head tail =>
          dsimp only
          split_ifs with ht
          · exact ⟨hr, hi, Or.inr ⟨head, tail, hstack, ht⟩⟩
          · simp only [Prog.eval_bind]
            have hs := networkSearch_spec G H data.network hr head.vertex
              (eligibleNext level data.dead head.vertex)
            cases he : (networkSearch data.network head.vertex
                (eligibleNext level data.dead head.vertex)).eval G.out with
            | mk st answer =>
                rw [he] at hs
                cases answer with
                | none =>
                    have hnext := hi.pop st hstack ht hs.2.1 hs.2.2.1
                    apply ih _ hs.1 hnext
                    have hw := hi.work_pop st hstack
                    omega
                | some answer =>
                    obtain ⟨v, c⟩ := answer
                    have hv : v ∈ eligibleNext level data.dead head.vertex := hs.2.1.1
                    have hp : 0 < H.c head.vertex v := by rw [hs.2.1.2.2]; exact hs.2.1.2.1
                    have hknown := hs.2.2.2 v c rfl
                    have hnext := hi.push st hstack hv hp hknown hs.2.2.1
                    dsimp only
                    simp only [hv, ↓reduceIte]
                    apply ih _ hs.1 hnext
                    have hw := hi.work_push st head.vertex v hnext
                    omega

def initialDFS (st : NetworkState V) (dead : Finset (Node V)) (s : Node V) : DFSData V where
  network := st
  dead := dead
  stack := if s ∈ dead then [] else [⟨s, false⟩]
  failedFresh := 0
  failedRows := 0

omit [Fintype V] in
theorem initialDFS_invariant (H : WeightedDiGraph (Node V)) (level : Node V → ℕ)
    (st : NetworkState V) (dead : Finset (Node V)) (s t : Node V)
    (hd : DeadClosed H level t dead) : DFSInvariant H level s t (initialDFS st dead s) := by
  by_cases hs : s ∈ dead
  · refine ⟨Or.inl (by simp [initialDFS, hs]), ?_, hd, fun _ => hs, ?_, le_rfl⟩
    · intro f hf
      simp [initialDFS, hs] at hf
    · simp [initialDFS, hs, StackKnown]
  · refine ⟨Or.inr ?_, ?_, hd, ?_, ?_, le_rfl⟩
    · simpa only [initialDFS, hs, ↓reduceIte] using (StackPath.root (H := H) (level := level) (s := s))
    · intro f hf
      simp only [initialDFS, hs, ↓reduceIte, List.mem_singleton] at hf
      subst f
      exact hs
    · intro he
      simp [initialDFS, hs] at he
    · simp [initialDFS, hs, StackKnown]

theorem initialDFS_work (st : NetworkState V) (dead : Finset (Node V)) (s : Node V) :
    (initialDFS st dead s).work ≤ 2 * Fintype.card (Node V) := by
  unfold DFSData.work initialDFS
  omega

def dfsProg (st : NetworkState V) (level : Node V → ℕ) (dead : Finset (Node V))
    (s t : Node V) : Prog (Finset V) ℝ (DFSData V) :=
  dfsRun level t (2 * Fintype.card (Node V)) (initialDFS st dead s)

theorem dfsProg_complete (G : WeightedDiGraph V) (H : WeightedDiGraph (Node V))
    (st : NetworkState V) (hr : st.Realizes G H) (level : Node V → ℕ)
    (dead : Finset (Node V)) (s t : Node V) (hd : DeadClosed H level t dead) :
    let result := (dfsProg st level dead s t).eval G.out
    result.network.Realizes G H ∧ DFSInvariant H level s t result ∧ DFSFinished t result :=
  dfsRun_complete G H level s t _ _ hr (initialDFS_invariant H level st dead s t hd)
    (initialDFS_work st dead s)

theorem dfsProg_cost (read : Finset V → ℝ) (st : NetworkState V) (level : Node V → ℕ)
    (dead : Finset (Node V)) (s t : Node V) :
    (dfsProg st level dead s t).cost read ≤
      2 * Fintype.card (Node V) * edgeQueryBound V := dfsRun_cost read _ _ _ _

/-- A frozen-forward path in the actual residual graph. -/
inductive LevelPath (H : WeightedDiGraph (Node V)) (level : Node V → ℕ) (s : Node V) :
    Node V → ℕ → Prop
  | nil : LevelPath H level s s 0
  | snoc {u v : Node V} {d : ℕ} : LevelPath H level s u d →
      0 < H.c u v → level v = level u + 1 → LevelPath H level s v (d + 1)

omit [Fintype V] [DecidableEq V] in
theorem LevelPath.dead {H : WeightedDiGraph (Node V)} {level : Node V → ℕ}
    {s v t : Node V} {d : ℕ} {dead : Finset (Node V)}
    (path : LevelPath H level s v d) (hd : DeadClosed H level t dead) (hs : s ∈ dead) :
    v ∈ dead := by
  induction path with
  | nil => exact hs
  | @snoc u v d path positive forward ih => exact hd.2 u ih v forward positive

/-- An exhausted operational DFS certifies that the frozen level graph is blocked. -/
theorem dfsProg_exhausted_blocks (G : WeightedDiGraph V) (H : WeightedDiGraph (Node V))
    (st : NetworkState V) (hr : st.Realizes G H) (level : Node V → ℕ)
    (dead : Finset (Node V)) (s t : Node V) (hd : DeadClosed H level t dead)
    (hex : ((dfsProg st level dead s t).eval G.out).stack = []) :
    ∀ d, ¬LevelPath H level s t d := by
  have hi := (dfsProg_complete G H st hr level dead s t hd).2.1
  intro d path
  exact hi.closed.1 (path.dead hi.closed (hi.exhausted hex))

omit [Fintype V] in
theorem DFSData.charge_pop (data : DFSData V) (st : NetworkState V)
    {head : Frame V} {tail : List (Frame V)} (he : data.stack = head :: tail) :
    (data.pop st head).charge = data.charge + 1 := by
  simp only [DFSData.charge, DFSData.pop, he, List.tail_cons, freshCount_cons]
  omega

omit [Fintype V] [DecidableEq V] in
theorem DFSData.charge_push (data : DFSData V) (st : NetworkState V) (u v : Node V) :
    (data.push st u v).charge = data.charge + if data.network.Known u v then 0 else 1 := by
  by_cases hk : data.network.Known u v <;>
    simp [DFSData.charge, DFSData.push, freshCount_cons, hk, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Actual query cost is charged only to exhausted rows and fresh traversals.
A pop transfers its fresh entering-arc flag to failedFresh, so a first
discovery is never charged both as a failure and as a surviving path arc. -/
theorem dfsRun_cost_charged (G : WeightedDiGraph V) (H : WeightedDiGraph (Node V))
    (level : Node V → ℕ) (t : Node V) (fuel : ℕ) (data : DFSData V)
    (hr : data.network.Realizes G H) :
    (dfsRun level t fuel data).cost G.out + data.charge * edgeQueryBound V ≤
      ((dfsRun level t fuel data).eval G.out).charge * edgeQueryBound V := by
  induction fuel generalizing data with
  | zero => simp [dfsRun]
  | succ fuel ih =>
      rw [dfsRun]
      cases hstack : data.stack with
      | nil => simp
      | cons head tail =>
          dsimp only
          split_ifs with ht
          · simp
          · simp only [Prog.cost_bind, Prog.eval_bind]
            have hs := networkSearch_spec G H data.network hr head.vertex
              (eligibleNext level data.dead head.vertex)
            have hc := networkSearch_cost G.out data.network head.vertex
              (eligibleNext level data.dead head.vertex)
            cases he : (networkSearch data.network head.vertex
                (eligibleNext level data.dead head.vertex)).eval G.out with
            | mk st answer =>
                rw [he] at hs
                cases answer with
                | none =>
                    dsimp only
                    have hi := ih (data.pop st head) hs.1
                    rw [data.charge_pop st hstack, Nat.add_mul, Nat.one_mul] at hi
                    simp only [edgeQueryBound] at hi ⊢
                    omega
                | some answer =>
                    obtain ⟨v, c⟩ := answer
                    have hv : v ∈ eligibleNext level data.dead head.vertex := hs.2.1.1
                    dsimp only
                    simp only [hv, ↓reduceIte]
                    have hi := ih (data.push st head.vertex v) hs.1
                    rw [data.charge_push st head.vertex v] at hi
                    by_cases hk : data.network.Known head.vertex v
                    · have hz := networkSearch_cost_of_known_answer G H data.network hr
                        head.vertex (eligibleNext level data.dead head.vertex)
                        (by rw [he]) hk
                      simp only [hk, ↓reduceIte, Nat.add_zero] at hi
                      omega
                    · simp only [hk, ↓reduceIte, Nat.add_mul, Nat.one_mul] at hi
                      simp only [edgeQueryBound] at hi ⊢
                      omega

/-- Starting from an empty search history leaves only failed rows, failed
first discoveries, and fresh arcs on the returned complete path to pay for. -/
theorem dfsProg_cost_charged (G : WeightedDiGraph V) (H : WeightedDiGraph (Node V))
    (st : NetworkState V) (hr : st.Realizes G H) (level : Node V → ℕ)
    (dead : Finset (Node V)) (s t : Node V) :
    (dfsProg st level dead s t).cost G.out ≤
      ((dfsProg st level dead s t).eval G.out).charge * edgeQueryBound V := by
  have h := dfsRun_cost_charged G H level t (2 * Fintype.card (Node V))
    (initialDFS st dead s) hr
  have hz : (initialDFS st dead s).charge = 0 := by
    by_cases hs : s ∈ dead <;> simp [initialDFS, DFSData.charge, hs, freshCount]
  simpa only [dfsProg, hz, Nat.zero_mul, Nat.add_zero] using h

/-- Every failed row kills a previously live destination, so the counter
counts distinct newly dead vertices, not arbitrary search attempts. -/
theorem dfsRun_failedRows (G : WeightedDiGraph V) (H : WeightedDiGraph (Node V))
    (level : Node V → ℕ) (s t : Node V) (fuel : ℕ) (data : DFSData V)
    (hr : data.network.Realizes G H) (hi : DFSInvariant H level s t data)
    (base : ℕ) (hcount : data.failedRows + base = data.dead.card) :
    let result := (dfsRun level t fuel data).eval G.out
    result.failedRows + base = result.dead.card := by
  induction fuel generalizing data with
  | zero => exact hcount
  | succ fuel ih =>
      rw [dfsRun]
      cases hstack : data.stack with
      | nil => exact hcount
      | cons head tail =>
          dsimp only
          split_ifs with ht
          · exact hcount
          · simp only [Prog.eval_bind]
            have hs := networkSearch_spec G H data.network hr head.vertex
              (eligibleNext level data.dead head.vertex)
            cases he : (networkSearch data.network head.vertex
                (eligibleNext level data.dead head.vertex)).eval G.out with
            | mk st answer =>
                rw [he] at hs
                cases answer with
                | none =>
                    apply ih _ hs.1 (hi.pop st hstack ht hs.2.1 hs.2.2.1)
                    have hn : head.vertex ∉ data.dead := hi.live head (by rw [hstack]; simp)
                    simp only [DFSData.pop, card_insert_of_notMem hn]
                    omega
                | some answer =>
                    obtain ⟨v, c⟩ := answer
                    have hv : v ∈ eligibleNext level data.dead head.vertex := hs.2.1.1
                    have hp : 0 < H.c head.vertex v := by rw [hs.2.1.2.2]; exact hs.2.1.2.1
                    dsimp only
                    simp only [hv, ↓reduceIte]
                    exact ih _ hs.1 (hi.push st hstack hv hp (hs.2.2.2 v c rfl) hs.2.2.1) hcount

theorem dfsProg_failedRows (G : WeightedDiGraph V) (H : WeightedDiGraph (Node V))
    (st : NetworkState V) (hr : st.Realizes G H) (level : Node V → ℕ)
    (dead : Finset (Node V)) (s t : Node V) (hd : DeadClosed H level t dead) :
    let result := (dfsProg st level dead s t).eval G.out
    result.failedRows + dead.card = result.dead.card :=
  dfsRun_failedRows G H level s t _ _ hr (initialDFS_invariant H level st dead s t hd)
    dead.card (by simp [initialDFS])

end
end CutQueryComplexity.DirectedUnitST.Blocking

#print axioms CutQueryComplexity.DirectedUnitST.Blocking.StackPath.vertices_nodup
#print axioms CutQueryComplexity.DirectedUnitST.Blocking.deadClosed_insert
#print axioms CutQueryComplexity.DirectedUnitST.Blocking.dfsRun_cost
#print axioms CutQueryComplexity.DirectedUnitST.Blocking.dfsProg_complete
#print axioms CutQueryComplexity.DirectedUnitST.Blocking.dfsProg_exhausted_blocks
#print axioms CutQueryComplexity.DirectedUnitST.Blocking.dfsProg_cost_charged
#print axioms CutQueryComplexity.DirectedUnitST.Blocking.dfsProg_failedRows
