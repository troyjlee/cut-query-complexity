import CutQueryComplexity.DeterministicAPMCExpansion.Flow.BFS
import CutQueryComplexity.DirectedUnitST.Blocking.Phase

/-!
# Query-driven complete-path DFS for symmetric residual capacities

Only the graph-independent path algebra from the directed blocking development
is reused. Its public-orientation state and its query program are not used.
Every traversal here executes the symmetric residual neighbor query. Charging
two units per newly dead vertex and one per surviving stack vertex accounts
for all queries. The caller will augment a returned complete path by one unit.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.Flow

open Finset DirectedCertificate Certificate Prog
open DirectedUnitST.Blocking (Frame StackPath DeadClosed eligibleNext mem_eligibleNext
  deadClosed_insert LevelPath)
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

structure DFSData (V : Type) where
  dead : Finset (NetworkVertex V)
  stack : List (Frame V)

namespace DFSData

def work (data : DFSData V) : ℕ :=
  2 * (Fintype.card (NetworkVertex V) - data.dead.card) - data.stack.length

def charge (data : DFSData V) : ℕ := 2 * data.dead.card + data.stack.length

def push (data : DFSData V) (v : NetworkVertex V) : DFSData V :=
  { data with stack := ⟨v, false⟩ :: data.stack }

def pop (data : DFSData V) (head : Frame V) : DFSData V :=
  { dead := insert head.vertex data.dead, stack := data.stack.tail }

theorem charge_push (data : DFSData V) (v : NetworkVertex V) :
    (data.push v).charge = data.charge + 1 := by
  simp only [charge, push, List.length_cons]
  omega

theorem charge_pop (data : DFSData V) {head : Frame V} {tail : List (Frame V)}
    (hs : data.stack = head :: tail) (hd : head.vertex ∉ data.dead) :
    (data.pop head).charge = data.charge + 1 := by
  simp only [charge, pop, hs, List.tail_cons, List.length_cons, card_insert_of_notMem hd]
  omega

end DFSData

def dfsRun (a z : V → ℕ) (f : NetworkVertex V → NetworkVertex V → ℝ)
    (level : NetworkVertex V → ℕ) (t : NetworkVertex V) :
    ℕ → DFSData V → Prog (Finset V) ℝ (DFSData V)
  | 0, data => .pure data
  | fuel + 1, data => match data.stack with
    | [] => .pure data
    | head :: _ =>
        if head.vertex = t then .pure data else
          (neighborProg a z f head.vertex (eligibleNext level data.dead head.vertex)).bind
            fun answer => match answer with
            | none => dfsRun a z f level t fuel (data.pop head)
            | some v =>
                if v ∈ eligibleNext level data.dead head.vertex then
                  dfsRun a z f level t fuel (data.push v)
                else .pure data

theorem dfsRun_cost (read : Finset V → ℝ) (a z : V → ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ) (level : NetworkVertex V → ℕ)
    (t : NetworkVertex V) (fuel : ℕ) (data : DFSData V) :
    (dfsRun a z f level t fuel data).cost read ≤ fuel * neighborBudget V := by
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
            have hc := neighborProg_cost read a z f head.vertex
              (eligibleNext level data.dead head.vertex)
            cases he : (neighborProg a z f head.vertex
                (eligibleNext level data.dead head.vertex)).eval read with
            | none =>
                change (neighborProg a z f head.vertex
                    (eligibleNext level data.dead head.vertex)).cost read +
                  (dfsRun a z f level t fuel (data.pop head)).cost read ≤
                    (fuel + 1) * neighborBudget V
                have hi := ih (data.pop head)
                rw [Nat.succ_mul]
                omega
            | some v =>
                change (neighborProg a z f head.vertex
                    (eligibleNext level data.dead head.vertex)).cost read +
                  (if v ∈ eligibleNext level data.dead head.vertex then
                    dfsRun a z f level t fuel (data.push v)
                    else Prog.pure data).cost read ≤ (fuel + 1) * neighborBudget V
                split_ifs
                · have hi := ih (data.push v)
                  rw [Nat.succ_mul]
                  omega
                · simp only [Prog.cost_pure, Nat.add_zero]
                  rw [Nat.succ_mul]
                  omega

structure DFSInvariant (H : WeightedDiGraph (NetworkVertex V))
    (level : NetworkVertex V → ℕ) (s t : NetworkVertex V) (data : DFSData V) : Prop where
  path : data.stack = [] ∨ StackPath H level s data.stack
  live : ∀ frame ∈ data.stack, frame.vertex ∉ data.dead
  closed : DeadClosed H level t data.dead
  exhausted : data.stack = [] → s ∈ data.dead

theorem DFSInvariant.live_bound {H : WeightedDiGraph (NetworkVertex V)}
    {level : NetworkVertex V → ℕ} {s t : NetworkVertex V} {data : DFSData V}
    (h : DFSInvariant H level s t data) :
    data.stack.length ≤ Fintype.card (NetworkVertex V) - data.dead.card := by
  rcases h.path with he | hp
  · simp [he]
  · have hsub : (data.stack.map Frame.vertex).toFinset ⊆ data.deadᶜ := by
      intro v hv
      obtain ⟨frame, hf, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
      exact mem_compl.mpr (h.live frame hf)
    have hc := card_le_card hsub
    rw [List.toFinset_card_of_nodup hp.vertices_nodup, List.length_map, card_compl] at hc
    exact hc

theorem DFSInvariant.push {H : WeightedDiGraph (NetworkVertex V)}
    {level : NetworkVertex V → ℕ} {s t : NetworkVertex V} {data : DFSData V}
    (h : DFSInvariant H level s t data) {head : Frame V} {tail : List (Frame V)}
    {v : NetworkVertex V} (hstack : data.stack = head :: tail)
    (hv : v ∈ eligibleNext level data.dead head.vertex) (hpos : 0 < H.c head.vertex v) :
    DFSInvariant H level s t (data.push v) := by
  have hp : StackPath H level s (head :: tail) := by
    rcases h.path with he | hp
    · rw [hstack] at he; contradiction
    · simpa only [hstack] using hp
  obtain ⟨hlevel, hvdead⟩ := (mem_eligibleNext _ _ _ _).mp hv
  refine ⟨Or.inr ?_, ?_, h.closed, ?_⟩
  · simpa only [DFSData.push, hstack] using StackPath.push hp v false hpos hlevel
  · intro frame hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact hvdead
    · exact h.live frame hf
  · intro he
    simp [DFSData.push] at he

theorem DFSInvariant.pop {H : WeightedDiGraph (NetworkVertex V)}
    {level : NetworkVertex V → ℕ} {s t : NetworkVertex V} {data : DFSData V}
    (h : DFSInvariant H level s t data) {head : Frame V} {tail : List (Frame V)}
    (hstack : data.stack = head :: tail) (ht : head.vertex ≠ t)
    (hz : ∀ v ∈ eligibleNext level data.dead head.vertex, H.c head.vertex v = 0) :
    DFSInvariant H level s t (data.pop head) := by
  have hp : StackPath H level s (head :: tail) := by
    rcases h.path with he | hp
    · rw [hstack] at he; contradiction
    · simpa only [hstack] using hp
  have hnd := hp.vertices_nodup
  simp only [List.map_cons, List.nodup_cons] at hnd
  refine ⟨?_, ?_, deadClosed_insert h.closed ht hz, ?_⟩
  · simpa only [DFSData.pop, hstack, List.tail_cons] using hp.tail
  · intro frame hf
    change frame ∈ data.stack.tail at hf
    rw [hstack, List.tail_cons] at hf
    change frame.vertex ∉ insert head.vertex data.dead
    rw [mem_insert, not_or]
    refine ⟨?_, h.live frame (by rw [hstack]; exact List.mem_cons_of_mem _ hf)⟩
    intro he
    exact hnd.1 (List.mem_map.mpr ⟨frame, hf, he⟩)
  · intro he
    change data.stack.tail = [] at he
    rw [hstack, List.tail_cons] at he
    subst tail
    cases hp with
    | root => exact mem_insert_self _ _

theorem DFSInvariant.work_push {H : WeightedDiGraph (NetworkVertex V)}
    {level : NetworkVertex V → ℕ} {s t : NetworkVertex V} {data : DFSData V}
    (v : NetworkVertex V) (hnext : DFSInvariant H level s t (data.push v)) :
    (data.push v).work + 1 = data.work := by
  have hn := hnext.live_bound
  simp only [DFSData.push, List.length_cons] at hn
  simp only [DFSData.work, DFSData.push, List.length_cons]
  omega

theorem DFSInvariant.work_pop {H : WeightedDiGraph (NetworkVertex V)}
    {level : NetworkVertex V → ℕ} {s t : NetworkVertex V} {data : DFSData V}
    (h : DFSInvariant H level s t data) {head : Frame V} {tail : List (Frame V)}
    (hstack : data.stack = head :: tail) : (data.pop head).work + 1 = data.work := by
  have hl := h.live_bound
  have hhd : head.vertex ∉ data.dead := h.live head (by rw [hstack]; simp)
  have hc := card_le_univ data.dead
  simp only [DFSData.work, DFSData.pop, card_insert_of_notMem hhd,
    hstack, List.tail_cons, List.length_cons] at hl ⊢
  omega

def DFSFinished (t : NetworkVertex V) (data : DFSData V) : Prop :=
  data.stack = [] ∨ ∃ head tail, data.stack = head :: tail ∧ head.vertex = t

theorem dfsRun_complete (G : WeightedGraph V) (a z : V → ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ)
    (hf : (directed (twoStar G a z)).Feasible f)
    (level : NetworkVertex V → ℕ) (s t : NetworkVertex V) (fuel : ℕ) (data : DFSData V)
    (hi : DFSInvariant (residualNetwork G a z f hf) level s t data)
    (hwork : data.work ≤ fuel) :
    let result := (dfsRun a z f level t fuel data).eval G.cut
    DFSInvariant (residualNetwork G a z f hf) level s t result ∧ DFSFinished t result := by
  induction fuel generalizing data with
  | zero =>
      have hl := hi.live_bound
      have he : data.stack = [] := by
        apply List.eq_nil_of_length_eq_zero
        unfold DFSData.work at hwork
        omega
      exact ⟨hi, Or.inl he⟩
  | succ fuel ih =>
      rw [dfsRun]
      cases hstack : data.stack with
      | nil => exact ⟨hi, Or.inl hstack⟩
      | cons head tail =>
          dsimp only
          split_ifs with ht
          · exact ⟨hi, Or.inr ⟨head, tail, hstack, ht⟩⟩
          · simp only [Prog.eval_bind]
            have hs := neighborProg_residual_spec G a z f hf head.vertex
              (eligibleNext level data.dead head.vertex)
            cases he : (neighborProg a z f head.vertex
                (eligibleNext level data.dead head.vertex)).eval G.cut with
            | none =>
                rw [he] at hs
                have hnext := hi.pop hstack ht hs
                apply ih _ hnext
                have hw := hi.work_pop hstack
                omega
            | some v =>
                rw [he] at hs
                have hv := hs.1
                have hnext := hi.push hstack hv hs.2
                simp only [hv, ↓reduceIte]
                apply ih _ hnext
                have hw := DFSInvariant.work_push v hnext
                omega

/-- The potential identity counts every neighbor query, including failed rows. -/
theorem dfsRun_cost_charged (G : WeightedGraph V) (a z : V → ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ)
    (hf : (directed (twoStar G a z)).Feasible f)
    (level : NetworkVertex V → ℕ) (s t : NetworkVertex V) (fuel : ℕ) (data : DFSData V)
    (hi : DFSInvariant (residualNetwork G a z f hf) level s t data) :
    (dfsRun a z f level t fuel data).cost G.cut + data.charge * neighborBudget V ≤
      ((dfsRun a z f level t fuel data).eval G.cut).charge * neighborBudget V := by
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
            have hs := neighborProg_residual_spec G a z f hf head.vertex
              (eligibleNext level data.dead head.vertex)
            have hc := neighborProg_cost G.cut a z f head.vertex
              (eligibleNext level data.dead head.vertex)
            cases he : (neighborProg a z f head.vertex
                (eligibleNext level data.dead head.vertex)).eval G.cut with
            | none =>
                change (neighborProg a z f head.vertex
                    (eligibleNext level data.dead head.vertex)).cost G.cut +
                  (dfsRun a z f level t fuel (data.pop head)).cost G.cut +
                    data.charge * neighborBudget V ≤
                  ((dfsRun a z f level t fuel (data.pop head)).eval G.cut).charge *
                    neighborBudget V
                rw [he] at hs
                have hnext := hi.pop hstack ht hs
                have hind := ih _ hnext
                have hcharge := data.charge_pop hstack
                  (hi.live head (by rw [hstack]; simp))
                rw [hcharge, Nat.add_mul, one_mul] at hind
                omega
            | some v =>
                rw [he] at hs
                have hnext := hi.push hstack hs.1 hs.2
                simp only [hs.1, ↓reduceIte]
                have hind := ih _ hnext
                rw [data.charge_push v, Nat.add_mul, one_mul] at hind
                omega

def initialDFS (dead : Finset (NetworkVertex V)) (s : NetworkVertex V) : DFSData V where
  dead := dead
  stack := if s ∈ dead then [] else [⟨s, false⟩]

theorem initialDFS_invariant (H : WeightedDiGraph (NetworkVertex V))
    (level : NetworkVertex V → ℕ) (dead : Finset (NetworkVertex V))
    (s t : NetworkVertex V) (hd : DeadClosed H level t dead) :
    DFSInvariant H level s t (initialDFS dead s) := by
  by_cases hs : s ∈ dead
  · refine ⟨Or.inl (by simp [initialDFS, hs]), ?_, hd, fun _ => hs⟩
    intro frame hframe
    simp [initialDFS, hs] at hframe
  · refine ⟨Or.inr ?_, ?_, hd, ?_⟩
    · simpa only [initialDFS, hs, ↓reduceIte] using
        (StackPath.root (H := H) (level := level) (s := s))
    · intro frame hframe
      simp only [initialDFS, hs, ↓reduceIte, List.mem_singleton] at hframe
      subst frame
      exact hs
    · intro he
      simp [initialDFS, hs] at he

def dfsProg (a z : V → ℕ) (f : NetworkVertex V → NetworkVertex V → ℝ)
    (level : NetworkVertex V → ℕ) (dead : Finset (NetworkVertex V))
    (s t : NetworkVertex V) : Prog (Finset V) ℝ (DFSData V) :=
  dfsRun a z f level t (2 * Fintype.card (NetworkVertex V)) (initialDFS dead s)

theorem dfsProg_complete (G : WeightedGraph V) (a z : V → ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ)
    (hf : (directed (twoStar G a z)).Feasible f)
    (level : NetworkVertex V → ℕ) (dead : Finset (NetworkVertex V))
    (s t : NetworkVertex V) (hd : DeadClosed (residualNetwork G a z f hf) level t dead) :
    let result := (dfsProg a z f level dead s t).eval G.cut
    DFSInvariant (residualNetwork G a z f hf) level s t result ∧ DFSFinished t result := by
  apply dfsRun_complete G a z f hf level s t _ _
    (initialDFS_invariant _ level dead s t hd)
  unfold DFSData.work initialDFS
  omega

theorem dfsProg_cost (read : Finset V → ℝ) (a z : V → ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ) (level : NetworkVertex V → ℕ)
    (dead : Finset (NetworkVertex V)) (s t : NetworkVertex V) :
    (dfsProg a z f level dead s t).cost read ≤
      2 * Fintype.card (NetworkVertex V) * neighborBudget V :=
  dfsRun_cost read a z f level t _ _

theorem dfsProg_exhausted_blocks (G : WeightedGraph V) (a z : V → ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ)
    (hf : (directed (twoStar G a z)).Feasible f)
    (level : NetworkVertex V → ℕ) (dead : Finset (NetworkVertex V))
    (s t : NetworkVertex V) (hd : DeadClosed (residualNetwork G a z f hf) level t dead)
    (hex : ((dfsProg a z f level dead s t).eval G.cut).stack = []) :
    ∀ d, ¬ LevelPath (residualNetwork G a z f hf) level s t d := by
  have hi := (dfsProg_complete G a z f hf level dead s t hd).1
  intro d path
  exact hi.closed.1 (path.dead hi.closed (hi.exhausted hex))

/-- Path length, including the root frame, is determined by frozen levels. -/
theorem stackPath_length {H : WeightedDiGraph (NetworkVertex V)}
    {level : NetworkVertex V → ℕ} {s : NetworkVertex V} {stack : List (Frame V)}
    (hp : StackPath H level s stack) :
    ∀ head tail, stack = head :: tail → level head.vertex + 1 = level s + stack.length := by
  induction hp with
  | root => intro head tail he; cases he; simp
  | @push head tail path v fresh positive forward ih =>
      intro top rest he
      cases he
      have h := ih head tail rfl
      simp only [List.length_cons] at h ⊢
      omega

end
end CutQueryComplexity.DeterministicAPMCExpansion.Flow

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.dfsRun_complete
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.dfsRun_cost_charged
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.dfsProg_exhausted_blocks
