import CutQueryComplexity.DirectedUnitST.Blocking.DFS
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Whole-path integral augmentation and blocking phases

All augmentation data is computed from the public returned DFS stack and its
learned capacities. The hidden residual graph appears only in proofs. Directed
natural-number usage is kept separate from its antisymmetric signed update.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DirectedUnitST.Blocking

open Finset DirectedCertificate Certificate Prog
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Actual consecutive directed arcs of a reversed DFS stack. -/
def stackArcs : List (Frame V) → Finset (Node V × Node V)
  | child :: parent :: tail => insert (parent.vertex, child.vertex) (stackArcs (parent :: tail))
  | _ => ∅

omit [Fintype V] in
theorem mem_stackArcs_vertices (stack : List (Frame V)) {u v : Node V}
    (h : (u, v) ∈ stackArcs stack) :
    u ∈ stack.map Frame.vertex ∧ v ∈ stack.map Frame.vertex := by
  induction stack with
  | nil => simp [stackArcs] at h
  | cons child tail ih =>
      cases tail with
      | nil => simp [stackArcs] at h
      | cons parent rest =>
          rcases mem_insert.mp h with he | he
          · cases he
            simp
          · obtain ⟨hu, hv⟩ := ih he
            exact ⟨List.mem_cons_of_mem _ hu, List.mem_cons_of_mem _ hv⟩

omit [Fintype V] in
theorem stackKnown_arc {st : NetworkState V} {stack : List (Frame V)}
    (h : StackKnown st stack) {u v : Node V} (he : (u, v) ∈ stackArcs stack) :
    st.Known u v := by
  induction stack with
  | nil => simp [stackArcs] at he
  | cons child tail ih =>
      cases tail with
      | nil => simp [stackArcs] at he
      | cons parent rest =>
          rcases mem_insert.mp he with he | he
          · cases he
            exact h.1
          · exact ih h.2 he

omit [Fintype V] in
theorem StackPath.arc {H : WeightedDiGraph (Node V)} {level : Node V → ℕ}
    {s : Node V} {stack : List (Frame V)} (hp : StackPath H level s stack)
    {u v : Node V} (he : (u, v) ∈ stackArcs stack) :
    0 < H.c u v ∧ level v = level u + 1 := by
  induction hp with
  | root => simp [stackArcs] at he
  | @push head tail path w fresh positive forward ih =>
      rcases mem_insert.mp he with he | he
      · cases he
        exact ⟨positive, forward⟩
      · exact ih he

omit [Fintype V] in
theorem StackPath.reverse_not_mem {H : WeightedDiGraph (Node V)} {level : Node V → ℕ}
    {s : Node V} {stack : List (Frame V)} (hp : StackPath H level s stack)
    {u v : Node V} (he : (u, v) ∈ stackArcs stack) : (v, u) ∉ stackArcs stack := by
  intro hr
  have hf := (hp.arc he).2
  have hb := (hp.arc hr).2
  omega

omit [Fintype V] in
theorem StackPath.new_arc {H : WeightedDiGraph (Node V)} {level : Node V → ℕ}
    {s v : Node V} {head : Frame V} {tail : List (Frame V)}
    (hp : StackPath H level s (head :: tail)) (hv : level v = level head.vertex + 1) :
    (head.vertex, v) ∉ stackArcs (head :: tail) := by
  intro hm
  obtain ⟨f, hf, he⟩ := List.mem_map.mp (mem_stackArcs_vertices _ hm).2
  have hle := hp.level_le_head head tail rfl f hf
  rw [he] at hle
  omega

omit [Fintype V] in
theorem StackPath.freshCount_le_arcs {H : WeightedDiGraph (Node V)} {level : Node V → ℕ}
    {s : Node V} {stack : List (Frame V)} (hp : StackPath H level s stack) :
    freshCount stack ≤ (stackArcs stack).card := by
  induction hp with
  | root => simp [freshCount, stackArcs]
  | @push head tail path v fresh positive forward ih =>
      have hn := path.new_arc forward
      rw [freshCount_cons]
      simp only [stackArcs, card_insert_of_notMem hn]
      split <;> omega

/-- Nonnegative directed usage for one whole-path augmentation. -/
def pathUse (stack : List (Frame V)) (amount : ℕ) (u v : Node V) : ℕ :=
  if (u, v) ∈ stackArcs stack then amount else 0

def pathDelta (stack : List (Frame V)) (amount : ℕ) : Node V → Node V → ℝ :=
  Repair.phaseDelta fun u v => (pathUse stack amount u v : ℝ)

def arcUse (a b : Node V) (amount : ℕ) (u v : Node V) : ℕ :=
  if u = a ∧ v = b then amount else 0

omit [Fintype V] in
theorem pathUse_push {H : WeightedDiGraph (Node V)} {level : Node V → ℕ}
    {s v : Node V} {head : Frame V} {tail : List (Frame V)}
    (hp : StackPath H level s (head :: tail)) (hlevel : level v = level head.vertex + 1)
    (fresh : Bool) (amount : ℕ) (a b : Node V) :
    pathUse (⟨v, fresh⟩ :: head :: tail) amount a b =
      arcUse head.vertex v amount a b + pathUse (head :: tail) amount a b := by
  have hn := hp.new_arc hlevel
  by_cases he : a = head.vertex ∧ b = v
  · obtain ⟨rfl, rfl⟩ := he
    simp [pathUse, stackArcs, arcUse, hn]
  · simp only [pathUse, stackArcs, mem_insert, Prod.mk.injEq, arcUse, he, ↓reduceIte,
      false_or, Nat.zero_add]

omit [Fintype V] in
theorem pathDelta_push {H : WeightedDiGraph (Node V)} {level : Node V → ℕ}
    {s v : Node V} {head : Frame V} {tail : List (Frame V)}
    (hp : StackPath H level s (head :: tail)) (hlevel : level v = level head.vertex + 1)
    (fresh : Bool) (amount : ℕ) (a b : Node V) :
    pathDelta (⟨v, fresh⟩ :: head :: tail) amount a b =
      Repair.phaseDelta (fun u w => (arcUse head.vertex v amount u w : ℝ)) a b +
        pathDelta (head :: tail) amount a b := by
  simp only [pathDelta, Repair.phaseDelta, pathUse_push hp hlevel, Nat.cast_add]
  ring

theorem arcDelta_netOut (a b : Node V) (amount : ℕ) (x : Node V) :
    netOut (Repair.phaseDelta fun u v => (arcUse a b amount u v : ℝ)) x =
      (if x = a then (amount : ℝ) else 0) - (if x = b then (amount : ℝ) else 0) := by
  by_cases ha : x = a <;> by_cases hb : x = b <;>
    simp [netOut, Repair.phaseDelta, arcUse, ha, hb, sum_sub_distrib, ite_and]

/-- The signed whole-path update has exactly its two terminal divergences. -/
theorem StackPath.pathDelta_netOut {H : WeightedDiGraph (Node V)} {level : Node V → ℕ}
    {s : Node V} {stack : List (Frame V)} (hp : StackPath H level s stack) (amount : ℕ) :
    ∀ head tail, stack = head :: tail → ∀ x,
      netOut (pathDelta stack amount) x =
        (if x = s then (amount : ℝ) else 0) -
          (if x = head.vertex then (amount : ℝ) else 0) := by
  induction hp with
  | root =>
      intro head tail he x
      cases he
      simp [pathDelta, Repair.phaseDelta, pathUse, stackArcs, netOut]
  | @push head tail path v fresh positive forward ih =>
      intro top rest he x
      cases he
      have heq : pathDelta (⟨v, fresh⟩ :: head :: tail) amount =
          fun u w => Repair.phaseDelta (fun a b => (arcUse head.vertex v amount a b : ℝ)) u w +
            pathDelta (head :: tail) amount u w := by
        funext u w
        exact pathDelta_push path forward fresh amount u w
      rw [heq]
      simp only [netOut, sum_add_distrib]
      change netOut (Repair.phaseDelta (fun a b => (arcUse head.vertex v amount a b : ℝ))) x +
        netOut (pathDelta (head :: tail) amount) x = _
      rw [arcDelta_netOut, ih head tail rfl x]
      ring

omit [Fintype V] in
theorem StackPath.arcs_nonempty_of_head_ne {H : WeightedDiGraph (Node V)}
    {level : Node V → ℕ} {s : Node V} {head : Frame V} {tail : List (Frame V)}
    (hp : StackPath H level s (head :: tail)) (hne : head.vertex ≠ s) :
    (stackArcs (head :: tail)).Nonempty := by
  cases hp with
  | root => exact False.elim (hne rfl)
  | @push old rest path v fresh positive forward => exact insert_nonempty _ _

omit [Fintype V] in
theorem pathDelta_forward {H : WeightedDiGraph (Node V)} {level : Node V → ℕ}
    {s : Node V} {stack : List (Frame V)} (hp : StackPath H level s stack)
    (amount : ℕ) {u v : Node V} (he : (u, v) ∈ stackArcs stack) :
    pathDelta stack amount u v = amount := by
  simp [pathDelta, Repair.phaseDelta, pathUse, he, hp.reverse_not_mem he]

omit [Fintype V] in
theorem pathDelta_off_le (stack : List (Frame V)) (amount : ℕ) {u v : Node V}
    (he : (u, v) ∉ stackArcs stack) : pathDelta stack amount u v ≤ 0 := by
  simp only [pathDelta, Repair.phaseDelta, pathUse, he, ↓reduceIte, Nat.cast_zero, zero_sub]
  exact neg_nonpos.mpr (Nat.cast_nonneg _)

theorem pathDelta_support {G : WeightedDiGraph V} {H : WeightedDiGraph (Node V)}
    {st : NetworkState V} (hr : st.Realizes G H) (stack : List (Frame V))
    (hk : StackKnown st stack) (amount : ℕ) (u v : Node V) (huv : ¬st.Known u v) :
    pathDelta stack amount u v = 0 := by
  have hforward : (u, v) ∉ stackArcs stack := fun h => huv (stackKnown_arc hk h)
  have hreverse : (v, u) ∉ stackArcs stack :=
    fun h => huv ((hr.known_symm u v).mpr (stackKnown_arc hk h))
  simp [pathDelta, Repair.phaseDelta, pathUse, hforward, hreverse]

/-- Purely public bottleneck; the empty path has zero augmentation. -/
def pathAmount (st : NetworkState V) (stack : List (Frame V)) : ℕ :=
  if h : (stackArcs stack).Nonempty then
    (stackArcs stack).inf' h (fun e => ⌊st.knownCapacity e.1 e.2⌋₊)
  else 0

omit [Fintype V] in
theorem pathAmount_le (st : NetworkState V) (stack : List (Frame V))
    {u v : Node V} (he : (u, v) ∈ stackArcs stack) :
    pathAmount st stack ≤ ⌊st.knownCapacity u v⌋₊ := by
  have hne : (stackArcs stack).Nonempty := ⟨(u, v), he⟩
  rw [pathAmount, dite_eq_left hne]
  exact inf'_le _ he

def IntegralCap (H : WeightedDiGraph (Node V)) : Prop :=
  ∀ u v, ∃ k : ℕ, H.c u v = k

omit [Fintype V] [DecidableEq V] in
theorem integralCap_floor {H : WeightedDiGraph (Node V)} (h : IntegralCap H) (u v : Node V) :
    (⌊H.c u v⌋₊ : ℝ) = H.c u v := by
  obtain ⟨k, hk⟩ := h u v
  simp [hk]

theorem pathAmount_pos {G : WeightedDiGraph V} {H : WeightedDiGraph (Node V)}
    {st : NetworkState V} (hr : st.Realizes G H) {level : Node V → ℕ}
    {s : Node V} {stack : List (Frame V)} (hp : StackPath H level s stack)
    (hk : StackKnown st stack) (hint : IntegralCap H)
    (hne : (stackArcs stack).Nonempty) : 0 < pathAmount st stack := by
  rw [pathAmount, dite_eq_left hne]
  apply (lt_inf'_iff hne).mpr
  intro e he
  rw [← hr.known e.1 e.2 (stackKnown_arc hk he)]
  obtain ⟨k, hcap⟩ := hint e.1 e.2
  have hpos := (hp.arc he).1
  rw [hcap] at hpos ⊢
  simpa only [Nat.floor_natCast, Nat.cast_pos] using hpos

/-- The public bottleneck always gives a feasible signed whole-path update. -/
theorem pathDelta_feasible {G : WeightedDiGraph V} {H : WeightedDiGraph (Node V)}
    {st : NetworkState V} (hr : st.Realizes G H) {level : Node V → ℕ}
    {s : Node V} {stack : List (Frame V)} (hp : StackPath H level s stack)
    (hk : StackKnown st stack) : H.Feasible (pathDelta stack (pathAmount st stack)) := by
  refine ⟨Repair.phaseDelta_isFlow _, ?_⟩
  intro u v
  by_cases he : (u, v) ∈ stackArcs stack
  · rw [pathDelta_forward hp _ he]
    have hc := pathAmount_le st stack he
    have hcap := hr.known u v (stackKnown_arc hk he)
    calc
      (pathAmount st stack : ℝ) ≤ ⌊st.knownCapacity u v⌋₊ := by exact_mod_cast hc
      _ ≤ st.knownCapacity u v := Nat.floor_le (by rw [← hcap]; exact H.nonneg u v)
      _ = H.c u v := hcap.symm
  · exact (pathDelta_off_le stack _ he).trans (H.nonneg u v)

/-- The public update represents the actual residual after the augmentation. -/
theorem augment_realizes {G : WeightedDiGraph V} {H : WeightedDiGraph (Node V)}
    {st : NetworkState V} (hr : st.Realizes G H) {level : Node V → ℕ}
    {s : Node V} {stack : List (Frame V)} (hp : StackPath H level s stack)
    (hk : StackKnown st stack) :
    (st.applyFlow (pathDelta stack (pathAmount st stack))).Realizes G
      (Repair.residual H _ (pathDelta_feasible hr hp hk)) :=
  hr.applyFlow _ (pathDelta_feasible hr hp hk) (pathDelta_support hr stack hk _)

omit [Fintype V] in
theorem pathAmount_attained (st : NetworkState V) (stack : List (Frame V))
    (hne : (stackArcs stack).Nonempty) :
    ∃ e ∈ stackArcs stack, pathAmount st stack = ⌊st.knownCapacity e.1 e.2⌋₊ := by
  have hm : (stackArcs stack).inf' hne (fun e => ⌊st.knownCapacity e.1 e.2⌋₊) ≤
      pathAmount st stack := by
    simpa only [pathAmount, dite_eq_left hne] using
      (le_refl ((stackArcs stack).inf' hne (fun e => ⌊st.knownCapacity e.1 e.2⌋₊)))
  obtain ⟨e, he, hle⟩ := (inf'_le_iff hne).mp hm
  exact ⟨e, he, Nat.le_antisymm (pathAmount_le st stack he) hle⟩

/-- A nonempty integral path saturates at least one of its forward arcs. -/
theorem augmentation_saturates {G : WeightedDiGraph V} {H : WeightedDiGraph (Node V)}
    {st : NetworkState V} (hr : st.Realizes G H) {level : Node V → ℕ}
    {s : Node V} {stack : List (Frame V)} (hp : StackPath H level s stack)
    (hk : StackKnown st stack) (hint : IntegralCap H)
    (hne : (stackArcs stack).Nonempty) :
    ∃ e ∈ stackArcs stack,
      (Repair.residual H _ (pathDelta_feasible hr hp hk)).c e.1 e.2 = 0 := by
  obtain ⟨e, he, hamount⟩ := pathAmount_attained st stack hne
  refine ⟨e, he, ?_⟩
  rw [Repair.residual_c, pathDelta_forward hp _ he, hamount,
    ← hr.known e.1 e.2 (stackKnown_arc hk he), integralCap_floor hint]
  exact sub_self _

omit [Fintype V] [DecidableEq V] in
/-- Subtracting an integral directed usage preserves integral capacities. -/
theorem integralCap_residual {H : WeightedDiGraph (Node V)} (hint : IntegralCap H)
    (g : Node V → Node V → ℕ)
    (hf : H.Feasible (Repair.phaseDelta fun u v => (g u v : ℝ))) :
    IntegralCap (Repair.residual H _ hf) := by
  intro u v
  obtain ⟨k, hk⟩ := hint u v
  have hleR : (g u v : ℝ) ≤ k + g v u := by
    have hle := hf.2 u v
    simp only [Repair.phaseDelta, hk] at hle
    linarith
  have hle : g u v ≤ k + g v u := by exact_mod_cast hleR
  refine ⟨k + g v u - g u v, ?_⟩
  rw [Repair.residual_c, hk, Nat.cast_sub hle, Nat.cast_add, Repair.phaseDelta]
  ring

omit [Fintype V] [DecidableEq V] in
/-- Forward capacities can only decrease during a frozen-level phase. -/
theorem forward_residual_le (H : WeightedDiGraph (Node V)) (level : Node V → ℕ)
    (g : Node V → Node V → ℕ)
    (hg : ∀ u v, g u v ≠ 0 → level v = level u + 1)
    (hf : H.Feasible (Repair.phaseDelta fun u v => (g u v : ℝ)))
    {u v : Node V} (hlevel : level v = level u + 1) :
    (Repair.residual H _ hf).c u v ≤ H.c u v := by
  have hreverse : g v u = 0 := by
    by_contra hn
    have hb := hg v u hn
    omega
  simp only [Repair.residual_c, Repair.phaseDelta, hreverse, Nat.cast_zero, sub_zero]
  exact sub_le_self _ (Nat.cast_nonneg _)

omit [Fintype V] [DecidableEq V] in
theorem deadClosed_residual {H : WeightedDiGraph (Node V)} {level : Node V → ℕ}
    {t : Node V} {dead : Finset (Node V)} (hd : DeadClosed H level t dead)
    (g : Node V → Node V → ℕ)
    (hg : ∀ u v, g u v ≠ 0 → level v = level u + 1)
    (hf : H.Feasible (Repair.phaseDelta fun u v => (g u v : ℝ))) :
    DeadClosed (Repair.residual H _ hf) level t dead := by
  refine ⟨hd.1, ?_⟩
  intro u hu v hlevel hpos
  exact hd.2 u hu v hlevel (hpos.trans_le (forward_residual_le H level g hg hf hlevel))

omit [Fintype V] in
theorem pathUse_forward {H : WeightedDiGraph (Node V)} {level : Node V → ℕ}
    {s : Node V} {stack : List (Frame V)} (hp : StackPath H level s stack)
    (amount : ℕ) (u v : Node V) (huse : pathUse stack amount u v ≠ 0) :
    level v = level u + 1 := by
  by_cases he : (u, v) ∈ stackArcs stack
  · exact (hp.arc he).2
  · simp [pathUse, he] at huse

/-- Every surviving first-discovery arc on a completed nonempty integral
path receives positive directed usage in its immediate augmentation. -/
theorem augmentation_uses_arc {G : WeightedDiGraph V} {H : WeightedDiGraph (Node V)}
    {st : NetworkState V} (hr : st.Realizes G H) {level : Node V → ℕ}
    {s : Node V} {stack : List (Frame V)} (hp : StackPath H level s stack)
    (hk : StackKnown st stack) (hint : IntegralCap H) {u v : Node V}
    (he : (u, v) ∈ stackArcs stack) : 0 < pathUse stack (pathAmount st stack) u v := by
  rw [pathUse, ite_eq_left he]
  exact pathAmount_pos hr hp hk hint ⟨(u, v), he⟩

/-- The successful first-discovery charge is paid only when the whole
returned path receives its next positive integral augmentation. -/
theorem freshCount_le_augmentation_mass {G : WeightedDiGraph V}
    {H : WeightedDiGraph (Node V)} {st : NetworkState V} (hr : st.Realizes G H)
    {level : Node V → ℕ} {s : Node V} {stack : List (Frame V)}
    (hp : StackPath H level s stack) (hk : StackKnown st stack) (hint : IntegralCap H) :
    freshCount stack ≤ ∑ u, ∑ v, pathUse stack (pathAmount st stack) u v := by
  apply hp.freshCount_le_arcs.trans
  exact Repair.discoveries_le_phase_mass _ (stackArcs stack)
    (fun e he => augmentation_uses_arc hr hp hk hint he)

/-- A completed DFS costs only newly dead destinations and the directed
usage of its immediately following whole-path augmentation. -/
theorem dfsProg_cost_augmentation (G : WeightedDiGraph V) (H : WeightedDiGraph (Node V))
    (st : NetworkState V) (hr : st.Realizes G H) (hint : IntegralCap H)
    (level : Node V → ℕ) (dead : Finset (Node V)) (s t : Node V)
    (hd : DeadClosed H level t dead) :
    let found := (dfsProg st level dead s t).eval G.out
    (dfsProg st level dead s t).cost G.out + (2 * dead.card) * edgeQueryBound V ≤
      (2 * found.dead.card +
        ∑ u, ∑ v, pathUse found.stack (pathAmount found.network found.stack) u v) *
          edgeQueryBound V := by
  let found := (dfsProg st level dead s t).eval G.out
  have hs := dfsProg_complete G H st hr level dead s t hd
  have hcount := dfsProg_failedRows G H st hr level dead s t hd
  have hcost := dfsProg_cost_charged G H st hr level dead s t
  have hfresh : freshCount found.stack ≤
      ∑ u, ∑ v, pathUse found.stack (pathAmount found.network found.stack) u v := by
    rcases hs.2.1.path with he | hp
    · simp [found, he, freshCount]
    · exact freshCount_le_augmentation_mass hs.1 hp hs.2.1.learned hint
  have hcharge : found.charge ≤ 2 * found.failedRows +
      ∑ u, ∑ v, pathUse found.stack (pathAmount found.network found.stack) u v := by
    have hf := hs.2.1.failed_le_rows
    change found.failedFresh ≤ found.failedRows at hf
    unfold DFSData.charge
    omega
  have hbound := hcost.trans (Nat.mul_le_mul_right (edgeQueryBound V) hcharge)
  change (dfsProg st level dead s t).cost G.out + (2 * dead.card) * edgeQueryBound V ≤ _
  calc
    _ ≤ (2 * found.failedRows +
        ∑ u, ∑ v, pathUse found.stack (pathAmount found.network found.stack) u v) *
          edgeQueryBound V + (2 * dead.card) * edgeQueryBound V :=
      Nat.add_le_add_right hbound _
    _ = _ := by
      change found.failedRows + dead.card = found.dead.card at hcount
      rw [← hcount]
      ring

/-- The exact directed usage mass of a returned path is its frozen distance
times the public integral bottleneck; heavy terminal arcs are included. -/
theorem augmentation_mass {H : WeightedDiGraph (Node V)} {level : Node V → ℕ}
    {s : Node V} {head : Frame V} {tail : List (Frame V)}
    (hp : StackPath H level s (head :: tail)) (amount : ℕ) :
    (∑ u, ∑ v, (pathUse (head :: tail) amount u v : ℝ)) =
      ((level head.vertex : ℝ) - level s) * amount := by
  apply Repair.phase_mass_eq _ (fun v => (level v : ℝ)) s head.vertex amount
  · intro u v huv
    have hn : pathUse (head :: tail) amount u v ≠ 0 := by exact_mod_cast huv
    exact_mod_cast pathUse_forward hp amount u v hn
  · exact hp.pathDelta_netOut amount head tail rfl

/-- Proof-only termination potential; the program uses the public N² cap. -/
def activeForward (H : WeightedDiGraph (Node V)) (level : Node V → ℕ) :
    Finset (Node V × Node V) :=
  univ.filter fun e => 0 < H.c e.1 e.2 ∧ level e.2 = level e.1 + 1

omit [DecidableEq V] in
@[simp] theorem mem_activeForward (H : WeightedDiGraph (Node V)) (level : Node V → ℕ)
    (u v : Node V) :
    (u, v) ∈ activeForward H level ↔ 0 < H.c u v ∧ level v = level u + 1 := by
  simp [activeForward]

theorem activeForward_residual_subset (H : WeightedDiGraph (Node V)) (level : Node V → ℕ)
    (g : Node V → Node V → ℕ)
    (hg : ∀ u v, g u v ≠ 0 → level v = level u + 1)
    (hf : H.Feasible (Repair.phaseDelta fun u v => (g u v : ℝ))) :
    activeForward (Repair.residual H _ hf) level ⊆ activeForward H level := by
  rintro ⟨u, v⟩ he
  obtain ⟨hpos, hlevel⟩ := (mem_activeForward _ _ _ _).mp he
  exact (mem_activeForward _ _ _ _).mpr
    ⟨hpos.trans_le (forward_residual_le H level g hg hf hlevel), hlevel⟩

/-- A whole-path bottleneck strictly decreases the number of positive
frozen-forward arcs, even when a terminal arc has arbitrarily large capacity. -/
theorem augmentation_active_lt {G : WeightedDiGraph V} {H : WeightedDiGraph (Node V)}
    {st : NetworkState V} (hr : st.Realizes G H) {level : Node V → ℕ}
    {s : Node V} {stack : List (Frame V)} (hp : StackPath H level s stack)
    (hk : StackKnown st stack) (hint : IntegralCap H)
    (hne : (stackArcs stack).Nonempty) :
    (activeForward (Repair.residual H _ (pathDelta_feasible hr hp hk)) level).card <
      (activeForward H level).card := by
  have hsub := activeForward_residual_subset H level (pathUse stack (pathAmount st stack))
    (pathUse_forward hp _) (pathDelta_feasible hr hp hk)
  obtain ⟨e, he, hz⟩ := augmentation_saturates hr hp hk hint hne
  have hold : e ∈ activeForward H level := (mem_activeForward _ _ _ _).mpr (hp.arc he)
  have hnew : e ∉ activeForward (Repair.residual H _ (pathDelta_feasible hr hp hk)) level := by
    intro hm
    have hpos := ((mem_activeForward _ _ _ _).mp hm).1
    rw [hz] at hpos
    exact (lt_irrefl 0) hpos
  apply card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
  intro heq
  exact hnew (heq.symm ▸ hold)

omit [DecidableEq V] in
theorem activeForward_card_le (H : WeightedDiGraph (Node V)) (level : Node V → ℕ) :
    (activeForward H level).card ≤ Fintype.card (Node V) ^ 2 := by
  have h := card_le_univ (activeForward H level)
  simpa only [Fintype.card_prod, pow_two] using h

/-- Public phase output. `usage` is directed and integral; its signed change
is always obtained using `Repair.phaseDelta`. -/
structure PhaseResult (V : Type) where
  network : NetworkState V
  dead : Finset (Node V)
  usage : Node V → Node V → ℕ
  value : ℕ
  blocked : Bool

def phaseEmpty (st : NetworkState V) (dead : Finset (Node V)) (blocked : Bool) :
    PhaseResult V := ⟨st, dead, fun _ _ => 0, 0, blocked⟩

def prependAugmentation (stack : List (Frame V)) (amount : ℕ) (result : PhaseResult V) :
    PhaseResult V :=
  { result with
    usage := fun u v => pathUse stack amount u v + result.usage u v
    value := amount + result.value }

/-- Operational blocking flow: complete a DFS, augment its entire returned
path by the public integral bottleneck, then repeat with the same dead set.
Invalid answer histories can stop early; a valid run never takes that exit. -/
def phaseRun (level : Node V → ℕ) (s t : Node V) :
    ℕ → NetworkState V → Finset (Node V) → Prog (Finset V) ℝ (PhaseResult V)
  | 0, st, dead => .pure (phaseEmpty st dead false)
  | fuel + 1, st, dead => (dfsProg st level dead s t).bind fun found =>
      match found.stack with
      | [] => .pure (phaseEmpty found.network found.dead true)
      | head :: _ =>
          let amount := pathAmount found.network found.stack
          if head.vertex = t ∧ s ≠ t ∧ 0 < amount then
            (phaseRun level s t fuel
              (found.network.applyFlow (pathDelta found.stack amount)) found.dead).map
                (prependAugmentation found.stack amount)
          else .pure (phaseEmpty found.network found.dead false)

def phaseProg (st : NetworkState V) (level : Node V → ℕ) (s t : Node V) :
    Prog (Finset V) ℝ (PhaseResult V) :=
  phaseRun level s t (Fintype.card (Node V) ^ 2 + 1) st ∅

/-- Every answer history has a finite public cap, independent of capacities.
The phase's sharper actual-oracle charge is proved separately from this cap. -/
theorem phaseRun_cost (read : Finset V → ℝ) (level : Node V → ℕ) (s t : Node V)
    (fuel : ℕ) (st : NetworkState V) (dead : Finset (Node V)) :
    (phaseRun level s t fuel st dead).cost read ≤
      fuel * (2 * Fintype.card (Node V) * edgeQueryBound V) := by
  induction fuel generalizing st dead with
  | zero => simp [phaseRun]
  | succ fuel ih =>
      rw [phaseRun, Prog.cost_bind]
      have hc := dfsProg_cost read st level dead s t
      cases he : (dfsProg st level dead s t).eval read with
      | mk network dead' stack failedFresh failedRows =>
          dsimp only
          cases hstack : stack with
          | nil =>
              simp only [Prog.cost_pure, Nat.add_zero]
              rw [Nat.succ_mul]
              omega
          | cons head tail =>
              dsimp only
              split_ifs
              · rw [Prog.cost_map]
                have hi := ih
                  (network.applyFlow (pathDelta (head :: tail) (pathAmount network (head :: tail)))) dead'
                rw [Nat.succ_mul]
                omega
              · simp only [Prog.cost_pure, Nat.add_zero]
                rw [Nat.succ_mul]
                omega

theorem phaseProg_cost (read : Finset V → ℝ) (st : NetworkState V)
    (level : Node V → ℕ) (s t : Node V) :
    (phaseProg st level s t).cost read ≤
      (Fintype.card (Node V) ^ 2 + 1) * (2 * Fintype.card (Node V) * edgeQueryBound V) :=
  phaseRun_cost read level s t _ st ∅

omit [Fintype V] [DecidableEq V] in
theorem network_eq_of_capacity {H K : WeightedDiGraph (Node V)}
    (h : ∀ u v, H.c u v = K.c u v) : H = K := by
  cases H with
  | mk hc hn hd =>
      cases K with
      | mk kc kn kd =>
          have he : hc = kc := by funext u v; exact h u v
          cases he
          rfl

def usageDelta (g : Node V → Node V → ℕ) : Node V → Node V → ℝ :=
  Repair.phaseDelta fun u v => (g u v : ℝ)

omit [Fintype V] [DecidableEq V] in
theorem usageDelta_add (g h : Node V → Node V → ℕ) :
    usageDelta (fun u v => g u v + h u v) = fun u v => usageDelta g u v + usageDelta h u v := by
  funext u v
  simp only [usageDelta, Repair.phaseDelta, Nat.cast_add]
  ring

omit [Fintype V] [DecidableEq V] in
theorem add_usage_feasible (H : WeightedDiGraph (Node V)) (g h : Node V → Node V → ℕ)
    (hg : H.Feasible (usageDelta g))
    (hh : (Repair.residual H _ hg).Feasible (usageDelta h)) :
    H.Feasible (usageDelta (fun u v => g u v + h u v)) := by
  refine ⟨Repair.phaseDelta_isFlow _, ?_⟩
  intro u v
  rw [usageDelta_add]
  have hh' := hh.2 u v
  rw [Repair.residual_c] at hh'
  dsimp
  linarith

omit [Fintype V] [DecidableEq V] in
theorem residual_add_usage (H : WeightedDiGraph (Node V)) (g h : Node V → Node V → ℕ)
    (hg : H.Feasible (usageDelta g))
    (hh : (Repair.residual H _ hg).Feasible (usageDelta h)) :
    Repair.residual (Repair.residual H _ hg) _ hh =
      Repair.residual H _ (add_usage_feasible H g h hg hh) := by
  apply network_eq_of_capacity
  intro u v
  simp only [Repair.residual_c, usageDelta_add]
  ring

/-- Correctness of the actual phase output, including a constructed blocking
endpoint. There is no assumed blocking-flow oracle or assumed phase outcome. -/
structure PhaseCorrect (G : WeightedDiGraph V) (H : WeightedDiGraph (Node V))
    (level : Node V → ℕ) (s t : Node V) (result : PhaseResult V) : Prop where
  feasible : H.Feasible (usageDelta result.usage)
  realizes : result.network.Realizes G (Repair.residual H _ feasible)
  forward : ∀ u v, result.usage u v ≠ 0 → level v = level u + 1
  divergence : ∀ x, netOut (usageDelta result.usage) x =
    (if x = s then (result.value : ℝ) else 0) - (if x = t then (result.value : ℝ) else 0)
  closed : DeadClosed (Repair.residual H _ feasible) level t result.dead
  finished : result.blocked = true
  blocks : ∀ d, ¬LevelPath (Repair.residual H _ feasible) level s t d

theorem phaseEmpty_correct (G : WeightedDiGraph V) (H : WeightedDiGraph (Node V))
    (level : Node V → ℕ) (s t : Node V) (st : NetworkState V) (dead : Finset (Node V))
    (hr : st.Realizes G H) (hd : DeadClosed H level t dead)
    (hb : ∀ d, ¬LevelPath H level s t d) :
    PhaseCorrect G H level s t (phaseEmpty st dead true) := by
  have hf : H.Feasible (usageDelta (fun _ _ => 0)) := by
    refine ⟨Repair.phaseDelta_isFlow _, ?_⟩
    intro u v
    simpa [usageDelta, Repair.phaseDelta] using H.nonneg u v
  have he : Repair.residual H _ hf = H := by
    apply network_eq_of_capacity
    intro u v
    simp [Repair.residual_c, usageDelta, Repair.phaseDelta]
  refine ⟨hf, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · change st.Realizes G (Repair.residual H _ hf)
    rw [he]
    exact hr
  · intro u v hn
    exact False.elim (hn rfl)
  · intro x
    simp [phaseEmpty, usageDelta, Repair.phaseDelta, netOut]
  · change DeadClosed (Repair.residual H _ hf) level t dead
    rw [he]
    exact hd
  · change ∀ d, ¬LevelPath (Repair.residual H _ hf) level s t d
    rw [he]
    exact hb

theorem phaseCorrect_prepend (G : WeightedDiGraph V) (H : WeightedDiGraph (Node V))
    (level : Node V → ℕ) (s t : Node V) (st : NetworkState V) (hr : st.Realizes G H)
    {head : Frame V} {tail : List (Frame V)} (hp : StackPath H level s (head :: tail))
    (hk : StackKnown st (head :: tail)) (ht : head.vertex = t) (result : PhaseResult V)
    (hc : PhaseCorrect G (Repair.residual H _ (pathDelta_feasible hr hp hk)) level s t result) :
    PhaseCorrect G H level s t
      (prependAugmentation (head :: tail) (pathAmount st (head :: tail)) result) := by
  let g := pathUse (head :: tail) (pathAmount st (head :: tail))
  have hg : H.Feasible (usageDelta g) := pathDelta_feasible hr hp hk
  have hf := add_usage_feasible H g result.usage hg hc.feasible
  have he := residual_add_usage H g result.usage hg hc.feasible
  refine ⟨hf, ?_, ?_, ?_, ?_, hc.finished, ?_⟩
  · change result.network.Realizes G (Repair.residual H _ hf)
    rw [← he]
    exact hc.realizes
  · intro u v huv
    change g u v + result.usage u v ≠ 0 at huv
    by_cases hguv : g u v = 0
    · exact hc.forward u v (by simpa [hguv] using huv)
    · exact pathUse_forward hp _ u v hguv
  · intro x
    change netOut (usageDelta (fun u v => g u v + result.usage u v)) x = _
    rw [usageDelta_add]
    simp only [netOut, sum_add_distrib]
    change netOut (pathDelta (head :: tail) (pathAmount st (head :: tail))) x +
      netOut (usageDelta result.usage) x = _
    rw [hp.pathDelta_netOut _ head tail rfl x, hc.divergence, ht]
    simp only [prependAugmentation, Nat.cast_add]
    split_ifs <;> ring
  · change DeadClosed (Repair.residual H _ hf) level t result.dead
    rw [← he]
    exact hc.closed
  · change ∀ d, ¬LevelPath (Repair.residual H _ hf) level s t d
    rw [← he]
    exact hc.blocks

/-- The operational loop, run for more than the current number of positive
forward arcs, returns a feasible integral blocking flow and its exact state. -/
theorem phaseRun_complete (G : WeightedDiGraph V) (H : WeightedDiGraph (Node V))
    (level : Node V → ℕ) (s t : Node V) (hst : s ≠ t) (fuel : ℕ)
    (st : NetworkState V) (dead : Finset (Node V)) (hr : st.Realizes G H)
    (hint : IntegralCap H) (hd : DeadClosed H level t dead)
    (hfuel : (activeForward H level).card < fuel) :
    PhaseCorrect G H level s t ((phaseRun level s t fuel st dead).eval G.out) := by
  induction fuel generalizing H st dead with
  | zero => omega
  | succ fuel ih =>
      rw [phaseRun, Prog.eval_bind]
      have hs := dfsProg_complete G H st hr level dead s t hd
      cases he : (dfsProg st level dead s t).eval G.out with
      | mk network dead' stack failedFresh failedRows =>
          rw [he] at hs
          cases hstack : stack with
          | nil =>
              apply phaseEmpty_correct G H level s t network dead' hs.1 hs.2.1.closed
              intro d path
              exact hs.2.1.closed.1 (path.dead hs.2.1.closed
                (hs.2.1.exhausted hstack))
          | cons head tail =>
              have hp : StackPath H level s (head :: tail) := by
                rcases hs.2.1.path with hn | hp
                · simp [hstack] at hn
                · simpa only [hstack] using hp
              have ht : head.vertex = t := by
                rcases hs.2.2 with hn | ⟨top, rest, htop, ht⟩
                · simp [hstack] at hn
                · rw [hstack] at htop
                  cases htop
                  exact ht
              have hk : StackKnown network (head :: tail) := by
                simpa only [hstack] using hs.2.1.learned
              have hne := hp.arcs_nonempty_of_head_ne (by rw [ht]; exact Ne.symm hst)
              have hpos := pathAmount_pos hs.1 hp hk hint hne
              dsimp only
              rw [ite_eq_left ⟨ht, hst, hpos⟩, Prog.eval_map]
              have hfeasible := pathDelta_feasible hs.1 hp hk
              have hrealizes := augment_realizes hs.1 hp hk
              have hintegral := integralCap_residual hint
                (pathUse (head :: tail) (pathAmount network (head :: tail))) hfeasible
              have hclosed := deadClosed_residual hs.2.1.closed
                (pathUse (head :: tail) (pathAmount network (head :: tail)))
                (pathUse_forward hp _) hfeasible
              have hlt := augmentation_active_lt hs.1 hp hk hint hne
              have hrec := ih (Repair.residual H _ hfeasible)
                (network.applyFlow (pathDelta (head :: tail) (pathAmount network (head :: tail))))
                dead' hrealizes hintegral hclosed (by omega)
              exact phaseCorrect_prepend G H level s t network hs.1 hp hk ht _ hrec

theorem phaseProg_complete (G : WeightedDiGraph V) (H : WeightedDiGraph (Node V))
    (st : NetworkState V) (hr : st.Realizes G H) (hint : IntegralCap H)
    (level : Node V → ℕ) (s t : Node V) (hst : s ≠ t) :
    PhaseCorrect G H level s t ((phaseProg st level s t).eval G.out) := by
  apply phaseRun_complete G H level s t hst _ st ∅ hr hint
  · exact ⟨notMem_empty t, fun _ h => False.elim (notMem_empty _ h)⟩
  · exact Nat.lt_succ_of_le (activeForward_card_le H level)

def usageMass (g : Node V → Node V → ℕ) : ℕ := ∑ u, ∑ v, g u v

/-- Exhausted-row charges telescope through the persistent dead set; every
other paid discovery is charged to the next completed-path augmentation. -/
theorem phaseRun_cost_mass (G : WeightedDiGraph V) (H : WeightedDiGraph (Node V))
    (level : Node V → ℕ) (s t : Node V) (hst : s ≠ t) (fuel : ℕ)
    (st : NetworkState V) (dead : Finset (Node V)) (hr : st.Realizes G H)
    (hint : IntegralCap H) (hd : DeadClosed H level t dead) :
    let result := (phaseRun level s t fuel st dead).eval G.out
    (phaseRun level s t fuel st dead).cost G.out + (2 * dead.card) * edgeQueryBound V ≤
      (2 * result.dead.card + usageMass result.usage) * edgeQueryBound V := by
  induction fuel generalizing H st dead with
  | zero => simp [phaseRun, phaseEmpty, usageMass]
  | succ fuel ih =>
      rw [phaseRun, Prog.cost_bind, Prog.eval_bind]
      have hs := dfsProg_complete G H st hr level dead s t hd
      have hcost := dfsProg_cost_augmentation G H st hr hint level dead s t hd
      cases he : (dfsProg st level dead s t).eval G.out with
      | mk network dead' stack failedFresh failedRows =>
          rw [he] at hs hcost
          cases hstack : stack with
          | nil =>
              simpa [phaseEmpty, usageMass, hstack, pathUse, stackArcs] using hcost
          | cons head tail =>
              have hp : StackPath H level s (head :: tail) := by
                rcases hs.2.1.path with hn | hp
                · simp [hstack] at hn
                · simpa only [hstack] using hp
              have ht : head.vertex = t := by
                rcases hs.2.2 with hn | ⟨top, rest, htop, ht⟩
                · simp [hstack] at hn
                · rw [hstack] at htop
                  cases htop
                  exact ht
              have hk : StackKnown network (head :: tail) := by
                simpa only [hstack] using hs.2.1.learned
              have hne := hp.arcs_nonempty_of_head_ne (by rw [ht]; exact Ne.symm hst)
              have hpos := pathAmount_pos hs.1 hp hk hint hne
              simp only [hstack] at hcost ⊢
              rw [ite_eq_left ⟨ht, hst, hpos⟩, Prog.cost_map, Prog.eval_map]
              have hfeasible := pathDelta_feasible hs.1 hp hk
              have hrealizes := augment_realizes hs.1 hp hk
              have hintegral := integralCap_residual hint
                (pathUse (head :: tail) (pathAmount network (head :: tail))) hfeasible
              have hclosed := deadClosed_residual hs.2.1.closed
                (pathUse (head :: tail) (pathAmount network (head :: tail)))
                (pathUse_forward hp _) hfeasible
              have hrec := ih (Repair.residual H _ hfeasible)
                (network.applyFlow (pathDelta (head :: tail) (pathAmount network (head :: tail))))
                dead' hrealizes hintegral hclosed
              simp only [prependAugmentation, usageMass, sum_add_distrib,
                Nat.add_mul] at hrec hcost ⊢
              omega

/-- The actual phase cost is O((N + directed usage mass) log n). -/
theorem phaseProg_cost_mass (G : WeightedDiGraph V) (H : WeightedDiGraph (Node V))
    (st : NetworkState V) (hr : st.Realizes G H) (hint : IntegralCap H)
    (level : Node V → ℕ) (s t : Node V) (hst : s ≠ t) :
    let result := (phaseProg st level s t).eval G.out
    (phaseProg st level s t).cost G.out ≤
      (2 * Fintype.card (Node V) + usageMass result.usage) * edgeQueryBound V := by
  have h := phaseRun_cost_mass G H level s t hst (Fintype.card (Node V) ^ 2 + 1)
    st ∅ hr hint ⟨notMem_empty t, fun _ h => False.elim (notMem_empty _ h)⟩
  simp only [card_empty, Nat.mul_zero, Nat.zero_mul, Nat.add_zero] at h
  apply h.trans
  apply Nat.mul_le_mul_right
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (card_le_univ _)) _

theorem PhaseCorrect.mass {G : WeightedDiGraph V} {H : WeightedDiGraph (Node V)}
    {level : Node V → ℕ} {s t : Node V} {result : PhaseResult V}
    (hc : PhaseCorrect G H level s t result) :
    (usageMass result.usage : ℝ) = ((level t : ℝ) - level s) * result.value := by
  have h := Repair.phase_mass_eq (fun u v => (result.usage u v : ℝ))
    (fun v => (level v : ℝ)) s t (result.value : ℝ)
    (fun u v hn => by
      have hnu : result.usage u v ≠ 0 := by exact_mod_cast hn
      exact_mod_cast hc.forward u v hnu) hc.divergence
  simpa only [usageMass, Nat.cast_sum] using h

/-- The completed program pays the exact d*r successful-discovery charge,
plus at most two charges for each dead destination. -/
theorem phaseProg_cost_distance_value (G : WeightedDiGraph V)
    (H : WeightedDiGraph (Node V)) (st : NetworkState V) (hr : st.Realizes G H)
    (hint : IntegralCap H) (level : Node V → ℕ) (s t : Node V) (hst : s ≠ t) :
    let result := (phaseProg st level s t).eval G.out
    ((phaseProg st level s t).cost G.out : ℝ) ≤
      (2 * (Fintype.card (Node V) : ℝ) +
        ((level t : ℝ) - level s) * result.value) * edgeQueryBound V := by
  have h := phaseProg_cost_mass G H st hr hint level s t hst
  have hm := (phaseProg_complete G H st hr hint level s t hst).mass
  have hcast : ((phaseProg st level s t).cost G.out : ℝ) ≤
      (2 * (Fintype.card (Node V) : ℝ) +
        (usageMass ((phaseProg st level s t).eval G.out).usage : ℝ)) * edgeQueryBound V := by
    exact_mod_cast h
  rwa [hm] at hcast

end
end CutQueryComplexity.DirectedUnitST.Blocking

#print axioms CutQueryComplexity.DirectedUnitST.Blocking.pathDelta_feasible
#print axioms CutQueryComplexity.DirectedUnitST.Blocking.augment_realizes
#print axioms CutQueryComplexity.DirectedUnitST.Blocking.augmentation_saturates
#print axioms CutQueryComplexity.DirectedUnitST.Blocking.integralCap_residual
#print axioms CutQueryComplexity.DirectedUnitST.Blocking.deadClosed_residual
#print axioms CutQueryComplexity.DirectedUnitST.Blocking.phaseProg_complete
#print axioms CutQueryComplexity.DirectedUnitST.Blocking.phaseProg_cost
#print axioms CutQueryComplexity.DirectedUnitST.Blocking.phaseProg_cost_distance_value
