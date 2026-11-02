import CutQueryComplexity.DirectedUnitST.Blocking.Phase

/-!
# Increasing residual distances and operational terminal flow iteration

The solve program alternates its actual queue BFS with its actual integral
blocking phase. It returns the shore discovered by the last BFS. All data
choices are from the public state and outgoing-cut answers.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DirectedUnitST.Blocking

open Finset DirectedCertificate Certificate Prog
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem PathAt.level_le_add {H : WeightedDiGraph (Node V)} {s v : Node V} {d : ℕ}
    (path : PathAt H s v d) (level : Node V → ℕ)
    (hstep : ∀ u v, 0 < H.c u v → level v ≤ level u + 1) : level v ≤ level s + d := by
  induction path with
  | nil => omega
  | @snoc u v d hp he ih =>
      have hr := hstep u v he
      omega

omit [Fintype V] [DecidableEq V] in
/-- A residual walk attaining the old distance is entirely frozen-forward. -/
theorem PathAt.tight {H : WeightedDiGraph (Node V)} {s v : Node V} {d : ℕ}
    (path : PathAt H s v d) (level : Node V → ℕ)
    (hstep : ∀ u v, 0 < H.c u v → level v ≤ level u + 1)
    (heq : level v = level s + d) : LevelPath H level s v d := by
  induction path with
  | nil => exact LevelPath.nil
  | @snoc u v d hp he ih =>
      have hprev := hp.level_le_add level hstep
      have hlast := hstep u v he
      have hprefix : level u = level s + d := by omega
      have hforward : level v = level u + 1 := by omega
      exact LevelPath.snoc (ih hprefix) he hforward

theorem PhaseCorrect.residual_rise {G : WeightedDiGraph V} {H : WeightedDiGraph (Node V)}
    {level : Node V → ℕ} {s t : Node V} {result : PhaseResult V}
    (hc : PhaseCorrect G H level s t result)
    (hrise : ∀ u v, 0 < H.c u v → level v ≤ level u + 1) :
    ∀ u v, 0 < (Repair.residual H _ hc.feasible).c u v → level v ≤ level u + 1 := by
  intro u v hpos
  have hriseR : ∀ u v, 0 < H.c u v → (level v : ℝ) ≤ level u + 1 := by
    intro a b hp
    exact_mod_cast hrise a b hp
  have hforward : ∀ u v, 0 < usageDelta result.usage u v →
      (level v : ℝ) = level u + 1 := by
    intro a b hp
    apply Repair.phaseDelta_pos_forward (fun u v => (result.usage u v : ℝ))
      (fun v => (level v : ℝ)) (fun _ _ => Nat.cast_nonneg _) _ hp
    intro x y hn
    have hnu : result.usage x y ≠ 0 := by exact_mod_cast hn
    exact_mod_cast hc.forward x y hnu
  have h := Repair.residual_level_rise H (fun v => (level v : ℝ)) hriseR
    (usageDelta result.usage) hc.feasible hforward u v hpos
  exact_mod_cast h

/-- The constructed blocking endpoint makes every later residual s-to-t
distance strictly larger than the frozen BFS distance. -/
theorem PhaseCorrect.distance_strict {G : WeightedDiGraph V} {H : WeightedDiGraph (Node V)}
    {level : Node V → ℕ} {s t : Node V} {result : PhaseResult V}
    (hc : PhaseCorrect G H level s t result) (hs : level s = 0)
    (hrise : ∀ u v, 0 < H.c u v → level v ≤ level u + 1)
    {d : ℕ} (path : PathAt (Repair.residual H _ hc.feasible) s t d) : level t < d := by
  have hsteps := hc.residual_rise hrise
  have hle := path.level_le level hs hsteps
  by_contra hn
  have heq : level t = level s + d := by omega
  exact hc.blocks d (path.tight level hsteps heq)

omit [DecidableEq V] in
theorem usage_le_mass (g : Node V → Node V → ℕ) (u v : Node V) : g u v ≤ usageMass g := by
  have hrow : g u v ≤ ∑ w, g u w :=
    single_le_sum (fun w _ => Nat.zero_le (g u w)) (mem_univ v)
  have hrows : (∑ w, g u w) ≤ ∑ x, ∑ w, g x w :=
    single_le_sum (fun x _ => Nat.zero_le (∑ w, g x w)) (mem_univ u)
  exact hrow.trans hrows

/-- A blocking phase with an initially reachable target sends at least one
unit. This follows from its constructed endpoint and integral directed mass. -/
theorem PhaseCorrect.value_pos {G : WeightedDiGraph V} {H : WeightedDiGraph (Node V)}
    {level : Node V → ℕ} {s t : Node V} {result : PhaseResult V}
    (hc : PhaseCorrect G H level s t result) (hs : level s = 0)
    (hrise : ∀ u v, 0 < H.c u v → level v ≤ level u + 1)
    (path : PathAt H s t (level t)) : 0 < result.value := by
  by_contra hn
  have hvalue : result.value = 0 := by omega
  have hm := hc.mass
  rw [hvalue, Nat.cast_zero, mul_zero] at hm
  have hmass : usageMass result.usage = 0 := by exact_mod_cast hm
  have hzero (u v : Node V) : result.usage u v = 0 := by
    have h := usage_le_mass result.usage u v
    rw [hmass] at h
    omega
  have he : Repair.residual H _ hc.feasible = H := by
    apply network_eq_of_capacity
    intro u v
    simp only [Repair.residual_c, usageDelta, Repair.phaseDelta, hzero,
      Nat.cast_zero, sub_self, sub_zero]
  have hb := hc.blocks (level t)
  rw [he] at hb
  exact hb (path.tight level hrise (by omega))

structure PhaseEvent where
  distance : ℕ
  amount : ℕ

structure SolveResult (V : Type) where
  network : NetworkState V
  flow : Node V → Node V → ℝ
  value : ℕ
  shore : Finset (Node V)
  phases : List PhaseEvent
  finished : Bool

def solveEmpty (st : NetworkState V) (shore : Finset (Node V)) (finished : Bool) :
    SolveResult V := ⟨st, fun _ _ => 0, 0, shore, [], finished⟩

def prependPhase (phase : PhaseResult V) (distance : ℕ) (result : SolveResult V) :
    SolveResult V :=
  { result with
    flow := fun u v => usageDelta phase.usage u v + result.flow u v
    value := phase.value + result.value
    phases := ⟨distance, phase.value⟩ :: result.phases }

/-- Terminal flow solve with a public phase counter. The BFS in the zero
counter branch is still performed, so the valid last shore is returned. -/
def solveRun (s t : Node V) : ℕ → NetworkState V → Prog (Finset V) ℝ (SolveResult V)
  | fuel, st => (bfsProg st s).bind fun bfs =>
      if t ∈ bfs.unseen then .pure (solveEmpty bfs.network bfs.unseenᶜ true)
      else match fuel with
        | 0 => .pure (solveEmpty bfs.network bfs.unseenᶜ false)
        | fuel + 1 => (phaseProg bfs.network (bfsLevel bfs) s t).bind fun phase =>
            (solveRun s t fuel phase.network).map (prependPhase phase (bfsLevel bfs t))
termination_by fuel _ => fuel

def solveProg (st : NetworkState V) (s t : Node V) :
    Prog (Finset V) ℝ (SolveResult V) := solveRun s t (Fintype.card (Node V)) st

def bfsBudget (V : Type) [Fintype V] : ℕ := 2 * Fintype.card (Node V) * edgeQueryBound V
def phaseBudget (V : Type) [Fintype V] : ℕ := (Fintype.card (Node V) ^ 2 + 1) * bfsBudget V

/-- A capacity-independent cap for every answer history. The sharp repair
budget is obtained by separately bounding the actual recorded phase costs. -/
theorem solveRun_cost (read : Finset V → ℝ) (s t : Node V) (fuel : ℕ) (st : NetworkState V) :
    (solveRun s t fuel st).cost read ≤ (fuel + 1) * bfsBudget V + fuel * phaseBudget V := by
  induction fuel generalizing st with
  | zero =>
      rw [solveRun, Prog.cost_bind]
      have h := bfsProg_cost read st s
      split_ifs <;> simpa [bfsBudget] using h
  | succ fuel ih =>
      rw [solveRun, Prog.cost_bind]
      have hb := bfsProg_cost read st s
      split_ifs
      · simp only [Prog.cost_pure, Nat.add_zero]
        unfold bfsBudget at *
        nlinarith
      · rw [Prog.cost_bind, Prog.cost_map]
        have hp := phaseProg_cost read ((bfsProg st s).eval read).network
          (bfsLevel ((bfsProg st s).eval read)) s t
        have hi := ih ((phaseProg ((bfsProg st s).eval read).network
          (bfsLevel ((bfsProg st s).eval read)) s t).eval read).network
        change _ ≤ (fuel + 1 + 1) * bfsBudget V + (fuel + 1) * phaseBudget V
        change _ ≤ bfsBudget V at hb
        change _ ≤ phaseBudget V at hp
        simp only [Nat.add_mul, Nat.one_mul] at hi ⊢
        omega

theorem solveProg_cost (read : Finset V → ℝ) (st : NetworkState V) (s t : Node V) :
    (solveProg st s t).cost read ≤
      (Fintype.card (Node V) + 1) * bfsBudget V + Fintype.card (Node V) * phaseBudget V :=
  solveRun_cost read s t _ st

omit [Fintype V] [DecidableEq V] in
theorem feasible_add_flow (H : WeightedDiGraph (Node V)) (f g : Node V → Node V → ℝ)
    (hf : H.Feasible f) (hg : (Repair.residual H f hf).Feasible g) :
    H.Feasible (fun u v => f u v + g u v) := by
  refine ⟨?_, ?_⟩
  · intro u v
    dsimp only
    rw [hf.1 u v, hg.1 u v]
    ring
  · intro u v
    have h := hg.2 u v
    rw [Repair.residual_c] at h
    linarith

omit [Fintype V] [DecidableEq V] in
theorem residual_add_flow (H : WeightedDiGraph (Node V)) (f g : Node V → Node V → ℝ)
    (hf : H.Feasible f) (hg : (Repair.residual H f hf).Feasible g) :
    Repair.residual (Repair.residual H f hf) g hg =
      Repair.residual H _ (feasible_add_flow H f g hf hg) := by
  apply network_eq_of_capacity
  intro u v
  simp only [Repair.residual_c]
  ring

theorem residual_out (H : WeightedDiGraph (Node V)) (f : Node V → Node V → ℝ)
    (hf : H.Feasible f) (S : Finset (Node V)) :
    (Repair.residual H f hf).out S = H.out S - ∑ u ∈ S, netOut f u := by
  rw [sum_netOut_eq hf.1]
  simp only [WeightedDiGraph.out, Repair.residual_c, sum_sub_distrib]

/-- An actual feasible terminal flow, together with the last BFS's residual
zero cut. Equality of value and original augmented cut follows from these. -/
structure SolveCorrect (G : WeightedDiGraph V) (H : WeightedDiGraph (Node V))
    (s t : Node V) (result : SolveResult V) : Prop where
  feasible : H.Feasible result.flow
  realizes : result.network.Realizes G (Repair.residual H _ feasible)
  divergence : ∀ x, netOut result.flow x =
    (if x = s then (result.value : ℝ) else 0) - (if x = t then (result.value : ℝ) else 0)
  source_mem : s ∈ result.shore
  target_notMem : t ∉ result.shore
  residual_zero : (Repair.residual H _ feasible).out result.shore = 0
  finished : result.finished = true

theorem SolveCorrect.value_eq_cut {G : WeightedDiGraph V} {H : WeightedDiGraph (Node V)}
    {s t : Node V} {result : SolveResult V} (hc : SolveCorrect G H s t result) :
    (result.value : ℝ) = H.out result.shore := by
  have hsum : ∑ u ∈ result.shore, netOut result.flow u = result.value := by
    simp only [hc.divergence, sum_sub_distrib, sum_ite_eq', hc.source_mem,
      hc.target_notMem, ↓reduceIte, sub_zero]
  have hz := hc.residual_zero
  rw [residual_out, hsum] at hz
  linarith

theorem SolveCorrect.min_cut {G : WeightedDiGraph V} {H : WeightedDiGraph (Node V)}
    {s t : Node V} {result : SolveResult V} (hc : SolveCorrect G H s t result)
    (S : Finset (Node V)) (hs : s ∈ S) (ht : t ∉ S) : H.out result.shore ≤ H.out S := by
  have hst : s ≠ t := fun he => ht (he ▸ hs)
  have hflow : H.STFlow s t result.flow := by
    refine ⟨hc.feasible, ?_⟩
    intro x hxs hxt
    simp [hc.divergence, hxs, hxt]
  have h := WeightedDiGraph.netOut_le_out hflow hs ht
  rw [hc.divergence] at h
  simp only [↓reduceIte, hst, sub_zero] at h
  rwa [hc.value_eq_cut] at h

theorem solveEmpty_correct (G : WeightedDiGraph V) (H : WeightedDiGraph (Node V))
    (st : NetworkState V) (hr : st.Realizes G H) (s t : Node V) (S : Finset (Node V))
    (hs : s ∈ S) (ht : t ∉ S) (hz : H.out S = 0) :
    SolveCorrect G H s t (solveEmpty st S true) := by
  have hf : H.Feasible (fun _ _ => 0) :=
    ⟨fun _ _ => by simp, fun u v => H.nonneg u v⟩
  have he : Repair.residual H _ hf = H := by
    apply network_eq_of_capacity
    intro u v
    simp only [Repair.residual_c, sub_zero]
  refine ⟨hf, ?_, ?_, hs, ht, ?_, rfl⟩
  · change st.Realizes G (Repair.residual H _ hf)
    rw [he]
    exact hr
  · intro x
    simp [solveEmpty, netOut]
  · change (Repair.residual H _ hf).out S = 0
    rw [he]
    exact hz

theorem solveCorrect_prepend (G : WeightedDiGraph V) (H : WeightedDiGraph (Node V))
    (level : Node V → ℕ) (s t : Node V) (phase : PhaseResult V)
    (hp : PhaseCorrect G H level s t phase) (result : SolveResult V)
    (hr : SolveCorrect G (Repair.residual H _ hp.feasible) s t result) :
    SolveCorrect G H s t (prependPhase phase (level t) result) := by
  have hf := feasible_add_flow H (usageDelta phase.usage) result.flow hp.feasible hr.feasible
  have he := residual_add_flow H (usageDelta phase.usage) result.flow hp.feasible hr.feasible
  refine ⟨hf, ?_, ?_, hr.source_mem, hr.target_notMem, ?_, hr.finished⟩
  · change result.network.Realizes G (Repair.residual H _ hf)
    rw [← he]
    exact hr.realizes
  · intro x
    change netOut (fun u v => usageDelta phase.usage u v + result.flow u v) x = _
    simp only [netOut, sum_add_distrib]
    change netOut (usageDelta phase.usage) x + netOut result.flow x = _
    rw [hp.divergence, hr.divergence]
    simp only [prependPhase, Nat.cast_add]
    split_ifs <;> ring
  · change (Repair.residual H _ hf).out result.shore = 0
    rw [← he]
    exact hr.residual_zero

theorem bfsProg_facts (G : WeightedDiGraph V) (H : WeightedDiGraph (Node V))
    (st : NetworkState V) (hr : st.Realizes G H) (s : Node V) :
    let bfs := (bfsProg st s).eval G.out
    bfs.network.Realizes G H ∧ bfsLevel bfs s = 0 ∧
      (∀ u v, 0 < H.c u v → bfsLevel bfs v ≤ bfsLevel bfs u + 1) ∧
      s ∈ bfs.unseenᶜ ∧ H.out bfs.unseenᶜ = 0 ∧
      (∀ v, v ∉ bfs.unseen →
        PathAt H s v (bfsLevel bfs v) ∧ bfsLevel bfs v < Fintype.card (Node V)) := by
  have hc := bfsProg_complete G H st hr s
  have hl := bfsProg_level_rise G H st hr s
  have hi := bfsRun_invariant G H s (2 * Fintype.card (Node V))
    (initialBFS st s) hr (initialBFS_invariant H st s)
  change BFSInvariant H s ((bfsProg st s).eval G.out) at hi
  refine ⟨hc.1, hl.1, hl.2.1, mem_compl.mpr hi.source_seen,
    bfsProg_out_zero G H st hr s, ?_⟩
  intro v hv
  refine ⟨hl.2.2 v hv, ?_⟩
  rw [bfsLevel, ite_eq_right hv]
  have hb := hi.level_bound v hv
  omega

/-- Once the public remaining phase counter covers the remaining possible
distance increases, the actual terminal solve returns a min-cut witness. -/
theorem solveRun_complete (G : WeightedDiGraph V) (H : WeightedDiGraph (Node V))
    (s t : Node V) (hst : s ≠ t) (fuel : ℕ) (st : NetworkState V)
    (hr : st.Realizes G H) (hint : IntegralCap H) (lower : ℕ)
    (hlower : ∀ d, PathAt H s t d → lower ≤ d)
    (hfuel : Fintype.card (Node V) ≤ fuel + lower) :
    SolveCorrect G H s t ((solveRun s t fuel st).eval G.out) := by
  induction fuel generalizing H st lower with
  | zero =>
      rw [solveRun, Prog.eval_bind]
      obtain ⟨hreal, hsource, hrise, hsourceMem, hout, hpath⟩ := bfsProg_facts G H st hr s
      split_ifs with ht
      · exact solveEmpty_correct G H _ hreal s t _ hsourceMem
          (by simpa only [mem_compl, not_not] using ht) hout
      · obtain ⟨hp, hd⟩ := hpath t ht
        have hlow := hlower _ hp
        omega
  | succ fuel ih =>
      rw [solveRun, Prog.eval_bind]
      obtain ⟨hreal, hsource, hrise, hsourceMem, hout, hpath⟩ := bfsProg_facts G H st hr s
      split_ifs with ht
      · exact solveEmpty_correct G H _ hreal s t _ hsourceMem
          (by simpa only [mem_compl, not_not] using ht) hout
      · rw [Prog.eval_bind, Prog.eval_map]
        let bfs := (bfsProg st s).eval G.out
        let phase := (phaseProg bfs.network (bfsLevel bfs) s t).eval G.out
        have hp : PhaseCorrect G H (bfsLevel bfs) s t phase :=
          phaseProg_complete G H bfs.network hreal hint (bfsLevel bfs) s t hst
        have hint' := integralCap_residual hint phase.usage hp.feasible
        have hlow := hlower _ (hpath t ht).1
        change lower ≤ bfsLevel bfs t at hlow
        have hrec := ih (Repair.residual H _ hp.feasible) phase.network hp.realizes hint'
          (bfsLevel bfs t + 1)
          (fun d path => Nat.succ_le_of_lt (hp.distance_strict hsource hrise path)) (by omega)
        exact solveCorrect_prepend G H (bfsLevel bfs) s t phase hp _ hrec

theorem solveProg_complete (G : WeightedDiGraph V) (H : WeightedDiGraph (Node V))
    (st : NetworkState V) (hr : st.Realizes G H) (hint : IntegralCap H)
    (s t : Node V) (hst : s ≠ t) :
    SolveCorrect G H s t ((solveProg st s t).eval G.out) :=
  solveRun_complete G H s t hst _ st hr hint 0 (fun _ _ => Nat.zero_le _) (by omega)

/-- The program's actual final shore is minimum and its actual public
integral flow value equals that cut. -/
theorem solveProg_min_cut (G : WeightedDiGraph V) (H : WeightedDiGraph (Node V))
    (st : NetworkState V) (hr : st.Realizes G H) (hint : IntegralCap H)
    (s t : Node V) (hst : s ≠ t) :
    let result := (solveProg st s t).eval G.out
    result.finished = true ∧ s ∈ result.shore ∧ t ∉ result.shore ∧
      (result.value : ℝ) = H.out result.shore ∧
      ∀ S : Finset (Node V), s ∈ S → t ∉ S → H.out result.shore ≤ H.out S := by
  have hc := solveProg_complete G H st hr hint s t hst
  exact ⟨hc.finished, hc.source_mem, hc.target_notMem, hc.value_eq_cut, hc.min_cut⟩


/-- Even inconsistent oracle histories can only add signed integral usages. -/
theorem solveRun_flow_integer (read : Finset V → ℝ) (s t : Node V)
    (fuel : ℕ) (st : NetworkState V) :
    ∀ u v, ∃ z : ℤ, ((solveRun s t fuel st).eval read).flow u v = z := by
  induction fuel generalizing st with
  | zero =>
      rw [solveRun, Prog.eval_bind]
      split_ifs <;> intro u v <;> refine ⟨0, ?_⟩ <;> simp [solveEmpty]
  | succ fuel ih =>
      rw [solveRun, Prog.eval_bind]
      split_ifs
      · intro u v
        refine ⟨0, ?_⟩
        simp [solveEmpty]
      · rw [Prog.eval_bind, Prog.eval_map]
        intro u v
        let phase := (phaseProg ((bfsProg st s).eval read).network
          (bfsLevel ((bfsProg st s).eval read)) s t).eval read
        obtain ⟨z, hz⟩ := ih phase.network u v
        refine ⟨(phase.usage u v : ℤ) - phase.usage v u + z, ?_⟩
        change usageDelta phase.usage u v + ((solveRun s t fuel phase.network).eval read).flow u v = _
        rw [hz]
        simp [usageDelta, Repair.phaseDelta]

omit [Fintype V] [DecidableEq V] in
/-- A feasible signed integral update preserves nonnegative integral residuals. -/
theorem integralCap_residual_flow {H : WeightedDiGraph (Node V)} (hint : IntegralCap H)
    (f : Node V → Node V → ℝ) (hf : H.Feasible f)
    (hinteger : ∀ u v, ∃ z : ℤ, f u v = z) : IntegralCap (Repair.residual H f hf) := by
  intro u v
  obtain ⟨k, hk⟩ := hint u v
  obtain ⟨z, hz⟩ := hinteger u v
  cases z with
  | ofNat m =>
      have hleR : (m : ℝ) ≤ k := by
        simpa only [hz, hk, Int.ofNat_eq_natCast, Int.cast_natCast] using hf.2 u v
      have hle : m ≤ k := by exact_mod_cast hleR
      refine ⟨k - m, ?_⟩
      rw [Repair.residual_c, hk, hz, Int.ofNat_eq_natCast, Int.cast_natCast, Nat.cast_sub hle]
  | negSucc m =>
      refine ⟨k + (m + 1), ?_⟩
      simp only [Repair.residual_c, hk, hz, Int.cast_negSucc, Nat.cast_add, Nat.cast_one]
      ring

end
end CutQueryComplexity.DirectedUnitST.Blocking

#print axioms CutQueryComplexity.DirectedUnitST.Blocking.PhaseCorrect.distance_strict
#print axioms CutQueryComplexity.DirectedUnitST.Blocking.solveProg_cost
#print axioms CutQueryComplexity.DirectedUnitST.Blocking.solveProg_complete
#print axioms CutQueryComplexity.DirectedUnitST.Blocking.solveProg_min_cut

#print axioms CutQueryComplexity.DirectedUnitST.Blocking.solveRun_flow_integer
