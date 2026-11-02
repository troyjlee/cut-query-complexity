import CutQueryComplexity.DirectedUnitST.Repair.Basic

/-! # Exact level-graph phase mass

`phaseUse` is directed nonnegative arc usage, while `phaseDelta phaseUse` is
its antisymmetric update to an older signed flow.  No operational blocking
flow theorem is assumed or asserted here.  This module proves the algebraic
and integral support accounting consumed by such an implementation.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DirectedUnitST.Repair

open Finset Certificate DirectedCertificate

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The antisymmetric update associated with directed phase usage. -/
def phaseDelta (phaseUse : V → V → ℝ) (u v : V) : ℝ :=
  phaseUse u v - phaseUse v u

omit [Fintype V] [DecidableEq V] in
theorem phaseDelta_isFlow (phaseUse : V → V → ℝ) : IsFlow (phaseDelta phaseUse) := by
  intro u v
  simp only [phaseDelta]
  ring

omit [DecidableEq V] in
/-- Discrete integration by parts for arbitrary directed arc usage. -/
theorem weighted_phase_divergence (g : V → V → ℝ) (p : V → ℝ) :
    ∑ u, p u * netOut (phaseDelta g) u =
      ∑ u, ∑ v, (p u - p v) * g u v := by
  simp only [netOut, phaseDelta, mul_sum, mul_sub, sub_mul, sum_sub_distrib]
  congr 1
  exact sum_comm

/-- Every used arc goes forward by exactly one frozen level, so total arc
mass is distance times phase value.  Terminal arcs are included. -/
theorem phase_mass_eq (g : V → V → ℝ) (level : V → ℝ) (s t : V) (value : ℝ)
    (hlevel : ∀ u v, g u v ≠ 0 → level v = level u + 1)
    (hdiv : ∀ v, netOut (phaseDelta g) v =
      (if v = s then value else 0) - (if v = t then value else 0)) :
    ∑ u, ∑ v, g u v = (level t - level s) * value := by
  have hmass : ∑ u, ∑ v, (level u - level v) * g u v =
      -(∑ u, ∑ v, g u v) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro u _
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro v _
    by_cases h : g u v = 0
    · simp [h]
    · rw [hlevel u v h]
      ring
  have htel := weighted_phase_divergence g level
  rw [hmass] at htel
  have hend : ∑ u, level u * netOut (phaseDelta g) u =
      level s * value - level t * value := by
    simp only [hdiv, mul_sub, sum_sub_distrib, mul_ite, mul_zero,
      sum_ite_eq', mem_univ, ↓reduceIte]
  rw [hend] at htel
  linarith

omit [Fintype V] [DecidableEq V] in
/-- Opposite directions cannot both be used during a frozen-level phase. -/
theorem reverse_phaseUse_zero (g : V → V → ℝ) (level : V → ℝ)
    (hlevel : ∀ u v, g u v ≠ 0 → level v = level u + 1)
    {u v : V} (huv : g u v ≠ 0) : g v u = 0 := by
  by_contra hvu
  have h1 := hlevel u v huv
  have h2 := hlevel v u hvu
  linarith

omit [Fintype V] [DecidableEq V] in
/-- On a used forward arc the signed phase update equals its entire directed
usage.  It is not canceled by the reverse arcs created in that phase. -/
theorem phaseDelta_eq_forward (g : V → V → ℝ) (level : V → ℝ)
    (hlevel : ∀ u v, g u v ≠ 0 → level v = level u + 1)
    {u v : V} (huv : g u v ≠ 0) : phaseDelta g u v = g u v := by
  simp only [phaseDelta, reverse_phaseUse_zero g level hlevel huv, sub_zero]

omit [Fintype V] [DecidableEq V] in
/-- Positive signed usage of a nonnegative frozen-level phase is forward.
This identifies which reverse residual arcs can be created by the phase. -/
theorem phaseDelta_pos_forward (g : V → V → ℝ) (level : V → ℝ)
    (hnonneg : ∀ u v, 0 ≤ g u v)
    (hlevel : ∀ u v, g u v ≠ 0 → level v = level u + 1)
    {u v : V} (hpos : 0 < phaseDelta g u v) : level v = level u + 1 := by
  apply hlevel u v
  intro hzero
  simp only [phaseDelta, hzero, zero_sub] at hpos
  linarith [hnonneg v u]

omit [Fintype V] [DecidableEq V] in
/-- After a forward-level flow, every positive residual arc still raises
the old levels by at most one. New reverse arcs go back by one level.
This is the all-arc invariant behind nondecreasing residual distances. -/
theorem residual_level_rise (G : WeightedDiGraph V) (level : V → ℝ)
    (hlevel : ∀ u v, 0 < G.c u v → level v ≤ level u + 1)
    (f : V → V → ℝ) (hf : G.Feasible f)
    (hforward : ∀ u v, 0 < f u v → level v = level u + 1)
    (u v : V) (hpos : 0 < (residual G f hf).c u v) :
    level v ≤ level u + 1 := by
  by_cases hc : 0 < G.c u v
  · exact hlevel u v hc
  · have hfneg : f u v < 0 := by
      rw [residual_c] at hpos
      linarith [le_of_not_gt hc]
    have hreverse : 0 < f v u := by rw [hf.1 u v]; linarith
    have h := hforward v u hreverse
    linarith

omit [Fintype V] [DecidableEq V] in
/-- Along a walk whose every step raises the old level by at most one, the
endpoint level difference is at most its length. -/
theorem walk_level_le_length (level : V → ℝ) (p : ℕ → V) (n : ℕ)
    (hstep : ∀ i < n, level (p (i + 1)) ≤ level (p i) + 1) :
    level (p n) ≤ level (p 0) + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprev := ih (fun i hi => hstep i (by omega))
    have hlast := hstep n (by omega)
    push_cast
    linarith

omit [Fintype V] [DecidableEq V] in
/-- A walk attaining the old distance must use only old forward-level arcs.
This supplies the graph-theoretic step from blocking to strict distance growth. -/
theorem tight_walk_steps (level : V → ℝ) (p : ℕ → V) (n : ℕ)
    (hstep : ∀ i < n, level (p (i + 1)) ≤ level (p i) + 1)
    (htight : level (p n) = level (p 0) + n) :
    ∀ i < n, level (p (i + 1)) = level (p i) + 1 := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    have hsteps : ∀ i < n, level (p (i + 1)) ≤ level (p i) + 1 :=
      fun i hi => hstep i (by omega)
    have hprev := walk_level_le_length level p n hsteps
    have hlast := hstep n (by omega)
    have htight' : level (p (n + 1)) = level (p 0) + (n : ℝ) + 1 := by
      push_cast at htight
      linarith
    have heq : level (p n) = level (p 0) + n := by linarith
    intro i hi
    by_cases hin : i = n
    · subst i
      linarith
    · exact ih hsteps heq i (by omega)

omit [Fintype V] [DecidableEq V] in
/-- If a residual walk is not entirely forward in the frozen levels, its
length is strictly larger than the old endpoint level difference. -/
theorem walk_length_strict (level : V → ℝ) (p : ℕ → V) (n : ℕ)
    (hstep : ∀ i < n, level (p (i + 1)) ≤ level (p i) + 1)
    (hnot : ¬ ∀ i < n, level (p (i + 1)) = level (p i) + 1) :
    level (p n) - level (p 0) < n := by
  have hle := walk_level_le_length level p n hstep
  by_contra h
  have htight : level (p n) = level (p 0) + n := by linarith
  exact hnot (tight_walk_steps level p n hstep htight)

omit [DecidableEq V] in
/-- Successful first discoveries represented by a set of distinct ordered
pairs are charged to integral directed phase usage. -/
theorem discoveries_le_phase_mass (g : V → V → ℕ) (D : Finset (V × V))
    (hD : ∀ e ∈ D, 0 < g e.1 e.2) :
    D.card ≤ ∑ u, ∑ v, g u v := by
  calc
    D.card = ∑ _ ∈ D, 1 := by simp
    _ ≤ ∑ e ∈ D, g e.1 e.2 := sum_le_sum fun e he => hD e he
    _ ≤ ∑ e : V × V, g e.1 e.2 := sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
    _ = _ := Fintype.sum_prod_type _

/-- The exact `d*r` charge for any distinct successful discoveries already
shown by an implementation to carry positive integral phase usage. -/
theorem discoveries_le_distance_value (g : V → V → ℕ) (level : V → ℝ)
    (s t : V) (value : ℝ) (D : Finset (V × V))
    (hD : ∀ e ∈ D, 0 < g e.1 e.2)
    (hlevel : ∀ u v, g u v ≠ 0 → level v = level u + 1)
    (hdiv : ∀ v, netOut (phaseDelta (fun u w => (g u w : ℝ))) v =
      (if v = s then value else 0) - (if v = t then value else 0)) :
    (D.card : ℝ) ≤ (level t - level s) * value := by
  have hmass := phase_mass_eq (fun u v => (g u v : ℝ)) level s t value
    (fun u v huv => hlevel u v (by exact_mod_cast huv)) hdiv
  have hcount := discoveries_le_phase_mass g D hD
  have hcountR : (D.card : ℝ) ≤ ∑ u, ∑ v, (g u v : ℝ) := by exact_mod_cast hcount
  rwa [hmass] at hcountR

end CutQueryComplexity.DirectedUnitST.Repair

#print axioms CutQueryComplexity.DirectedUnitST.Repair.phase_mass_eq
#print axioms CutQueryComplexity.DirectedUnitST.Repair.phaseDelta_eq_forward
#print axioms CutQueryComplexity.DirectedUnitST.Repair.residual_level_rise
#print axioms CutQueryComplexity.DirectedUnitST.Repair.walk_length_strict
#print axioms CutQueryComplexity.DirectedUnitST.Repair.discoveries_le_distance_value
