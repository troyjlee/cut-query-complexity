import CutQueryComplexity.ImplicitLP.GenericQuery.SpectralBounds

/-! # The public general finite-box incidence-LP query endpoint

The program and its finite cap depend only on original public input. Honest
hidden multiplicities and a strictly feasible supplied start are proof-side
conditions for success. Every answer oracle satisfies the same cost bound.
Exact local real arithmetic is free in this theorem.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option exponentiation.threshold 512
namespace CutQueryComplexity.ImplicitLP.GenericQuery
open Real Probability
noncomputable section
variable {n me : ℕ} {D : Data n me} {P : Envelope}

def logarithmicDegree : ℕ := 21
def leadingConstant (C Cexp : ℝ) : ℝ := 2 ^ 330 * (C + Cexp)
def explicitQueryBound (n : ℕ) (P : Envelope) : ℝ :=
  leadingConstant P.C P.Cexp * (n : ℝ) ^ (3 / 2 : ℝ) *
    log (2 * P.Npub n) ^ logarithmicDegree

theorem leadingConstant_pos {C Cexp : ℝ} (hC : 1 ≤ C) (hCe : 1 ≤ Cexp) :
    0 < leadingConstant C Cexp := by
  unfold leadingConstant
  positivity

theorem logarithmicDegree_eq : logarithmicDegree = 21 := rfl

theorem n_mul_sqrt_eq (n : ℕ) :
    (n : ℝ) * sqrt n = (n : ℝ) ^ (3 / 2 : ℝ) := by
  by_cases hn : n = 0
  · subst n
    norm_num
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [sqrt_eq_rpow]
  calc (n : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) =
      (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := by rw [rpow_one]
    _ = (n : ℝ) ^ ((1 : ℝ) + 1 / 2) := (rpow_add hn0 _ _).symm
    _ = _ := by norm_num

/-- The finite solver cap, with the n^(3/2) factor retained through all phases. -/
theorem queryCap_logb_le (HP : PublicHyp D P) :
    (queryCap D P : ℝ) ≤ 2 ^ 304 * P.C * (n : ℝ) ^ (3 / 2 : ℝ) * logHeight n P ^ 21 := by
  let Q := calibratedParams D P
  let L := logHeight n P
  let B := P.C * (n : ℝ) * sqrt n * L ^ 21
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast HP.rank_ge
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hC : 0 ≤ P.C := by linarith [HP.C_ge]
  have hL : 1 ≤ L := HP.logHeight_bounds.1
  have hs : 1 ≤ sqrt (n : ℝ) := one_le_sqrt.mpr (by linarith)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hscale : 1 ≤ sqrt (n : ℝ) * L ^ 6 := by
    have hp := one_le_pow₀ hL (n := 6)
    nlinarith
  have hd : (Q.downSteps : ℝ) ≤ 2 ^ 74 * sqrt n * L ^ 6 := calibratedDownSteps_le HP
  have hu : (Q.upSteps : ℝ) ≤ 2 ^ 74 * sqrt n * L ^ 6 := calibratedUpSteps_le HP
  have hphase : (Q.downSteps : ℝ) + 1 + Q.upSteps ≤ 2 ^ 76 * sqrt n * L ^ 6 := by nlinarith
  have hf : (Q.finalSteps : ℝ) ≤ 32 * L := publicFinalCount_le HP
  obtain ⟨hnewton, hinit, hbatch⟩ := calibrated_primitive_budgets HP
  change (Q.newtonBudget : ℝ) ≤ 2 ^ 217 * P.C * n * L ^ 14 at hnewton
  change (Q.initialBudget : ℝ) ≤ 2 ^ 224 * P.C * n * L ^ 15 at hinit
  change (Q.batchBudget : ℝ) ≤ 2 ^ 226 * P.C * n * L ^ 15 at hbatch
  have hgrowth (k : ℕ) (hk : k ≤ 21) : P.C * (n : ℝ) * L ^ k ≤ B := by
    calc _ ≤ P.C * (n : ℝ) * L ^ 21 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL hk) (by positivity)
      _ ≤ (P.C * (n : ℝ) * sqrt n) * L ^ 21 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact le_mul_of_one_le_right (by positivity) hs
  have hinit' : (Q.initialBudget : ℝ) ≤ 2 ^ 224 * B :=
    hinit.trans (by nlinarith [hgrowth 15 (by norm_num)])
  have hpath : ((Q.downSteps : ℝ) + 1 + Q.upSteps) * Q.batchBudget ≤ 2 ^ 302 * B := by
    have hh := mul_le_mul hphase hbatch (Nat.cast_nonneg _)
      (by positivity : 0 ≤ 2 ^ 76 * sqrt n * L ^ 6)
    convert hh using 1 <;> dsimp [B] <;> ring
  have hcenter : (Q.finalSteps : ℝ) * Q.newtonBudget ≤ 2 ^ 222 * B := by
    have hh := mul_le_mul hf hnewton (Nat.cast_nonneg _) (by positivity : 0 ≤ 32 * L)
    have he : (32 * L) * (2 ^ 217 * P.C * n * L ^ 14) =
        2 ^ 222 * (P.C * (n : ℝ) * L ^ 15) := by ring
    rw [he] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (hgrowth 15 (by norm_num)) (by positivity))
  have he : (queryCap D P : ℝ) = (Q.initialBudget : ℝ) +
      ((Q.downSteps : ℝ) + 1 + Q.upSteps) * Q.batchBudget +
        (Q.finalSteps : ℝ) * Q.newtonBudget := by
    unfold queryCap Params.solverBudget
    push_cast
    ring
  have heq : P.C * (n : ℝ) ^ (3 / 2 : ℝ) * L ^ 21 = B := by
    rw [← n_mul_sqrt_eq]
    dsimp [B]
    ring
  change _ ≤ 2 ^ 304 * P.C * (n : ℝ) ^ (3 / 2 : ℝ) * L ^ 21
  rw [he, show (2 : ℝ) ^ 304 * P.C * (n : ℝ) ^ (3 / 2 : ℝ) * L ^ 21 =
      2 ^ 304 * B by
        calc _ = 2 ^ 304 * (P.C * (n : ℝ) ^ (3 / 2 : ℝ) * L ^ 21) := by ring
          _ = _ := by rw [heq]]
  nlinarith only [hinit', hpath, hcenter, hB]

/-- Constructed universal exponent and leading constant; no cost premise is supplied. -/
theorem queryCap_le (HP : PublicHyp D P) : (queryCap D P : ℝ) ≤ explicitQueryBound n P := by
  have hB := HP.height_inputs.1
  have hlog0 : 0 ≤ log (height n P) := log_nonneg (by linarith)
  have htwo := Sparsify.log_two_ge
  have hl : logHeight n P ≤ 2 * log (height n P) := by
    unfold logHeight logb
    rw [div_le_iff₀ (log_pos (by norm_num : (1 : ℝ) < 2))]
    nlinarith [mul_le_mul_of_nonneg_left htwo hlog0]
  have hl0 : 0 ≤ logHeight n P := by linarith [HP.logHeight_bounds.1]
  have hC : 0 ≤ P.C := by linarith [HP.C_ge]
  have hCe : 0 ≤ P.Cexp := by linarith [HP.Cexp_ge]
  have hn0 : 0 ≤ (n : ℝ) ^ (3 / 2 : ℝ) := rpow_nonneg (Nat.cast_nonneg _) _
  have hcoef : 0 ≤ (2 : ℝ) ^ 304 * P.C * (n : ℝ) ^ (3 / 2 : ℝ) :=
    mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) hC) hn0
  have hh := queryCap_logb_le HP
  calc (queryCap D P : ℝ) ≤ 2 ^ 304 * P.C * (n : ℝ) ^ (3 / 2 : ℝ) * logHeight n P ^ 21 := hh
    _ ≤ 2 ^ 304 * P.C * (n : ℝ) ^ (3 / 2 : ℝ) * (2 * log (height n P)) ^ 21 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl0 hl _) hcoef
    _ = 2 ^ 325 * P.C * ((n : ℝ) ^ (3 / 2 : ℝ) * log (height n P) ^ 21) := by ring
    _ ≤ 2 ^ 330 * (P.C + P.Cexp) *
        ((n : ℝ) ^ (3 / 2 : ℝ) * log (height n P) ^ 21) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith
    _ = explicitQueryBound n P := by
      unfold explicitQueryBound leadingConstant logarithmicDegree height
      ring

theorem solve_query_bound (HP : PublicHyp D P) (read : Finset (Fin n) → ℕ)
    {out : Option (Point n me) × ℕ} (ho : out ∈ (RTree.run read (solve D P)).support) :
    (out.2 : ℝ) ≤ explicitQueryBound n P := by
  have hc : (out.2 : ℝ) ≤ queryCap D P := by exact_mod_cast solve_cost D P read ho
  exact hc.trans (queryCap_le HP)

/-- The headline is about the actual public program, with one shared success event
for every feasible comparator. Hidden rows occur only in the graph-side predicate. -/
theorem incidenceLP_query_endpoint (HP : PublicHyp D P) :
    (∀ (read : Finset (Fin n) → ℕ) (out : Option (Point n me) × ℕ),
      out ∈ (RTree.run read (solve D P)).support → (out.2 : ℝ) ≤ explicitQueryBound n P) ∧
    (∀ (G : DiGraph (Fin n)), HonestInput G D P →
      1 - P.ζ ≤ (solve D P).successProb G.out (Solved G D P.ε)) := by
  exact ⟨fun read out ho => solve_query_bound HP read ho, fun G HG => solve_success HP HG⟩

/-- Optional polynomial-size input envelopes yield the paper's soft-O corollary.
The extra hypothesis is only on original numerical data, never on execution. -/
theorem polynomial_input_query_bound (HP : PublicHyp D P) {k : ℕ}
    (hsize : 2 * P.Npub n ≤ (2 * (n : ℝ)) ^ k)
    (read : Finset (Fin n) → ℕ) {out : Option (Point n me) × ℕ}
    (ho : out ∈ (RTree.run read (solve D P)).support) :
    (out.2 : ℝ) ≤ (leadingConstant P.C P.Cexp * (k : ℝ) ^ logarithmicDegree) *
      (n : ℝ) ^ (3 / 2 : ℝ) * log (2 * (n : ℝ)) ^ logarithmicDegree := by
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast HP.rank_ge
  have hN : 0 < 2 * P.Npub n := by have := HP.height_inputs.1; change 2 ≤ 2 * P.Npub n at this; linarith
  have hlog := log_le_log hN hsize
  rw [log_pow] at hlog
  have hlog0 : 0 ≤ log (2 * P.Npub n) := log_nonneg (by have := HP.height_inputs.1; exact (by norm_num : (1 : ℝ) ≤ 2).trans this)
  have hC : 0 ≤ leadingConstant P.C P.Cexp := by
    unfold leadingConstant
    have := HP.C_ge
    have := HP.Cexp_ge
    positivity
  calc (out.2 : ℝ) ≤ explicitQueryBound n P := solve_query_bound HP read ho
    _ ≤ leadingConstant P.C P.Cexp * (n : ℝ) ^ (3 / 2 : ℝ) *
        ((k : ℝ) * log (2 * (n : ℝ))) ^ logarithmicDegree := by
      unfold explicitQueryBound
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog0 hlog _)
        (mul_nonneg hC (rpow_nonneg (Nat.cast_nonneg _) _))
    _ = _ := by rw [mul_pow]; ring

#print axioms queryCap_logb_le
#print axioms leadingConstant_pos
#print axioms queryCap_le
#print axioms solve_query_bound
#print axioms incidenceLP_query_endpoint
#print axioms polynomial_input_query_bound

end
end CutQueryComplexity.ImplicitLP.GenericQuery
