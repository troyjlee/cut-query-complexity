import CutQueryComplexity.FractionalForest.Potential
import Mathlib.Tactic.FieldSimp
import CutQueryComplexity.Graph.ArborescencePacking

/-! # Logarithm-free forest deletion (W4; `cor:forest-deletion`)

For a fractional forest `x` and `1 ≤ k ≤ n`, some `Z` with `|Z| ≤ n − 1` (`k = 1`) or
`|Z| ≤ q(n,k) = ⌊(2n+k−2)/k⌋ − 2` (`k ≥ 2`) satisfies the target
`x(E(S)) ≤ (1 − 1/k)|S|` for every `S ⊆ V ∖ Z`; uniformly, `|Z| ≤ 2(⌈n/k⌉ − 1)`.

* A: the rounding lemma for `q(n,k)` (`budgetQ`), with the quotient bounded below before the
  truncated subtraction is rewritten (`budgetQ_le`, `budgetQ_real`, `budgetQ_eq_ceil`).
* B: `D(V) ≤ 2n/k − 1` and a violation forces `D(W) > 1 + 1/k` (`Dpot_le_start`,
  `violation_Dpot`).
* C: a bounded induction over `q(n,k)` steps; idle steps keep `W` unchanged and claim no
  decrease (`deletion_induction`).
* D: the boundary cases `k = 1`, `k = 2`, `k = n` (`target_of_card_le`).
* E: the endpoints `forest_deletion_of_three_le`, `forest_deletion`, `forest_deletion_uniform`.

The unit-progress theorem enters as the explicit hypothesis `hprog`, in the exact form of
`unit_progress`.
-/

namespace CutQueryComplexity

open Finset

namespace FractionalForest

/-! ## A. The rounding lemma -/

/-- `q(n,k) = ⌊(2n+k-2)/k⌋ - 2 = ⌈(2n-1)/k⌉ - 2`, in `ℕ`. -/
def budgetQ (n k : ℕ) : ℕ := (2 * n + k - 2) / k - 2

/-- `A(n,k) = ⌈n/k⌉`, in `ℕ`. -/
def ceilA (n k : ℕ) : ℕ := (n + k - 1) / k

theorem two_le_budget_quot {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) :
    2 ≤ (2 * n + k - 2) / k := by
  rw [Nat.le_div_iff_mul_le (by omega)]
  omega

/-- The quotient `Q = (2n+k-2)/k` satisfies `2n - 1 ≤ kQ ≤ 2n + k - 2`. -/
theorem budget_quot_bounds {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) :
    2 * n - 1 ≤ k * ((2 * n + k - 2) / k) ∧ k * ((2 * n + k - 2) / k) ≤ 2 * n + k - 2 := by
  have h1 := Nat.div_add_mod (2 * n + k - 2) k
  have h2 := Nat.mod_lt (2 * n + k - 2) (show 0 < k by omega)
  constructor <;> omega

theorem budgetQ_add_two {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) :
    budgetQ n k + 2 = (2 * n + k - 2) / k := by
  have := two_le_budget_quot hk hkn
  unfold budgetQ; omega

theorem budgetQ_le {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) :
    budgetQ n k ≤ 2 * (ceilA n k - 1) := by
  have hQ := budgetQ_add_two hk hkn
  have hk0 : 0 < k := by omega
  -- `n ≤ k * A`
  have hA : n ≤ k * ceilA n k := by
    have h1 := Nat.div_add_mod (n + k - 1) k
    have h2 := Nat.mod_lt (n + k - 1) hk0
    unfold ceilA; omega
  have hA1 : 1 ≤ ceilA n k := by
    unfold ceilA; rw [Nat.le_div_iff_mul_le hk0]; omega
  -- `Q ≤ 2A`
  have hQA : (2 * n + k - 2) / k ≤ 2 * ceilA n k := by
    have : (2 * n + k - 2) / k < 2 * ceilA n k + 1 := by
      rw [Nat.div_lt_iff_lt_mul hk0]
      have : (2 * ceilA n k + 1) * k = 2 * (k * ceilA n k) + k := by ring
      rw [this]; omega
    omega
  omega

/-- The real rounding inequality `2n/k - 1 - q(n,k) ≤ 1 + 1/k`. -/
theorem budgetQ_real {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) :
    (2 * n / k - 1 : ℝ) - budgetQ n k ≤ 1 + 1 / k := by
  have hQ := budgetQ_add_two hk hkn
  obtain ⟨hlo, -⟩ := budget_quot_bounds hk hkn
  set Q := (2 * n + k - 2) / k with hQdef
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hqR : (budgetQ n k : ℝ) = (Q : ℝ) - 2 := by
    have : ((budgetQ n k + 2 : ℕ) : ℝ) = (Q : ℝ) := by rw [hQ]
    push_cast at this; linarith
  have hloR : (2 * n - 1 : ℝ) ≤ k * Q := by
    have h1 : 1 ≤ 2 * n := by omega
    have : ((2 * n - 1 : ℕ) : ℝ) ≤ ((k * Q : ℕ) : ℝ) := by exact_mod_cast hlo
    push_cast [Nat.cast_sub h1] at this; linarith
  rw [hqR]
  have : (2 * n / k : ℝ) - 1 - (Q - 2) - (1 + 1 / k) = (2 * n - 1 - k * Q) / k := by
    field_simp; ring
  have h2 : (2 * n - 1 - k * Q : ℝ) / k ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hkR.le
  linarith

/-- The ceiling form `q(n,k) = ⌈(2n-1)/k⌉ - 2`. -/
theorem budgetQ_eq_ceil {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) :
    (budgetQ n k : ℤ) = ⌈((2 * n - 1 : ℝ) / k)⌉ - 2 := by
  have hQ := budgetQ_add_two hk hkn
  obtain ⟨hlo, hhi⟩ := budget_quot_bounds hk hkn
  set Q := (2 * n + k - 2) / k with hQdef
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have h1 : 1 ≤ 2 * n := by omega
  have hloR : (2 * n - 1 : ℝ) ≤ k * Q := by
    have : ((2 * n - 1 : ℕ) : ℝ) ≤ ((k * Q : ℕ) : ℝ) := by exact_mod_cast hlo
    push_cast [Nat.cast_sub h1] at this; linarith
  have hhiR : (k * Q : ℝ) ≤ 2 * n + k - 2 := by
    have h2 : 2 ≤ 2 * n + k := by omega
    have : ((k * Q : ℕ) : ℝ) ≤ ((2 * n + k - 2 : ℕ) : ℝ) := by exact_mod_cast hhi
    push_cast [Nat.cast_sub h2] at this; linarith
  have hceil : ⌈((2 * n - 1 : ℝ) / k)⌉ = (Q : ℤ) := by
    rw [Int.ceil_eq_iff]
    push_cast
    constructor
    · rw [lt_div_iff₀ hkR]; nlinarith
    · rw [div_le_iff₀ hkR]; linarith
  rw [hceil]; omega

theorem budgetQ_two (n : ℕ) (hn : 2 ≤ n) : budgetQ n 2 = n - 2 := by
  unfold budgetQ
  have : (2 * n + 2 - 2) / 2 = n := by omega
  rw [this]

theorem budgetQ_self (n : ℕ) (hn : 2 ≤ n) : budgetQ n n = 0 := by
  unfold budgetQ
  have : (2 * n + n - 2) / n = 2 := by
    exact Nat.div_eq_of_lt_le (by omega) (by omega)
  rw [this]

/-! ## B. Start and stop bounds -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The deletion target `x(E(S)) ≤ (1 - 1/k)|S|` for every `S ⊆ W`. -/
def Target (x : WeightedGraph V) (k : ℕ) (W : Finset V) : Prop :=
  ∀ S ⊆ W, mass x S ≤ (1 - 1 / (k : ℝ)) * S.card

omit [Fintype V] [DecidableEq V] in
theorem Target.mono {x : WeightedGraph V} {k : ℕ} {W W' : Finset V} (h : Target x k W)
    (hW : W' ⊆ W) : Target x k W' := fun S hS => h S (hS.trans hW)

omit [Fintype V] [DecidableEq V] in
theorem not_target_iff {x : WeightedGraph V} {k : ℕ} {W : Finset V} :
    ¬ Target x k W ↔ ∃ S ⊆ W, (1 - 1 / (k : ℝ)) * S.card < mass x S := by
  unfold Target; push Not; rfl

omit [DecidableEq V] in
/-- **Start bound.** `D(W) ≤ 2n/k - 1` for a fractional forest (in particular for `W = V`). -/
theorem Dpot_le_start {x : WeightedGraph V} (hx : IsFractionalForest x) {k : ℕ} (hk : 0 < k)
    (hkn : k ≤ 2 * Fintype.card V) (W : Finset V) :
    Dpot x (2 / k) W ≤ 2 * (Fintype.card V : ℝ) / k - 1 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hn1 : (1 : ℝ) ≤ 2 * (Fintype.card V : ℝ) / k := by
    rw [le_div_iff₀ hkR]; have : (k : ℝ) ≤ 2 * Fintype.card V := by exact_mod_cast hkn
    linarith
  rw [Dpot_le_iff]
  intro S _
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp only [gfun_empty]; linarith
  · have hm := hx S hS
    have hc : (S.card : ℝ) ≤ Fintype.card V := by exact_mod_cast card_le_univ S
    have : gfun x (2 / k) S ≤ 2 * (S.card : ℝ) / k - 1 := by
      unfold gfun
      have : (1 - 2 / (k : ℝ)) * S.card = S.card - 2 * S.card / k := by ring
      linarith
    have h2 : 2 * (S.card : ℝ) / k ≤ 2 * (Fintype.card V : ℝ) / k :=
      div_le_div_of_nonneg_right (by linarith) hkR.le
    linarith

omit [Fintype V] [DecidableEq V] in
/-- A violating set has at least `k + 1` vertices. -/
theorem violation_card {x : WeightedGraph V} (hx : IsFractionalForest x) {k : ℕ} (hk : 0 < k)
    {S : Finset V} (hS : (1 - 1 / (k : ℝ)) * S.card < mass x S) : k + 1 ≤ S.card := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp at hS
  have hm := hx S hne
  have h1 : (1 : ℝ) < S.card / k := by
    have : (1 - 1 / (k : ℝ)) * S.card = S.card - S.card / k := by ring
    linarith
  rw [lt_div_iff₀ hkR, one_mul] at h1
  have : k < S.card := by exact_mod_cast h1
  omega

omit [Fintype V] [DecidableEq V] in
/-- **Stop bound.** A violation inside `W` forces `D(W) > 1 + 1/k` (strictly). -/
theorem violation_Dpot {x : WeightedGraph V} (hx : IsFractionalForest x) {k : ℕ} (hk : 0 < k)
    {W S : Finset V} (hSW : S ⊆ W) (hS : (1 - 1 / (k : ℝ)) * S.card < mass x S) :
    1 + 1 / (k : ℝ) < Dpot x (2 / k) W := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hc : ((k : ℝ) + 1) ≤ S.card := by exact_mod_cast violation_card hx hk hS
  have h1 : (S.card : ℝ) / k < gfun x (2 / k) S := by
    unfold gfun
    have : (1 - 2 / (k : ℝ)) * S.card = (1 - 1 / (k : ℝ)) * S.card - S.card / k := by ring
    linarith
  have h2 : 1 + 1 / (k : ℝ) ≤ S.card / k := by
    have : 1 + 1 / (k : ℝ) = (k + 1) / k := by field_simp
    rw [this]; exact div_le_div_of_nonneg_right hc hkR.le
  linarith [gfun_le_Dpot x (2 / k) hSW]

/-! ## C. Bounded induction -/

/-- **Bounded induction (plan step 5).** After `t` steps there are `W_t` and the number `a_t`
of active steps with `|V ∖ W_t| = a_t ≤ t`, `D(W_t) + a_t ≤ D(V)`, and, if some step was
idle (`a_t < t`), the target already holds on `W_t`. No decrease is claimed at idle steps. -/
theorem deletion_induction {x : WeightedGraph V} {k : ℕ}
    (hprog : ∀ {W : Finset V}, (∃ S ⊆ W, (1 - 1 / (k : ℝ)) * S.card < mass x S) →
      ∃ v ∈ W, 1 ≤ gain x (2 / k) W v) :
    ∀ t : ℕ, ∃ W : Finset V, ∃ a : ℕ, a ≤ t ∧ Wᶜ.card = a ∧
      Dpot x (2 / k) W + a ≤ Dpot x (2 / k) univ ∧ (a < t → Target x k W) := by
  intro t
  induction t with
  | zero => exact ⟨univ, 0, le_rfl, by simp, by simp, fun h => absurd h (Nat.lt_irrefl 0)⟩
  | succ t ih =>
    obtain ⟨W, a, hat, hcard, hD, hidle⟩ := ih
    by_cases hT : Target x k W
    · -- idle step: keep `W`
      exact ⟨W, a, by omega, hcard, hD, fun _ => hT⟩
    · -- active step: every earlier step was active, and we delete a unit-gain witness
      have hat' : a = t := by
        by_contra hne; exact hT (hidle (by omega))
      obtain ⟨v, hv, hg⟩ := hprog (not_target_iff.1 hT)
      refine ⟨W.erase v, a + 1, by omega, ?_, ?_, fun h => by omega⟩
      · rw [compl_erase, card_insert_of_notMem (by simpa using hv), hcard]
      · unfold gain at hg; push_cast; linarith

/-! ## E. The deletion endpoint for `k ≥ 3` -/

/-- **Forest deletion, `k ≥ 3`** (conditional on unit progress `hprog` at this `k`):
at most `q(n,k)` deletions leave every induced set of density at most `1 - 1/k`. -/
theorem forest_deletion_of_three_le {x : WeightedGraph V} (hx : IsFractionalForest x) {k : ℕ}
    (hk : 3 ≤ k) (hkn : k ≤ Fintype.card V)
    (hprog : ∀ {W : Finset V}, (∃ S ⊆ W, (1 - 1 / (k : ℝ)) * S.card < mass x S) →
      ∃ v ∈ W, 1 ≤ gain x (2 / k) W v) :
    ∃ Z : Finset V, Z.card ≤ budgetQ (Fintype.card V) k ∧
      ∀ S ⊆ Zᶜ, mass x S ≤ (1 - 1 / (k : ℝ)) * S.card := by
  obtain ⟨W, a, haq, hcard, hD, hidle⟩ := deletion_induction hprog (budgetQ (Fintype.card V) k)
  refine ⟨Wᶜ, hcard ▸ haq, ?_⟩
  rw [compl_compl]
  rcases Nat.lt_or_ge a (budgetQ (Fintype.card V) k) with hlt | hge
  · exact hidle hlt
  · have ha : a = budgetQ (Fintype.card V) k := le_antisymm haq hge
    by_contra hT
    obtain ⟨S, hSW, hS⟩ := not_target_iff.1 hT
    have h1 := violation_Dpot hx (by omega) hSW hS
    have h2 := Dpot_le_start hx (k := k) (by omega) (by omega) univ
    have h3 := budgetQ_real (n := Fintype.card V) (by omega) hkn
    rw [ha] at hD
    linarith

/-! ## D. Boundary cases -/

omit [Fintype V] [DecidableEq V] in
/-- If `|W| ≤ k`, the forest inequalities already give the target on `W`. -/
theorem target_of_card_le {x : WeightedGraph V} (hx : IsFractionalForest x) {k : ℕ}
    (hk : 0 < k) {W : Finset V} (hW : W.card ≤ k) : Target x k W := by
  intro S hS
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  have hm := hx S hne
  have hc : (S.card : ℝ) ≤ k := by exact_mod_cast (card_le_card hS).trans hW
  have : (S.card : ℝ) / k ≤ 1 := by rw [div_le_one hkR]; exact hc
  have : (1 - 1 / (k : ℝ)) * S.card = S.card - S.card / k := by ring
  linarith

/-- Retaining any `k ≤ n` vertices: `n - k` deletions suffice (this covers `k = 1, 2, n`). -/
theorem forest_deletion_retain {x : WeightedGraph V} (hx : IsFractionalForest x) {k : ℕ}
    (hk : 0 < k) (hkn : k ≤ Fintype.card V) :
    ∃ Z : Finset V, Z.card = Fintype.card V - k ∧
      ∀ S ⊆ Zᶜ, mass x S ≤ (1 - 1 / (k : ℝ)) * S.card := by
  obtain ⟨W, -, hW⟩ := exists_subset_card_eq (s := (univ : Finset V)) (by simpa using hkn)
  refine ⟨Wᶜ, by rw [card_compl, hW], ?_⟩
  rw [compl_compl]
  exact target_of_card_le hx hk hW.le

/-- `k = 1`: retain one vertex, delete `n - 1`. -/
theorem forest_deletion_one {x : WeightedGraph V} (hx : IsFractionalForest x)
    (hn : 1 ≤ Fintype.card V) :
    ∃ Z : Finset V, Z.card = Fintype.card V - 1 ∧
      ∀ S ⊆ Zᶜ, mass x S ≤ (1 - 1 / ((1 : ℕ) : ℝ)) * S.card :=
  forest_deletion_retain hx Nat.one_pos hn

/-- `k = 2`: retain two vertices (pair weight at most one), `n - 2 = q(n,2)` deletions. -/
theorem forest_deletion_two {x : WeightedGraph V} (hx : IsFractionalForest x)
    (hn : 2 ≤ Fintype.card V) :
    ∃ Z : Finset V, Z.card = budgetQ (Fintype.card V) 2 ∧
      ∀ S ⊆ Zᶜ, mass x S ≤ (1 - 1 / ((2 : ℕ) : ℝ)) * S.card := by
  rw [budgetQ_two _ hn]; exact forest_deletion_retain hx two_pos hn

/-- `k = n`: budget zero, and `q(n,n) = 0` so this agrees with the general formula. -/
theorem forest_deletion_self {x : WeightedGraph V} (hx : IsFractionalForest x)
    (hn : 2 ≤ Fintype.card V) :
    ∃ Z : Finset V, Z.card = budgetQ (Fintype.card V) (Fintype.card V) ∧
      ∀ S ⊆ Zᶜ, mass x S ≤ (1 - 1 / ((Fintype.card V : ℕ) : ℝ)) * S.card := by
  rw [budgetQ_self _ hn]
  simpa using forest_deletion_retain hx (k := Fintype.card V) (by omega) le_rfl

/-! ## E. The deletion endpoint for `1 ≤ k ≤ n` -/

/-- **Forest deletion endpoint** (`cor:forest-deletion`, conditional on unit progress for every
`k ≥ 3`). For `1 ≤ k ≤ n`: `|Z| ≤ n - 1` if `k = 1`, and `|Z| ≤ q(n,k)` otherwise. -/
theorem forest_deletion {x : WeightedGraph V} (hx : IsFractionalForest x) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ Fintype.card V)
    (hprog : ∀ k : ℕ, 3 ≤ k → ∀ W : Finset V,
      (∃ S ⊆ W, (1 - 1 / (k : ℝ)) * S.card < mass x S) → ∃ v ∈ W, 1 ≤ gain x (2 / k) W v) :
    ∃ Z : Finset V,
      Z.card ≤ (if k = 1 then Fintype.card V - 1 else budgetQ (Fintype.card V) k) ∧
      ∀ S ⊆ Zᶜ, mass x S ≤ (1 - 1 / (k : ℝ)) * S.card := by
  rcases (show k = 1 ∨ k = 2 ∨ 3 ≤ k by omega) with rfl | rfl | h3
  · obtain ⟨Z, hZ, h⟩ := forest_deletion_one hx hkn
    exact ⟨Z, by simp [hZ], h⟩
  · obtain ⟨Z, hZ, h⟩ := forest_deletion_two hx hkn
    exact ⟨Z, by simp [hZ], h⟩
  · obtain ⟨Z, hZ, h⟩ := forest_deletion_of_three_le hx h3 hkn (fun hv => hprog k h3 _ hv)
    exact ⟨Z, by simpa [show k ≠ 1 by omega] using hZ, h⟩

/-- **Uniform corollary**: `|Z| ≤ 2(⌈n/k⌉ - 1) = O(n/k)`. -/
theorem forest_deletion_uniform {x : WeightedGraph V} (hx : IsFractionalForest x) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ Fintype.card V)
    (hprog : ∀ k : ℕ, 3 ≤ k → ∀ W : Finset V,
      (∃ S ⊆ W, (1 - 1 / (k : ℝ)) * S.card < mass x S) → ∃ v ∈ W, 1 ≤ gain x (2 / k) W v) :
    ∃ Z : Finset V, Z.card ≤ 2 * (ceilA (Fintype.card V) k - 1) ∧
      ∀ S ⊆ Zᶜ, mass x S ≤ (1 - 1 / (k : ℝ)) * S.card := by
  obtain ⟨Z, hZ, h⟩ := forest_deletion hx hk hkn hprog
  refine ⟨Z, ?_, h⟩
  split_ifs at hZ with h1
  · subst h1
    have : ceilA (Fintype.card V) 1 = Fintype.card V := by simp [ceilA]
    omega
  · exact hZ.trans (budgetQ_le (by omega) hkn)

end FractionalForest

end CutQueryComplexity
