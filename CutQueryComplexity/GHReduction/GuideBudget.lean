import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Log
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Repaired guide-recursion vertex accounting

An actual same-parameter child keeps a disjoint shore `S i` and adds one
complement proxy. Its real guide vertices are `S i ∩ R` plus that proxy.
The two conserved quantities are nonterminal mass and real count minus two.
No equality between the union of isolating shores and the original graph is
used. The scalar frontier lemmas below are arithmetic interfaces; connecting
them to the complete recursive program is a separate obligation.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical BigOperators

variable {V ι : Type} [Fintype V] [DecidableEq V] [DecidableEq ι]

/-- Each child's complement proxy counts once as both a graph and a real guide
vertex, so it contributes no nonterminal mass. -/
theorem child_nonterminal_mass (S R : Finset V) :
    S.card + 1 - ((S ∩ R).card + 1) = (S \ R).card := by
  rw [Finset.card_sdiff, Finset.inter_comm R S]
  omega

theorem sum_child_nonterminal_mass_le (I : Finset ι) (S : ι → Finset V)
    (R : Finset V) (hdisj : (I : Set ι).PairwiseDisjoint S) :
    (∑ i ∈ I, ((S i).card + 1 - ((S i ∩ R).card + 1))) ≤
      Fintype.card V - R.card := by
  have hd : (I : Set ι).PairwiseDisjoint (fun i => S i \ R) := by
    intro i hi j hj hij
    exact (hdisj hi hj hij).mono Finset.sdiff_subset Finset.sdiff_subset
  calc
    _ = ∑ i ∈ I, (S i \ R).card := Finset.sum_congr rfl (fun i _ => child_nonterminal_mass _ _)
    _ = (I.biUnion (fun i => S i \ R)).card := (Finset.card_biUnion hd).symm
    _ ≤ Rᶜ.card := Finset.card_le_card (by
      intro v hv
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hv
      exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hi).2)
    _ = _ := Finset.card_compl R

theorem sum_real_groups_le (I : Finset ι) (S : ι → Finset V) (R : Finset V)
    (hdisj : (I : Set ι).PairwiseDisjoint S) :
    (∑ i ∈ I, (S i ∩ R).card) ≤ R.card := by
  have hd : (I : Set ι).PairwiseDisjoint (fun i => S i ∩ R) := by
    intro i hi j hj hij
    exact (hdisj hi hj hij).mono Finset.inter_subset_left Finset.inter_subset_left
  rw [← Finset.card_biUnion hd]
  apply Finset.card_le_card
  intro v hv
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hv
  exact (Finset.mem_inter.mp hi).2

/-- Nonempty retained centroid groups pay for their new real proxies. -/
theorem child_count_le_real_count (I : Finset ι) (S : ι → Finset V) (R : Finset V)
    (hdisj : (I : Set ι).PairwiseDisjoint S)
    (hne : ∀ i ∈ I, (S i ∩ R).Nonempty) : I.card ≤ R.card := by
  calc
    I.card = ∑ _i ∈ I, 1 := by simp
    _ ≤ ∑ i ∈ I, (S i ∩ R).card := Finset.sum_le_sum (fun i hi => (hne i hi).card_pos)
    _ ≤ R.card := sum_real_groups_le I S R hdisj

/-- Balance and coverage except for at most one centroid force at least two
nonempty groups above the constant-size base case. -/
theorem two_le_children_of_balanced_cover (I : Finset ι) (r : ι → ℕ) {R : ℕ}
    (hlarge : 2 < R) (hcover : R ≤ 1 + ∑ i ∈ I, r i)
    (hhalf : ∀ i ∈ I, 2 * r i ≤ R) : 2 ≤ I.card := by
  by_contra h
  have hsmall : I.card = 0 ∨ I.card = 1 := by omega
  rcases hsmall with hz | ho
  · have he : I = ∅ := Finset.card_eq_zero.mp hz
    simp only [he, Finset.sum_empty, add_zero] at hcover
    omega
  · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp ho
    have hh := hhalf i (by simp [hi])
    simp only [hi, Finset.sum_singleton] at hcover
    omega

/-- The exact nonnegative `r - 2` potential, including size-two children. -/
theorem sum_child_real_potential_le (I : Finset ι) (S : ι → Finset V)
    (R : Finset V) (hdisj : (I : Set ι).PairwiseDisjoint S)
    (hne : ∀ i ∈ I, (S i ∩ R).Nonempty) (htwo : 2 ≤ I.card) :
    (∑ i ∈ I, ((S i ∩ R).card + 1 - 2)) ≤ R.card - 2 := by
  have hsum : (∑ i ∈ I, ((S i ∩ R).card + 1 - 2)) + I.card =
      ∑ i ∈ I, (S i ∩ R).card := by
    calc
      _ = (∑ i ∈ I, ((S i ∩ R).card + 1 - 2)) + ∑ _i ∈ I, 1 := by simp
      _ = ∑ i ∈ I, (((S i ∩ R).card + 1 - 2) + 1) :=
        (Finset.sum_add_distrib).symm
      _ = _ := Finset.sum_congr rfl (fun i hi => by have := (hne i hi).card_pos; omega)
  have hle := sum_real_groups_le I S R hdisj
  omega

/-- The total size of all children, including the zero-potential size-two
leaves, is charged to their parent. -/
theorem sum_child_sizes_le (I : Finset ι) (S : ι → Finset V) (R : Finset V)
    (hdisj : (I : Set ι).PairwiseDisjoint S)
    (hne : ∀ i ∈ I, (S i ∩ R).Nonempty) :
    (∑ i ∈ I, ((S i).card + 1)) ≤ Fintype.card V + R.card := by
  have hs : (∑ i ∈ I, (S i).card) ≤ Fintype.card V := by
    rw [← Finset.card_biUnion hdisj]
    exact Finset.card_le_univ _
  have hc := child_count_le_real_count I S R hdisj hne
  simpa [Finset.sum_add_distrib] using Nat.add_le_add hs hc

theorem child_size_le_parent (S R : Finset V) (hhalf : 2 * (S ∩ R).card ≤ R.card)
    (hne : R.Nonempty) : S.card + 1 ≤ Fintype.card V := by
  have hproper : S ≠ Finset.univ := by
    intro he
    rw [he, Finset.univ_inter] at hhalf
    have := hne.card_pos
    omega
  have hlt : S.card < Fintype.card V := Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hproper⟩)
  omega

/-- Subtracting two absorbs the complement proxy and halves the potential. -/
theorem child_potential_halves {r rchild : ℕ} (hreal : 1 ≤ rchild)
    (hhalf : 2 * rchild ≤ r) : 2 * (rchild + 1 - 2) ≤ r - 2 := by
  omega

/-- A same-parameter path cannot retain positive potential beyond logarithmic
depth. This avoids real logarithms and follows the actual halving recurrence. -/
theorem potential_path_bound (r : ℕ → ℕ) (hstep : ∀ i, 2 * r (i + 1) ≤ r i) :
    ∀ d, 2 ^ d * r d ≤ r 0 := by
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
      calc
        2 ^ (d + 1) * r (d + 1) = 2 ^ d * (2 * r (d + 1)) := by rw [pow_succ, Nat.mul_assoc]
        _ ≤ 2 ^ d * r d := Nat.mul_le_mul_left _ (hstep d)
        _ ≤ r 0 := ih

theorem potential_path_zero (r : ℕ → ℕ) (hstep : ∀ i, 2 * r (i + 1) ≤ r i)
    {d : ℕ} (hd : r 0 < 2 ^ d) : r d = 0 := by
  have h := potential_path_bound r hstep d
  by_contra hn
  have hr : 1 ≤ r d := by omega
  have hp := Nat.mul_le_mul_left (2 ^ d) hr
  simp only [mul_one] at hp
  omega

theorem potential_path_clog (r : ℕ → ℕ) (hstep : ∀ i, 2 * r (i + 1) ≤ r i) :
    r (Nat.clog 2 (r 0 + 1)) = 0 := by
  apply potential_path_zero r hstep
  have h := Nat.le_pow_clog (by omega : 1 < 2) (r 0 + 1)
  omega

/-- Internal graph sizes are bounded by the two conserved quantities. -/
theorem internal_size_le_mass_potential {s r : ℕ} (hrs : r ≤ s) (hr : 4 ≤ r) :
    s ≤ (s - r) + 2 * (r - 2) := by omega

/-- A level of internal nodes has linear aggregate size once conservation has
been transported down the actual recursion. This is a scalar summation lemma. -/
theorem internal_level_size_le (I : Finset ι) (s r : ι → ℕ) {s0 r0 : ℕ}
    (hroot : r0 ≤ s0)
    (hsize : ∀ i ∈ I, r i ≤ s i) (hinternal : ∀ i ∈ I, 4 ≤ r i)
    (hmass : (∑ i ∈ I, (s i - r i)) ≤ s0 - r0)
    (hpotential : (∑ i ∈ I, (r i - 2)) ≤ r0 - 2) :
    (∑ i ∈ I, s i) ≤ 2 * s0 := by
  have hsum := Finset.sum_le_sum (fun i hi =>
    internal_size_le_mass_potential (hsize i hi) (hinternal i hi))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  omega

/-- Translate a proved aggregate vertex budget to the supplied size-dependent
primitive query budget, with the original capacity parameter held fixed. -/
theorem sum_primitive_cost_le (I : Finset ι) (sizes : ι → ℕ) (Q : ℕ → ℕ)
    {n B : ℕ} (hn : 0 < n)
    (hrange : ∀ i ∈ I, 1 ≤ sizes i ∧ sizes i ≤ n)
    (hregular : ∀ s, 1 ≤ s → s ≤ n → n * Q s ≤ s * Q n)
    (hsize : (∑ i ∈ I, sizes i) ≤ n * B) :
    (∑ i ∈ I, Q (sizes i)) ≤ B * Q n := by
  have hmul : n * (∑ i ∈ I, Q (sizes i)) ≤ n * (B * Q n) := by
    calc
      _ = ∑ i ∈ I, n * Q (sizes i) := Finset.mul_sum _ _ _
      _ ≤ ∑ i ∈ I, sizes i * Q n := Finset.sum_le_sum
        (fun i hi => hregular _ (hrange i hi).1 (hrange i hi).2)
      _ = (∑ i ∈ I, sizes i) * Q n := (Finset.sum_mul _ _ _).symm
      _ ≤ (n * B) * Q n := Nat.mul_le_mul_right (Q n) hsize
      _ = _ := Nat.mul_assoc _ _ _
  by_contra h
  have hstrict : B * Q n + 1 ≤ ∑ i ∈ I, Q (sizes i) := by omega
  have hscaled := Nat.mul_le_mul_left n hstrict
  nlinarith

end
end CutQueryComplexity.GHReduction
