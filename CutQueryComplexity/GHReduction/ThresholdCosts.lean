import CutQueryComplexity.GHReduction.SourceMaximum
import CutQueryComplexity.GHReduction.RandomPrograms

/-! # Realized costs of adaptive threshold and maximum searches

Although each bounded subroutine has a cap indexed by the original size,
its realized cost is proportional to the actual graph size after multiplying
by that reference size. These pathwise bounds hold for every read history;
no probability cutoff or independence assumption is used for query accounting.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical

variable {V : Type} [Fintype V] [DecidableEq V]

theorem thresholdRoundTree_run {M n : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) (U : Finset V) (s : V)
    (W : ℝ) (z levels : ℕ) (read : Finset V → ℝ) :
    RTree.run read (thresholdRoundTree family n U s W z levels) =
      (thresholdSeedPMF V levels).map (fun seed =>
        (Prog.eval read (thresholdRoundProgram family U s W z levels seed),
          Prog.cost read (thresholdRoundProgram family U s W z levels seed))) := by
  simp only [thresholdRoundTree, RTree.run_mix, PMF.bind_map, Function.comp_def]
  have he (seed : ThresholdSeed V levels) :
      RTree.run read (RTree.ofDeterministic
        ((Prog.toDTree (thresholdRoundProgram family U s W z levels seed)
          (thresholdRoundBudget Q n levels)).map (fun output => output.getD ∅))) =
      PMF.pure (Prog.eval read (thresholdRoundProgram family U s W z levels seed),
        Prog.cost read (thresholdRoundProgram family U s W z levels seed)) := by
    simp only [RTree.run_ofDeterministic, DTree.run_map,
      Prog.toDTree_run read _ _ (thresholdRoundProgram_cost family hvn hQ U s W z levels seed read),
      Option.getD_some]
  simp_rw [he]
  rfl

theorem thresholdRoundTree_cost_scaled {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (U : Finset V) (s : V) (W : ℝ) (z levels : ℕ) (read : Finset V → ℝ)
    {p : Finset V × ℕ}
    (hp : p ∈ (RTree.run read (thresholdRoundTree family n U s W z levels)).support) :
    n * p.2 ≤ Fintype.card V * thresholdRoundBudget Q n levels := by
  rw [thresholdRoundTree_run family hvn hQ] at hp
  obtain ⟨seed, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
  rw [← heq]
  have h := thresholdRoundProgram_cost_scaled family hvn hQ U s W z levels seed read
  simpa only [thresholdRoundBudget, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

theorem thresholdRemainingTree_cost_scaled {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (s : V) (W : ℝ) (levels rounds : ℕ) (U : Finset V) (read : Finset V → ℝ)
    {p : Finset V × ℕ}
    (hp : p ∈ (RTree.run read (thresholdRemainingTree family n s W levels rounds U)).support) :
    n * p.2 ≤ Fintype.card V * (rounds * thresholdRoundBudget Q n levels) := by
  induction rounds generalizing U p with
  | zero =>
    simp only [thresholdRemainingTree, RTree.run_pure, PMF.pure_map] at hp
    have heq := (PMF.mem_support_pure_iff _ _).mp hp
    subst p
    simp
  | succ rounds ih =>
    simp only [thresholdRemainingTree, RTree.run_cast, RTree.run_bind] at hp
    obtain ⟨first, hfirst, hnext⟩ := (PMF.mem_support_bind_iff _ _ _).mp hp
    obtain ⟨second, hsecond, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hnext
    have h₁ := thresholdRoundTree_cost_scaled family hvn hQ U s W n levels read hfirst
    have h₂ := ih (U := U \ first.1) hsecond
    rw [← heq]
    simp only [Nat.mul_add, Nat.succ_mul]
    nlinarith

theorem thresholdClassifyTree_cost_scaled {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (U : Finset V) (s : V) (W : ℝ) (levels scale exponent : ℕ) (read : Finset V → ℝ)
    {p : Finset V × ℕ}
    (hp : p ∈ (RTree.run read
      (thresholdClassifyTree family n U s W levels scale exponent)).support) :
    n * p.2 ≤ Fintype.card V * sourceThresholdBudget Q n levels scale exponent := by
  rw [thresholdClassifyTree, random_run_map] at hp
  obtain ⟨r, hr, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
  rw [← heq]
  exact thresholdRemainingTree_cost_scaled family hvn hQ s W levels _ U read (p := r) hr

theorem sourceMaxAtTree_cost_scaled {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (s : V) (levels scale exponent fuel : ℕ) (R : Finset V) (lo hi : ℕ)
    (read : Finset V → ℝ) {p : Option V × ℕ}
    (hp : p ∈ (RTree.run read
      (sourceMaxAtTree family n s levels scale exponent fuel R lo hi)).support) :
    n * p.2 ≤ Fintype.card V * (fuel * sourceThresholdBudget Q n levels scale exponent) := by
  induction fuel generalizing R lo hi p with
  | zero =>
    simp only [sourceMaxAtTree, RTree.run_pure, PMF.pure_map] at hp
    have heq := (PMF.mem_support_pure_iff _ _).mp hp
    subst p
    simp
  | succ fuel ih =>
    by_cases hhilo : hi ≤ lo
    · simp only [sourceMaxAtTree, hhilo, ite_true, RTree.run_pure, PMF.pure_map] at hp
      have heq := (PMF.mem_support_pure_iff _ _).mp hp
      subst p
      simp
    · simp only [sourceMaxAtTree, hhilo, ite_false, RTree.run_cast, RTree.run_bind] at hp
      obtain ⟨first, hfirst, hnext⟩ := (PMF.mem_support_bind_iff _ _ _).mp hp
      obtain ⟨second, hsecond, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hnext
      have h₁ := thresholdClassifyTree_cost_scaled family hvn hQ (insert s R) s
        ((lo + (hi - lo) / 2 : ℕ) : ℝ) levels scale exponent read hfirst
      have h₂ : n * second.2 ≤
          Fintype.card V * (fuel * sourceThresholdBudget Q n levels scale exponent) := by
        by_cases hhigh : (R \ first.1).Nonempty
        · simp only [hhigh, ite_true] at hsecond
          exact ih _ _ _ hsecond
        · simp only [hhigh, ite_false] at hsecond
          exact ih _ _ _ hsecond
      rw [← heq]
      simp only [Nat.mul_add, Nat.succ_mul]
      nlinarith

theorem sourceMaxTree_cost_scaled {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (R : Finset V) (s : V) (levels scale exponent : ℕ) (read : Finset V → ℝ)
    {p : Option V × ℕ}
    (hp : p ∈ (RTree.run read (sourceMaxTree family n R s levels scale exponent)).support) :
    n * p.2 ≤ Fintype.card V *
      (Nat.clog 2 (M + 1) * sourceThresholdBudget Q n levels scale exponent) :=
  sourceMaxAtTree_cost_scaled family hvn hQ s levels scale exponent _ R 0 M read hp

end
end CutQueryComplexity.GHReduction
