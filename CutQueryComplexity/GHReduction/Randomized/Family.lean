import CutQueryComplexity.GHReduction.RandomRepetition
import CutQueryComplexity.GHReduction.Specification

/-! # Randomized canonical s-t families and their amplification

A randomized s-t family returns the canonical (inclusion-minimal) minimum s-t
shore with probability at least `1 - δ` on every promised instance. Repeating it
`r` times, querying the value of every returned shore, and intersecting the
valid candidates of least value gives a family that fails with probability at
most `δ ^ r`. If one run returned the canonical shore `S*`, the least value is
the minimum, every kept candidate is a minimum s-t shore and hence contains
`S*`, and `S*` is itself kept, so the intersection is `S*`. No majority vote or
concentration bound is needed.

The amplified cost is `r * (Q k + k)` rather than `r * (Q k + 1)`, so that the
size regularity `n * Q s ≤ s * Q n` of the reduction is preserved.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction.Randomized
noncomputable section
open scoped Classical ENNReal
open WeightedGraph Probability

/-- Public randomized s-t programs on every compact size, before any correctness claim. -/
abbrev STPrograms (Q : ℕ → ℕ) : Type :=
  ∀ k : ℕ, Fin k → Fin k → RTree (Finset (Fin k)) ℝ (Finset (Fin k)) (Q k)

/-- On every instance satisfying the primitive's promise, the program misses the
canonical shore with probability at most `δ`. -/
def STPrograms.FailsAtMost {Q : ℕ → ℕ} (P : STPrograms Q) (M : ℕ) (δ : ℝ≥0∞) : Prop :=
  ∀ (k : ℕ) (s t : Fin k), s ≠ t → ∀ G : WeightedGraph (Fin k),
    G.IsIntegral → (∀ u v, G.w u v ≤ M) →
      mass ((P k s t).eval G.cut) (fun S => ¬IsCanonicalSTCut G s t S) ≤ δ

theorem STPrograms.FailsAtMost.mono {Q : ℕ → ℕ} {P : STPrograms Q} {M : ℕ} {δ ε : ℝ≥0∞}
    (hP : P.FailsAtMost M δ) (h : δ ≤ ε) : P.FailsAtMost M ε :=
  fun k s t hst G hint hcap => (hP k s t hst G hint hcap).trans h

/-- A public randomized s-t family that returns the canonical shore with
probability at least 2/3. The deterministic `CanonicalSTFamily` is the
zero-error case (`CanonicalSTFamily.toRandom`). -/
structure RandomCanonicalSTFamily (M : ℕ) (Q : ℕ → ℕ) where
  program : STPrograms Q
  correct : program.FailsAtMost M (1 / 3)

/-- A deterministic exact family never fails. -/
def _root_.CutQueryComplexity.GHReduction.CanonicalSTFamily.toRandom {M : ℕ} {Q : ℕ → ℕ}
    (A : CanonicalSTFamily M Q) : RandomCanonicalSTFamily M Q where
  program k s t := RTree.ofDeterministic (A.program k s t)
  correct k s t hst G hint hcap := by
    simp [RTree.eval_ofDeterministic, A.correct k s t hst G hint hcap]

variable {V : Type}

/-- One run, followed by one query of the returned shore's value. -/
def valuedRun {q : ℕ} (T : RTree (Finset V) ℝ (Finset V) q) :
    RTree (Finset V) ℝ (Finset V × ℝ) (q + 1) :=
  T.bind (fun S => RTree.query S (fun a => RTree.pure (q := 0) (PMF.pure (S, a))))

theorem valuedRun_eval {q : ℕ} (T : RTree (Finset V) ℝ (Finset V) q) (read : Finset V → ℝ) :
    (valuedRun T).eval read = (T.eval read).map (fun S => (S, read S)) := by
  simp [valuedRun, PMF.map, Function.comp_def]

variable [Fintype V] [DecidableEq V]

/-- The valid candidates of least reported value, intersected. -/
def selectShore (s t : V) (L : List (Finset V × ℝ)) : Finset V :=
  let C := L.filter (fun p => s ∈ p.1 ∧ t ∉ p.1)
  (C.filter (fun p => ∀ p' ∈ C, p.2 ≤ p'.2)).foldr (fun p acc => p.1 ∩ acc) Finset.univ

theorem mem_foldr_inter {L : List (Finset V × ℝ)} {v : V} :
    v ∈ L.foldr (fun p acc => p.1 ∩ acc) Finset.univ ↔ ∀ p ∈ L, v ∈ p.1 := by
  induction L with
  | nil => simp
  | cons p L ih => simp [ih]

/-- If the reported values are the true cut values and one candidate is the
canonical shore, the selection returns it. -/
theorem selectShore_eq (G : WeightedGraph V) {s t : V} {L : List (Finset V × ℝ)}
    (hval : ∀ p ∈ L, p.2 = G.cut p.1) {p : Finset V × ℝ} (hp : p ∈ L)
    (hcan : IsCanonicalSTCut G s t p.1) : selectShore s t L = p.1 := by
  have hpC : p ∈ L.filter (fun p => s ∈ p.1 ∧ t ∉ p.1) := by
    simpa [List.mem_filter] using And.intro hp (And.intro hcan.1.1 hcan.1.2.1)
  ext v
  simp only [selectShore, mem_foldr_inter]
  constructor
  · intro hv
    apply hv p
    refine List.mem_filter.mpr ⟨hpC, ?_⟩
    simp only [decide_eq_true_eq]
    intro p' hp'
    obtain ⟨hp'L, hp'st⟩ := List.mem_filter.mp hp'
    simp only [decide_eq_true_eq] at hp'st
    rw [hval p hp, hval p' hp'L]
    exact hcan.1.2.2 p'.1 hp'st.1 hp'st.2
  · intro hv p' hp'
    obtain ⟨hp'C, hleast⟩ := List.mem_filter.mp hp'
    simp only [decide_eq_true_eq] at hleast
    obtain ⟨hp'L, hp'st⟩ := List.mem_filter.mp hp'C
    simp only [decide_eq_true_eq] at hp'st
    have hle : G.cut p'.1 ≤ G.cut p.1 := by
      rw [← hval p' hp'L, ← hval p hp]
      exact hleast p hpC
    have hmin : IsSTMinCut G s t p'.1 :=
      ⟨hp'st.1, hp'st.2, fun A hsA htA => hle.trans (hcan.1.2.2 A hsA htA)⟩
    exact hcan.2 p'.1 hmin hv

/-- `r` valued runs, then the selection. -/
def amplifiedRun {q : ℕ} (T : RTree (Finset V) ℝ (Finset V) q) (s t : V) (r : ℕ) :
    RTree (Finset V) ℝ (Finset V) (r * (q + 1)) :=
  (randomRepeat (valuedRun T) r).map (selectShore s t)

/-- The amplified run fails only if every one of the `r` runs failed. -/
theorem amplifiedRun_failure (G : WeightedGraph V) {q : ℕ}
    (T : RTree (Finset V) ℝ (Finset V) q) (s t : V) (r : ℕ) {δ : ℝ≥0∞}
    (hT : mass (T.eval G.cut) (fun S => ¬IsCanonicalSTCut G s t S) ≤ δ) :
    mass ((amplifiedRun T s t r).eval G.cut) (fun S => ¬IsCanonicalSTCut G s t S) ≤ δ ^ r := by
  have hbad : mass ((valuedRun T).eval G.cut) (fun p => ¬IsCanonicalSTCut G s t p.1) ≤ δ := by
    rw [valuedRun_eval, mass_map]
    exact hT
  rw [amplifiedRun, RTree.eval_map, mass_map]
  refine le_trans (mass_mono_on_support _ ?_) (randomRepeat_failure_le _ r G.cut _ hbad)
  intro L hL hfail p hp hcan
  have hval : ∀ p ∈ L, p.2 = G.cut p.1 := by
    intro p' hp'
    have h := randomRepeat_member _ r G.cut hL hp'
    rw [valuedRun_eval] at h
    obtain ⟨S, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp h
    rfl
  apply hfail
  rw [selectShore_eq G hval hp hcan]
  exact hcan

/-- Cost of `r` repetitions with value queries, padded so that size regularity
is preserved. -/
def amplifiedCost (r : ℕ) (Q : ℕ → ℕ) : ℕ → ℕ := fun k => r * (Q k + k)

/-- The amplified family. Every program has a terminal, so its size is positive
and the padding `r * (Q k + 1) ≤ r * (Q k + k)` is available. -/
def STPrograms.amplify {Q : ℕ → ℕ} (P : STPrograms Q) (r : ℕ) :
    STPrograms (amplifiedCost r Q) :=
  fun k s t => (amplifiedRun (P k s t) s t r).weaken (by
    have hk := s.pos
    show r * (Q k + 1) ≤ r * (Q k + k)
    exact Nat.mul_le_mul_left r (by omega))

theorem STPrograms.FailsAtMost.amplify {Q : ℕ → ℕ} {P : STPrograms Q} {M : ℕ} {δ : ℝ≥0∞}
    (hP : P.FailsAtMost M δ) (r : ℕ) : (P.amplify r).FailsAtMost M (δ ^ r) := by
  intro k s t hst G hint hcap
  simp only [STPrograms.amplify, RTree.eval_weaken]
  exact amplifiedRun_failure G _ s t r (hP k s t hst G hint hcap)

/-- The amplified family of a randomized canonical family fails with probability at most `3⁻¹ ^ r`. -/
theorem RandomCanonicalSTFamily.amplify_failsAtMost {M : ℕ} {Q : ℕ → ℕ}
    (family : RandomCanonicalSTFamily M Q) (r : ℕ) :
    (family.program.amplify r).FailsAtMost M (3⁻¹ ^ r) := by
  simpa only [one_div] using family.correct.amplify r

theorem sizeRegular_amplifiedCost {n : ℕ} {Q : ℕ → ℕ} (hQ : SizeRegular n Q) (r : ℕ) :
    SizeRegular n (amplifiedCost r Q) := by
  intro s hs hsn
  have h := hQ s hs hsn
  simp only [amplifiedCost]
  calc
    n * (r * (Q s + s)) = r * (n * Q s + n * s) := by ring
    _ ≤ r * (s * Q n + s * n) := by
      rw [Nat.mul_comm n s]
      exact Nat.mul_le_mul_left r (Nat.add_le_add_right h _)
    _ = s * (r * (Q n + n)) := by ring

/-- With at least one repetition, every call of positive size costs at least one query. -/
theorem one_le_amplifiedCost {r : ℕ} (hr : 1 ≤ r) (Q : ℕ → ℕ) {k : ℕ} (hk : 1 ≤ k) :
    1 ≤ amplifiedCost r Q k := by
  simp only [amplifiedCost]
  exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))

/-- Repetitions multiply the single-repetition cost. -/
theorem amplifiedCost_eq_mul (r : ℕ) (Q : ℕ → ℕ) (k : ℕ) :
    amplifiedCost r Q k = r * amplifiedCost 1 Q k := by
  simp [amplifiedCost]

end
end CutQueryComplexity.GHReduction.Randomized
