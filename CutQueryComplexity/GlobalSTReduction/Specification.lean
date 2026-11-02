import CutQueryComplexity.GHReduction.Randomized.Family

/-! # Real-weight s-t families and global success

The two primitives of the reduction act on undirected graphs with arbitrary
nonnegative real edge weights, on every compact vertex type `Fin k`:

* `RealSTFamily Q`: a deterministic program that returns *some* minimum s-t
  shore. It need not be inclusion-minimal, and it returns no flow or certificate;
* `RandomRealSTFamily Q`: a randomized program that misses a minimum s-t shore
  with probability at most `1/3` on every instance.

Neither family carries an integrality, capacity or total-weight promise.
`OptFailsAtMost P δ` is the per-instance failure bound that the reduction uses;
a deterministic family has `δ = 0` (`RealSTFamily.optFailsAtMost_zero`).

`GlobalSuccess G out` asks for a minimum proper shore and its exact cut value.
`ValidOutput G out` asks only for a proper shore and its exact value; the
reduction guarantees it on every execution.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GlobalSTReduction
noncomputable section
open scoped Classical ENNReal
open Probability GHReduction.Randomized

/-- A deterministic s-t minimum-cut family over real weights, fixed before the
hidden graph. Correctness is required only for distinct terminals. -/
structure RealSTFamily (Q : ℕ → ℕ) where
  program : ∀ k : ℕ, Fin k → Fin k →
    DTree (Finset (Fin k)) ℝ (Finset (Fin k)) (Q k)
  correct : ∀ (k : ℕ) (s t : Fin k), s ≠ t →
    ∀ G : WeightedGraph (Fin k),
      IsSTMinCut G s t ((program k s t).eval G.cut)

/-- A randomized s-t minimum-cut family over real weights that misses a minimum
shore with probability at most `1/3` on every instance with distinct terminals. -/
structure RandomRealSTFamily (Q : ℕ → ℕ) where
  program : ∀ k : ℕ, Fin k → Fin k →
    RTree (Finset (Fin k)) ℝ (Finset (Fin k)) (Q k)
  correct : ∀ (k : ℕ) (s t : Fin k), s ≠ t →
    ∀ G : WeightedGraph (Fin k),
      mass ((program k s t).eval G.cut)
        (fun S => ¬IsSTMinCut G s t S) ≤ (1 / 3 : ℝ≥0∞)

/-- On every instance with distinct terminals, the program misses a minimum s-t
shore with probability at most `δ`. Any minimum shore counts as a success. -/
def OptFailsAtMost {Q : ℕ → ℕ} (P : STPrograms Q) (δ : ℝ≥0∞) : Prop :=
  ∀ (k : ℕ) (s t : Fin k), s ≠ t → ∀ G : WeightedGraph (Fin k),
    mass ((P k s t).eval G.cut) (fun S => ¬IsSTMinCut G s t S) ≤ δ

theorem OptFailsAtMost.mono {Q : ℕ → ℕ} {P : STPrograms Q} {δ ε : ℝ≥0∞}
    (hP : OptFailsAtMost P δ) (h : δ ≤ ε) : OptFailsAtMost P ε :=
  fun k s t hst G => (hP k s t hst G).trans h

/-- A deterministic family, run as a randomized one with point masses. -/
def RealSTFamily.toPrograms {Q : ℕ → ℕ} (A : RealSTFamily Q) : STPrograms Q :=
  fun k s t => RTree.ofDeterministic (A.program k s t)

/-- A deterministic family never misses a minimum shore. -/
theorem RealSTFamily.optFailsAtMost_zero {Q : ℕ → ℕ} (A : RealSTFamily Q) :
    OptFailsAtMost A.toPrograms 0 := by
  intro k s t hst G
  simp [RealSTFamily.toPrograms, RTree.eval_ofDeterministic, A.correct k s t hst G]

theorem RandomRealSTFamily.optFailsAtMost {Q : ℕ → ℕ} (family : RandomRealSTFamily Q) :
    OptFailsAtMost family.program (1 / 3) :=
  family.correct

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A minimum proper shore together with its exact cut value. -/
def GlobalSuccess (G : WeightedGraph V) (out : Finset V × ℝ) : Prop :=
  IsMinCut G out.1 ∧ out.2 = G.cut out.1

/-- A proper shore together with its exact cut value. -/
def ValidOutput (G : WeightedGraph V) (out : Finset V × ℝ) : Prop :=
  ProperShore out.1 ∧ out.2 = G.cut out.1

end
end CutQueryComplexity.GlobalSTReduction
