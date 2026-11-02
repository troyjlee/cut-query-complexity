import CutQueryComplexity.DetMinCut.Unconditional
import CutQueryComplexity.Model.Composition

/-! # Exact shore-and-value outputs for the existing global algorithm

The unconditional global solver already returns an optimum shore.  One
additional original cut query returns its exact numerical value.  The tree
and its budget are selected before the hidden graph, and the budget holds
for every answer function.
-/

set_option autoImplicit false

namespace CutQueryComplexity.UndirectedClosure

variable {V : Type}

/-- A final original query measures the selected shore. -/
def queryShoreValue : Option (Finset V) →
    DTree (Finset V) ℝ (Option (Finset V × ℝ)) 1
  | none => DTree.pure none
  | some S => DTree.query S (fun value => DTree.pure (some (S, value)))

/-- Attach a value to any public shore tree with one further query available. -/
def withShoreValue {q : ℕ} (D : DTree (Finset V) ℝ (Option (Finset V)) q) :
    DTree (Finset V) ℝ (Option (Finset V × ℝ)) (q + 1) := D.bind queryShoreValue

theorem withShoreValue_eval {q : ℕ} (D : DTree (Finset V) ℝ (Option (Finset V)) q)
    (read : Finset V → ℝ) :
    (withShoreValue D).eval read = (D.eval read).map (fun S => (S, read S)) := by
  change (DTree.run read (D.bind queryShoreValue)).1 = _
  rw [DTree.run_bind]
  cases D.eval read <;> rfl

theorem withShoreValue_cost {q : ℕ} (D : DTree (Finset V) ℝ (Option (Finset V)) q)
    (read : Finset V → ℝ) :
    (withShoreValue D).cost read = D.cost read + if (D.eval read).isSome then 1 else 0 := by
  change (DTree.run read (D.bind queryShoreValue)).2 = _
  rw [DTree.run_bind]
  cases D.eval read <;> rfl

theorem withShoreValue_cost_le {q : ℕ}
    (D : DTree (Finset V) ℝ (Option (Finset V)) q) (read : Finset V → ℝ) :
    (withShoreValue D).cost read ≤ q + 1 := DTree.cost_le _ _

/-- The existing unconditional global algorithm, now with both an optimum
shore and its exact value. No hierarchy or guard premise remains. -/
theorem deterministic_mincut_shore_value_log5 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ q : ℕ, (q : ℝ) ≤ C * (n : ℝ) * (Nat.sqrt n + 1) *
          (DetMinCut.logL n : ℝ) ^ 5 ∧
        ∃ D : DTree (Finset (Fin n)) ℝ (Option (Finset (Fin n) × ℝ)) q,
          (∀ read, D.cost read ≤ q) ∧
          ∀ G : WeightedGraph (Fin n), ∃ S,
            D.eval G.cut = some (S, mincutValue G) ∧ IsMinCut G S := by
  obtain ⟨C, hC, hsolve⟩ := DetMinCut.deterministic_mincut_log5
  refine ⟨C + 1, by linarith, fun n hn => ?_⟩
  obtain ⟨q, hq, D, hD⟩ := hsolve n hn
  refine ⟨q + 1, ?_, withShoreValue D, fun read => DTree.cost_le _ read, ?_⟩
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hs1 : (1 : ℝ) ≤ (Nat.sqrt n : ℝ) + 1 := by
      linarith [Nat.cast_nonneg (α := ℝ) (Nat.sqrt n)]
    have hL1 : (1 : ℝ) ≤ (DetMinCut.logL n : ℝ) :=
      by exact_mod_cast DetMinCut.one_le_logL' n
    have hbase : (1 : ℝ) ≤ (n : ℝ) * (Nat.sqrt n + 1) *
        (DetMinCut.logL n : ℝ) ^ 5 :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hn1 hs1)
        (one_le_pow₀ hL1)
    push_cast
    nlinarith
  · intro G
    obtain ⟨S, heval, hS⟩ := hD G
    refine ⟨S, ?_, hS⟩
    rw [withShoreValue_eval, heval]
    simp only [Option.map_some, DetMinCut.isMinCut_of_sat hS]

#print axioms withShoreValue_eval
#print axioms withShoreValue_cost
#print axioms withShoreValue_cost_le
#print axioms deterministic_mincut_shore_value_log5

end CutQueryComplexity.UndirectedClosure
