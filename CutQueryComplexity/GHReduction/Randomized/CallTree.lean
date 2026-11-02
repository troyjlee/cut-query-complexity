import CutQueryComplexity.GHReduction.Randomized.Family

/-! # Randomized programs with explicit s-t calls

`CallTree V Q O q` is a randomized program over the cut oracle of a graph on `V`
whose s-t calls are explicit nodes. The index `q` is the budget: a cut query
consumes one unit, and a call on `k` vertices consumes `Q k`. A call node names
a public contraction `π : V → Fin k` and two distinct terminals of `Fin k`, and
continues with the returned shore of `Fin k`. The call is not implemented here:
`Interpret.lean` gives the randomized, deterministic and ideal meanings.

The `random` node draws from a `PMF` over any type, so `CallTree` lives in
`Type 1`. The `up` node raises the budget without any query; it gives budget
weakening and casts.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction.Randomized

/-- Budgeted randomized programs with cut queries and s-t calls. -/
inductive CallTree (V : Type) (Q : ℕ → ℕ) (O : Type) : ℕ → Type 1 where
  /-- Return an output. -/
  | ret : O → CallTree V Q O 0
  /-- Ask the cut value of a vertex set. -/
  | query {q : ℕ} : Finset V → (ℝ → CallTree V Q O q) → CallTree V Q O (q + 1)
  /-- Ask for the canonical s-t shore of the contraction along `π`. -/
  | call {q : ℕ} (k : ℕ) (π : V → Fin k) (s t : Fin k) (hst : s ≠ t) :
      (Finset (Fin k) → CallTree V Q O q) → CallTree V Q O (q + Q k)
  /-- Draw a public random choice at no query cost. -/
  | random {q : ℕ} {ι : Type} : PMF ι → (ι → CallTree V Q O q) → CallTree V Q O q
  /-- Raise the budget. -/
  | up {q r : ℕ} : q ≤ r → CallTree V Q O q → CallTree V Q O r

namespace CallTree

variable {V : Type} {Q : ℕ → ℕ} {O P : Type}

/-- Draw an output without using the oracle. -/
def pure (p : PMF O) : CallTree V Q O 0 := random p ret

/-- Budget weakening. -/
def weaken {q r : ℕ} (h : q ≤ r) (T : CallTree V Q O q) : CallTree V Q O r := up h T

/-- Reindex the budget by an equality. -/
def cast {q r : ℕ} (h : q = r) (T : CallTree V Q O q) : CallTree V Q O r := up h.le T

/-- Run the second program selected by the output of the first. -/
def bind {r : ℕ} (f : O → CallTree V Q P r) : {q : ℕ} → CallTree V Q O q → CallTree V Q P (q + r)
  | _, ret o => up (by omega) (f o)
  | _, query S next => up (by omega) (query S (fun a => bind f (next a)))
  | _, call k π s t hst next => up (by omega) (call k π s t hst (fun S => bind f (next S)))
  | _, random μ next => random μ (fun i => bind f (next i))
  | _, up h T => up (by omega) (bind f T)

/-- Free postprocessing of the output. -/
def map {q : ℕ} (f : O → P) (T : CallTree V Q O q) : CallTree V Q P q :=
  (T.bind (fun o => ret (f o))).cast (Nat.add_zero q)

/-- A call-free randomized tree, as a call tree with the same budget. -/
def ofRTree : {q : ℕ} → RTree (Finset V) ℝ O q → CallTree V Q O q
  | 0, T => random T ret
  | _ + 1, T => random T (fun action => match action with
      | Sum.inl o => up (Nat.zero_le _) (ret o)
      | Sum.inr (S, next) => query S (fun a => ofRTree (next a)))

end CallTree
end CutQueryComplexity.GHReduction.Randomized
