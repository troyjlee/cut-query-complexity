import CutQueryComplexity.Search.Comp

/-! # Implementing each question by a subprogram

`Comp.subst f c` answers every question `q` of `c` by running the program `f q`
against another oracle. If each `f q` returns the answer `o q` and costs at most
`k`, the substituted program returns what `c` returns on `o` and costs at most
`k` times the cost of `c` on `o`.
-/

namespace CutQueryComplexity
namespace Search
namespace Comp

variable {Q Q' A A' β : Type}

/-- Replace every question by a subprogram computing its answer. -/
def subst (f : Q → Comp Q' A' A) : Comp Q A β → Comp Q' A' β
  | pure b => pure b
  | query q k => (f q).bind fun a => subst f (k a)

theorem eval_subst (f : Q → Comp Q' A' A) (o' : Q' → A') (o : Q → A)
    (h : ∀ q, (f q).eval o' = o q) (c : Comp Q A β) : (subst f c).eval o' = c.eval o := by
  induction c with
  | pure b => rfl
  | query q k ih => simp [subst, h, ih]

theorem cost_subst_le (f : Q → Comp Q' A' A) (o' : Q' → A') (o : Q → A)
    (h : ∀ q, (f q).eval o' = o q) {k : ℕ} (hk : ∀ q, (f q).cost o' ≤ k) (c : Comp Q A β) :
    (subst f c).cost o' ≤ k * c.cost o := by
  induction c with
  | pure b => simp [subst]
  | query q c ih =>
      simp only [subst, cost_bind, h, cost_query]
      have := ih (o q)
      have := hk q
      rw [Nat.mul_succ]
      omega

end Comp
end Search
end CutQueryComplexity
