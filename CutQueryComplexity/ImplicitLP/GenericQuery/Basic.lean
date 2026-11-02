import CutQueryComplexity.ImplicitLP.PublicParams

/-! # Public data and semantic rows for general incidence LPs

Executable points are public ordered-pair formulas and an explicit vector.
Only the semantic row type and its interpretation depend on the unknown graph.
Hidden copies all use the canonical orientation `u < v`.
-/

set_option autoImplicit false

namespace CutQueryComplexity.ImplicitLP.GenericQuery

open Matrix Finset Spectral
noncomputable section

/-- Public coordinate indices; no edge set or multiplicity is an input. -/
abbrev Index (n m : ℕ) := (Fin n × Fin n) ⊕ Fin m
abbrev Point (n m : ℕ) := Index n m → ℝ

variable {n m : ℕ}

namespace Point

def mk (z : Fin n → Fin n → ℝ) (x : Fin m → ℝ) : Point n m :=
  Sum.elim (fun p => z p.1 p.2) x

def pair (x : Point n m) (u v : Fin n) : ℝ := x (.inl (u, v))
def explicit (x : Point n m) (j : Fin m) : ℝ := x (.inr j)
def map (f : ℝ → ℝ) (x : Point n m) : Point n m := fun i => f (x i)

@[simp] theorem pair_mk (z : Fin n → Fin n → ℝ) (x : Fin m → ℝ) (u v : Fin n) :
    (mk z x).pair u v = z u v := rfl
@[simp] theorem explicit_mk (z : Fin n → Fin n → ℝ) (x : Fin m → ℝ) (j : Fin m) :
    (mk z x).explicit j = x j := rfl
@[simp] theorem mk_eta (x : Point n m) : mk x.pair x.explicit = x := by
  funext i
  cases i <;> rfl

end Point

/-- Public arbitrary explicit rows, including a designated positive identity block. -/
structure ExplicitRows (n m : ℕ) where
  matrix : Matrix (Fin m) (Fin n) ℝ
  iota : Fin n → Fin m
  identity : IdRows matrix iota

/-- Original input data. No run, oracle, optimum or cost certificate is a field. -/
structure Data (n m : ℕ) where
  rows : ExplicitRows n m
  lower : Point n m
  upper : Point n m
  cost : Point n m
  initial : Point n m
  rhs : Fin n → ℝ

/-- Graph-dependent row copies, used in semantics only. -/
abbrev Row (G : DiGraph (Fin n)) (m : ℕ) :=
  (Σ p : CPair n, Fin (G.sym p.1.1 p.1.2)) ⊕ Fin m

abbrev rowCount (G : DiGraph (Fin n)) (m : ℕ) := Fintype.card (Row G m)
def rowEquiv (G : DiGraph (Fin n)) (m : ℕ) : Row G m ≃ Fin (rowCount G m) :=
  Fintype.equivFin _

def rowIndex {G : DiGraph (Fin n)} : Row G m → Index n m
  | .inl ⟨p, _⟩ => .inl p.1
  | .inr j => .inr j

def hiddenRow {G : DiGraph (Fin n)} : Row G m → Option (Sym2 (Fin n))
  | .inl ⟨p, _⟩ => some s(p.1.1, p.1.2)
  | .inr _ => none

def hidden (G : DiGraph (Fin n)) (m : ℕ) : Fin (rowCount G m) → Option (Sym2 (Fin n)) :=
  fun i => hiddenRow ((rowEquiv G m).symm i)

/-- Interpretation of a public formula, with equal values on all copies of a pair. -/
def vec (G : DiGraph (Fin n)) (x : Point n m) : Fin (rowCount G m) → ℝ :=
  fun i => x (rowIndex ((rowEquiv G m).symm i))

@[simp] theorem vec_map (G : DiGraph (Fin n)) (f : ℝ → ℝ) (x : Point n m) :
    vec G (x.map f) = fun i => f (vec G x i) := rfl
@[simp] theorem vec_add (G : DiGraph (Fin n)) (x y : Point n m) :
    vec G (x + y) = vec G x + vec G y := rfl
@[simp] theorem vec_sub (G : DiGraph (Fin n)) (x y : Point n m) :
    vec G (x - y) = vec G x - vec G y := rfl
@[simp] theorem vec_smul (G : DiGraph (Fin n)) (a : ℝ) (x : Point n m) :
    vec G (a • x) = a • vec G x := rfl
@[simp] theorem vec_mul (G : DiGraph (Fin n)) (x y : Point n m) :
    vec G (x * y) = vec G x * vec G y := rfl
@[simp] theorem vec_zero (G : DiGraph (Fin n)) : vec G (0 : Point n m) = 0 := rfl

@[simp] theorem vec_explicit (G : DiGraph (Fin n)) (x : Point n m) (j : Fin m) :
    vec G x (rowEquiv G m (.inr j)) = x.explicit j := by
  simp [vec, rowIndex, Point.explicit]

theorem vec_hidden (G : DiGraph (Fin n)) (x : Point n m) (i : Fin (rowCount G m))
    (e : Sym2 (Fin n)) (h : hidden G m i = some e) :
    vec G x i = pairOf x.pair e := by
  simp only [hidden] at h
  simp only [vec]
  generalize (rowEquiv G m).symm i = r at h ⊢
  rcases r with ⟨p, k⟩ | j
  · simp only [hiddenRow, Option.some.injEq] at h
    subst h
    exact (pairOf_mk_lt x.pair p.2).symm
  · simp [hiddenRow] at h

theorem copy_eq (G : DiGraph (Fin n)) (x : Point n m)
    {i j : Fin (rowCount G m)} {e : Sym2 (Fin n)}
    (hi : hidden G m i = some e) (hj : hidden G m j = some e) :
    vec G x i = vec G x j :=
  (vec_hidden G x i e hi).trans (vec_hidden G x j e hj).symm

theorem hidden_count (G : DiGraph (Fin n)) (m : ℕ) (e : Sym2 (Fin n)) :
    (univ.filter fun i => hidden G m i = some e).card = Spanner.symS G e := by
  -- transport to the row type
  have h1 : (univ.filter fun i => hidden G m i = some e).card =
      (univ.filter fun x : Row G m => hiddenRow x = some e).card := by
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    exact Fintype.card_congr ((rowEquiv G m).symm.subtypeEquiv fun _ => Iff.rfl)
  -- only hidden rows of the pair `e` count
  rw [h1, card_filter, Fintype.sum_sum_type]
  simp only [hiddenRow, reduceCtorEq, ite_false, sum_const_zero, add_zero, Option.some.injEq]
  rw [Fintype.sum_sigma]
  -- `Σ_{p : u < v} [s(u,v) = e] · sym(u,v) = symS G e`
  induction e using Sym2.ind with
  | h a b =>
      rw [Spanner.symS_mk]
      rcases lt_trichotomy a b with hab | rfl | hab
      · rw [sum_eq_single ⟨(a, b), hab⟩]
        · simp
        · rintro ⟨⟨c, d⟩, hcd⟩ _ hne
          refine sum_eq_zero fun _ _ => ?_
          simp only [ite_eq_right_iff]
          intro h; exfalso
          rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hne rfl
          · exact absurd hab (not_lt.mpr hcd.le)
        · simp
      · rw [DiGraph.sym_self]
        refine sum_eq_zero fun ⟨⟨c, d⟩, hcd⟩ _ => ?_
        refine sum_eq_zero fun _ _ => ?_
        simp only [ite_eq_right_iff]
        intro h; exfalso
        rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact lt_irrefl _ hcd
      · rw [sum_eq_single ⟨(b, a), hab⟩]
        · simp [Sym2.eq_swap, G.sym_comm]
        · rintro ⟨⟨c, d⟩, hcd⟩ _ hne
          refine sum_eq_zero fun _ _ => ?_
          simp only [ite_eq_right_iff]
          intro h; exfalso
          rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact absurd hab (not_lt.mpr hcd.le)
          · exact hne rfl
        · simp

/-- Exact row count; it is never an executable input. -/
theorem rowCount_eq (G : DiGraph (Fin n)) (m : ℕ) :
    rowCount G m = (∑ p : CPair n, G.sym p.1.1 p.1.2) + m := by
  simp [rowCount, Fintype.card_sum, Fintype.card_sigma]

#print axioms vec_hidden
#print axioms copy_eq
#print axioms hidden_count
#print axioms rowCount_eq

end
end CutQueryComplexity.ImplicitLP.GenericQuery
