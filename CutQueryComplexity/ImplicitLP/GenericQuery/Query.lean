import CutQueryComplexity.ImplicitLP.GenericQuery.Rows

/-! # Executed general transpose and repaired Newton query programs

The arbitrary explicit rows are evaluated offline. The only oracle operations
are the hidden RHS aggregate, the actual frozen solver, and the repair aggregate.
Their tree indices bound every answer oracle, including unsuccessful replies.
-/

set_option autoImplicit false

namespace CutQueryComplexity.ImplicitLP.GenericQuery

open Matrix Finset Spectral
noncomputable section
variable {n m : ℕ}

/-- The hidden divergence query plus the arbitrary public explicit transpose. -/
def transposeProg (E : ExplicitRows n m) (x : Point n m) (e : ℤ) (B : ℕ) :
    DTree (Finset (Fin n)) ℕ (Fin n → ℝ) (6 * B * n) :=
  (divProg x.pair e B).map fun y => y + knownTranspose E x

theorem transposeProg_eval (G : DiGraph (Fin n)) (E : ExplicitRows n m) (x : Point n m)
    (e : ℤ) (B : ℕ)
    (hg : ∀ u v, ∃ z : ℤ, x.pair u v = z * (2 : ℝ) ^ e)
    (hB : ∀ u v, |x.pair u v| < (2 : ℝ) ^ B * (2 : ℝ) ^ e) :
    (transposeProg E x e B).eval G.out = (matrix G E)ᵀ *ᵥ vec G x := by
  rw [transposeProg, DTree.eval_map, divProg, DTree.eval_cast,
    hiddenDiv_exact G x.pair e B (antiForm_grid hg) (antiForm_bound (by positivity) hB),
    transpose_vec]

theorem transposeProg_cost (E : ExplicitRows n m) (x : Point n m) (e : ℤ) (B : ℕ)
    (read : Finset (Fin n) → ℕ) :
    (transposeProg E x e B).cost read ≤ 6 * B * n := DTree.cost_le _ _

/-- A public per-pair weight with an arbitrary explicit vector. -/
def weights (wf : Sym2 (Fin n) → ℝ) (de : Fin m → ℝ) : Point n m :=
  Point.mk (fun u v => wf s(u, v)) de

theorem weights_hidden (G : DiGraph (Fin n)) (wf : Sym2 (Fin n) → ℝ) (de : Fin m → ℝ)
    (i : Fin (rowCount G m)) (e : Sym2 (Fin n)) (hi : hidden G m i = some e) :
    vec G (weights wf de) i = wf e := by
  simp only [hidden] at hi
  simp only [vec]
  generalize (rowEquiv G m).symm i = r at hi ⊢
  rcases r with ⟨p, k⟩ | j
  · simp only [hiddenRow, Option.some.injEq] at hi
    subst hi
    rfl
  · simp [hiddenRow] at hi

def rawDirection (E : ExplicitRows n m) (wf : Sym2 (Fin n) → ℝ) (de : Fin m → ℝ)
    (q : Point n m) (y : Fin n → ℝ) : Point n m :=
  -weights wf de * (q - rowProduct E y)

theorem rawDirection_vec (G : DiGraph (Fin n)) (E : ExplicitRows n m)
    (wf : Sym2 (Fin n) → ℝ) (de : Fin m → ℝ) (q : Point n m) (y : Fin n → ℝ) :
    (fun i => -vec G (weights wf de) i * (vec G q i - (matrix G E *ᵥ y) i)) =
      vec G (rawDirection E wf de q y) := by
  rw [matrix_mulVec]
  rfl

/-- Actual finite RHS/solve/repair composition; no hidden enumeration is a parameter. -/
def newtonStepProg (E : ExplicitRows n m) (wf : Sym2 (Fin n) → ℝ) (de : Fin m → ℝ)
    (q : Point n m) (out : Sym2 (Fin n) → ℝ) (ew eq : ℤ) (p Brhs Bmv Brep k : ℕ) :
    DTree (Finset (Fin n)) ℕ (Point n m)
      (6 * Brhs * n + (k * (6 * Bmv * n) + 6 * Brep * n)) :=
  (transposeProg E (weights wf de * q) (ew + eq) Brhs).bind fun b =>
    (frozenSolveProg wf ew p Bmv (knownGram E de) (lap out univ + knownGram E de)⁻¹ b k
      0).bind fun y =>
      (transposeProg E (rawDirection E wf de q y) (ew + eq) Brep).map fun rho =>
        repairPoint E (rawDirection E wf de q y) rho

/-- The executed program's cost on every answer function, with explicit rows free. -/
theorem newtonStepProg_cost (E : ExplicitRows n m) (wf : Sym2 (Fin n) → ℝ) (de : Fin m → ℝ)
    (q : Point n m) (out : Sym2 (Fin n) → ℝ) (ew eq : ℤ) (p Brhs Bmv Brep k : ℕ)
    (read : Finset (Fin n) → ℕ) :
    (newtonStepProg E wf de q out ew eq p Brhs Bmv Brep k).cost read ≤
      6 * n * (Brhs + k * Bmv + Brep) :=
  (DTree.cost_le _ _).trans (le_of_eq (by ring))

/-- Grid-licensed execution is exactly the algebraic repaired direction.
The local bit bounds will be discharged by the public numerical envelopes. -/
theorem newtonStepProg_eval (G : DiGraph (Fin n)) (E : ExplicitRows n m)
    (wf : Sym2 (Fin n) → ℝ) (de : Fin m → ℝ) (q : Point n m)
    (out : Sym2 (Fin n) → ℝ) (ew eq : ℤ) (p Brhs Bmv Brep k : ℕ)
    (hwg : ∀ e, ∃ z : ℤ, wf e = z * (2 : ℝ) ^ ew)
    (hqg : ∀ u v, ∃ z : ℤ, q.pair u v = z * (2 : ℝ) ^ eq) (heq : eq ≤ -(p : ℤ))
    (hrhs : ∀ u v, |wf s(u, v) * q.pair u v| < (2 : ℝ) ^ Brhs * (2 : ℝ) ^ (ew + eq)) :
    let A := matrix G E
    let Dh := vec G (weights wf de)
    let b : Fin n → ℝ := Aᵀ *ᵥ fun i => Dh i * vec G q i
    let P := lap out univ + explicitGram A Dh (hidden G m)
    let y := (frozenSolveProg wf ew p Bmv (explicitGram A Dh (hidden G m)) P⁻¹ b k 0).eval G.out
    (∀ u v, |wf s(u, v) * (q.pair u v - (y u - y v))| <
      (2 : ℝ) ^ Brep * (2 : ℝ) ^ (ew + eq)) →
    vec G ((newtonStepProg E wf de q out ew eq p Brhs Bmv Brep k).eval G.out) =
      repairDir A (iota G E) (fun i => -Dh i * (vec G q i - (A *ᵥ y) i)) := by
  intro A Dh b P y hrep
  have hE : explicitGram A Dh (hidden G m) = knownGram E de :=
    explicitGram_eq G E (weights wf de)
  have hb : (transposeProg E (weights wf de * q) (ew + eq) Brhs).eval G.out = b := by
    exact transposeProg_eval G E (weights wf de * q) (ew + eq) Brhs
      (fun u v => mul_grid (hwg s(u, v)) (hqg u v)) hrhs
  have hy : (frozenSolveProg wf ew p Bmv (knownGram E de) (lap out univ + knownGram E de)⁻¹
      b k 0).eval G.out = y := by
    simp only [y, P, hE]
  have hyg := frozenSolveProg_grid G wf ew p Bmv (knownGram E de)
    (lap out univ + knownGram E de)⁻¹ b k 0 (fun _ => ⟨0, by simp⟩)
  rw [hy] at hyg
  have hhg : ∀ u v, ∃ z : ℤ, (rawDirection E wf de q y).pair u v =
      z * (2 : ℝ) ^ (ew + eq) := fun u v => by
    change ∃ z : ℤ, -wf s(u, v) * (q.pair u v - (y u - y v)) = z * (2 : ℝ) ^ (ew + eq)
    rw [neg_mul]
    exact neg_grid (mul_grid (hwg _) (sub_grid (hqg u v)
      (sub_grid (grid_of_le heq (hyg u)) (grid_of_le heq (hyg v)))))
  have hhB : ∀ u v, |(rawDirection E wf de q y).pair u v| <
      (2 : ℝ) ^ Brep * (2 : ℝ) ^ (ew + eq) := fun u v => by
    change |-wf s(u, v) * (q.pair u v - (y u - y v))| < _
    rw [neg_mul, abs_neg]
    exact hrep u v
  simp only [newtonStepProg, DTree.eval_bind, DTree.eval_map]
  rw [hb, hy, vec_repairPoint, transposeProg_eval G E _ _ _ hhg hhB, ← rawDirection_vec]
  rfl

/-- The same actual execution gives an exactly feasible direction. -/
theorem newtonStepProg_feasible (G : DiGraph (Fin n)) (E : ExplicitRows n m)
    (wf : Sym2 (Fin n) → ℝ) (de : Fin m → ℝ) (q : Point n m)
    (out : Sym2 (Fin n) → ℝ) (ew eq : ℤ) (p Brhs Bmv Brep k : ℕ)
    (hwg : ∀ e, ∃ z : ℤ, wf e = z * (2 : ℝ) ^ ew)
    (hqg : ∀ u v, ∃ z : ℤ, q.pair u v = z * (2 : ℝ) ^ eq) (heq : eq ≤ -(p : ℤ))
    (hrhs : ∀ u v, |wf s(u, v) * q.pair u v| < (2 : ℝ) ^ Brhs * (2 : ℝ) ^ (ew + eq)) :
    let b := (matrix G E)ᵀ *ᵥ vec G (weights wf de * q)
    let y := (frozenSolveProg wf ew p Bmv (knownGram E de)
      (lap out univ + knownGram E de)⁻¹ b k 0).eval G.out
    (∀ u v, |wf s(u, v) * (q.pair u v - (y u - y v))| <
      (2 : ℝ) ^ Brep * (2 : ℝ) ^ (ew + eq)) →
    (matrix G E)ᵀ *ᵥ vec G ((newtonStepProg E wf de q out ew eq p Brhs Bmv Brep k).eval G.out) = 0 := by
  intro b y hrep
  have heval := newtonStepProg_eval G E wf de q out ew eq p Brhs Bmv Brep k hwg hqg heq hrhs
  dsimp only at heval
  rw [explicitGram_eq] at heval
  have heval' := heval hrep
  rw [heval']
  exact repair_feasible (matrix_idRows G E) _

#print axioms transposeProg_eval
#print axioms transposeProg_cost
#print axioms newtonStepProg_cost
#print axioms newtonStepProg_eval
#print axioms newtonStepProg_feasible

end
end CutQueryComplexity.ImplicitLP.GenericQuery
