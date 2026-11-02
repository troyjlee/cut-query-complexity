import CutQueryComplexity.GHReduction.Randomized.CallProg
import CutQueryComplexity.Primitive.Learn

/-! # Plumbing for call programs

The analogues, for `CallProg`, of the `Prog` plumbing in `GHReduction/Programs.lean`
and of the call wrappers in `GHReduction/Specification.lean`:

* `ofProg` embeds a call-free `Prog`, so the family-free parts of the reduction
  are reused unchanged;
* `tableProgram` and `finiteTable` run a finite table of programs in order;
* `contract f` pulls every query and every call back along a public map. A call
  on the contracted instance becomes a call on `G` along the composed map;
* `canonicalCall s t` is one s-t call on a finite vertex type, through its compact
  relabeling. It is the twin of `canonicalSTProgram`.

Each comes with its ideal output and ideal charged cost. `canonicalSTProgram_eval_eq`
is the bridge at a single call: an exact family's inlined program evaluates to
the call's ideal answer on every promised graph.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction.Randomized
noncomputable section
open scoped Classical BigOperators
open WeightedGraph

/-- Two weighted graphs with the same cut function are equal. -/
theorem graph_eq_of_cut_eq {V : Type} [Fintype V] [DecidableEq V] {G H : WeightedGraph V}
    (h : G.cut = H.cut) : G = H := by
  rw [← reconstructionDecode_correct G, ← reconstructionDecode_correct H, h]

/-- Contracting twice is contracting along the composed map. -/
theorem contract_contract {V W B : Type} [Fintype V] [DecidableEq V] [Fintype W]
    [DecidableEq W] [Fintype B] [DecidableEq B] (G : WeightedGraph V) (f : V → W) (π : W → B) :
    (G.contract f).contract π = G.contract (fun v => π (f v)) :=
  graph_eq_of_cut_eq (funext (cut_contract_comp G f π))

/-- The input promise passes to every contraction. -/
theorem inputPromise_contract {V W : Type} [Fintype V] [DecidableEq V] [Fintype W]
    [DecidableEq W] {M : ℕ} (G : WeightedGraph V) (hG : InputPromise M G) (f : V → W) :
    InputPromise M (G.contract f) :=
  ⟨integral_contract G hG.1 f, (edgeMass_contract_le G f).trans hG.2⟩

namespace CallProg

variable {V W : Type} {α β : Type}

/-- A call-free program. -/
def ofProg : Prog (Finset V) ℝ α → CallProg V α
  | Prog.pure a => pure a
  | Prog.query S next => query S (fun x => ofProg (next x))

/-- A finite indexed table of outputs, run in order. -/
def tableProgram : (n : ℕ) → (Fin n → CallProg V α) → CallProg V (Fin n → α)
  | 0, _ => pure (fun i => Fin.elim0 i)
  | n + 1, p => (p 0).bind (fun o => (tableProgram n (fun i => p i.succ)).map (Fin.cases o))

/-- A table indexed by a finite type. -/
def finiteTable {D : Type} [Fintype D] (p : D → CallProg V α) : CallProg V (D → α) :=
  (tableProgram (Fintype.card D) (fun i => p ((Fintype.equivFin D).symm i))).map
    (fun f x => f ((Fintype.equivFin D) x))

@[simp] theorem pure_bind (a : α) (f : α → CallProg V β) : (pure a).bind f = f a := rfl

variable [Fintype V] [DecidableEq V]

attribute [simp] idealEval_bind idealCost_bind

@[simp] theorem idealEval_pure (G : WeightedGraph V) (a : α) :
    idealEval G (pure a : CallProg V α) = a := rfl

@[simp] theorem idealCost_pure (G : WeightedGraph V) (Q : ℕ → ℕ) (a : α) :
    idealCost G Q (pure a : CallProg V α) = 0 := rfl

@[simp] theorem idealEval_ask (G : WeightedGraph V) (S : Finset V) :
    idealEval G (ask S) = G.cut S := rfl

@[simp] theorem idealCost_ask (G : WeightedGraph V) (Q : ℕ → ℕ) (S : Finset V) :
    idealCost G Q (ask S) = 1 := rfl

@[simp] theorem idealEval_map (G : WeightedGraph V) (f : α → β) (p : CallProg V α) :
    idealEval G (p.map f) = f (idealEval G p) := by
  simp [map]

@[simp] theorem idealCost_map (G : WeightedGraph V) (Q : ℕ → ℕ) (f : α → β) (p : CallProg V α) :
    idealCost G Q (p.map f) = idealCost G Q p := by
  simp [map]

@[simp] theorem idealEval_ofProg (G : WeightedGraph V) (p : Prog (Finset V) ℝ α) :
    idealEval G (ofProg p) = Prog.eval G.cut p := by
  induction p with
  | pure a => rfl
  | query S next ih => exact ih _

@[simp] theorem idealCost_ofProg (G : WeightedGraph V) (Q : ℕ → ℕ) (p : Prog (Finset V) ℝ α) :
    idealCost G Q (ofProg p) = Prog.cost G.cut p := by
  induction p with
  | pure a => rfl
  | query S next ih =>
      simp only [ofProg, idealCost, prog_cost_query]
      rw [ih]

@[simp] theorem idealEval_tableProgram (G : WeightedGraph V) (n : ℕ) (p : Fin n → CallProg V α) :
    idealEval G (tableProgram n p) = fun i => idealEval G (p i) := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
      simp only [tableProgram, idealEval_bind, idealEval_map, ih]
      funext i
      cases i using Fin.cases <;> rfl

@[simp] theorem idealCost_tableProgram (G : WeightedGraph V) (Q : ℕ → ℕ) (n : ℕ)
    (p : Fin n → CallProg V α) :
    idealCost G Q (tableProgram n p) = ∑ i, idealCost G Q (p i) := by
  induction n with
  | zero => simp [tableProgram]
  | succ n ih => simp [tableProgram, ih, Fin.sum_univ_succ]

@[simp] theorem idealEval_finiteTable {D : Type} [Fintype D] (G : WeightedGraph V)
    (p : D → CallProg V α) : idealEval G (finiteTable p) = fun x => idealEval G (p x) := by
  simp [finiteTable]

@[simp] theorem idealCost_finiteTable {D : Type} [Fintype D] (G : WeightedGraph V) (Q : ℕ → ℕ)
    (p : D → CallProg V α) : idealCost G Q (finiteTable p) = ∑ x, idealCost G Q (p x) := by
  simp only [finiteTable, idealCost_map, idealCost_tableProgram]
  exact (Fintype.equivFin D).symm.sum_comp (fun x => idealCost G Q (p x))

variable [Fintype W] [DecidableEq W]

/-- Pull every query and call back along a public map. -/
def contract (f : V → W) : CallProg W α → CallProg V α
  | pure a => pure a
  | query S next => query (pull f S) (fun x => contract f (next x))
  | call k π s t hst next => call k (fun v => π (f v)) s t hst (fun S => contract f (next S))

@[simp] theorem idealEval_contract (G : WeightedGraph V) (f : V → W) (p : CallProg W α) :
    idealEval G (contract f p) = idealEval (G.contract f) p := by
  induction p with
  | pure a => rfl
  | query S next ih =>
      simp only [contract, idealEval, ih, cut_contract]
  | call k π s t hst next ih =>
      simp only [contract, idealEval, ih, contract_contract]

@[simp] theorem idealCost_contract (G : WeightedGraph V) (Q : ℕ → ℕ) (f : V → W)
    (p : CallProg W α) : idealCost G Q (contract f p) = idealCost (G.contract f) Q p := by
  induction p with
  | pure a => rfl
  | query S next ih =>
      simp only [contract, idealCost, ih, cut_contract]
  | call k π s t hst next ih =>
      simp only [contract, idealCost, ih, contract_contract]

/-- One canonical s-t call on `W`, through its compact relabeling. -/
def canonicalCall (s t : W) (hst : s ≠ t) : CallProg W (Finset W) :=
  call (Fintype.card W) (Fintype.equivFin W) (Fintype.equivFin W s) (Fintype.equivFin W t)
    ((Fintype.equivFin W).injective.ne hst) (fun S => pure (pull (Fintype.equivFin W) S))

/-- The ideal answer of a canonical call is the canonical shore. -/
theorem idealEval_canonicalCall (G : WeightedGraph W) {s t : W} (hst : s ≠ t) :
    IsCanonicalSTCut G s t (idealEval G (canonicalCall s t hst)) :=
  canonicalSTCut_equiv_pull G (Fintype.equivFin W)
    (idealShore_spec _ ((Fintype.equivFin W).injective.ne hst))

@[simp] theorem idealCost_canonicalCall (G : WeightedGraph W) (Q : ℕ → ℕ) {s t : W}
    (hst : s ≠ t) : idealCost G Q (canonicalCall s t hst) = Q (Fintype.card W) := by
  simp [canonicalCall, idealCost]

/-- Bridge at one call: on a promised graph, an exact family's inlined program
returns the call's ideal answer. -/
theorem canonicalSTProgram_eval_eq {M : ℕ} {QA : ℕ → ℕ} (A : CanonicalSTFamily M QA)
    (G : WeightedGraph W) (hG : InputPromise M G) {s t : W} (hst : s ≠ t) :
    (canonicalSTProgram A s t).eval G.cut = idealEval G (canonicalCall s t hst) :=
  canonicalSTCut_unique G (canonicalSTProgram_correct A G hG hst) (idealEval_canonicalCall G hst)

end CallProg
end
end CutQueryComplexity.GHReduction.Randomized
