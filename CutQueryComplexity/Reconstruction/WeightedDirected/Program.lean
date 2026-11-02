import CutQueryComplexity.Reconstruction.DirectedData
import CutQueryComplexity.Primitive.Learn
import CutQueryComplexity.Model.RandomizedComposition

/-! Exact quadratic reconstruction of arbitrary real nonnegative directed cuts.
Only symmetrized capacities and imbalances are recovered; arc orientations are
not determined by outgoing cuts. Every query schedule and decoder is public. -/
namespace CutQueryComplexity.Reconstruction.WeightedDirected

open Finset DirectedCertificate
open scoped Classical
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Singletons, complementary singletons, and ordered pairs. -/
abbrev QueryIndex (V : Type) := V ⊕ (V ⊕ (V × V))

def queryBudget (V : Type) [Fintype V] : ℕ := Fintype.card (QueryIndex V)

def schedule : QueryIndex V → Finset V
  | .inl v => {v}
  | .inr (.inl v) => {v}ᶜ
  | .inr (.inr (u, v)) => {u, v}

/-- Symmetrize and clip inconsistent real replies so every branch is total. -/
def publicSym (a : QueryIndex V → ℝ) : WeightedGraph V where
  w u v := if u = v then 0 else
    max 0 (a (.inl u) + a (.inl v) -
      (a (.inr (.inr (u, v))) + a (.inr (.inr (v, u)))) / 2)
  symm u v := by simp only [eq_comm]; congr 2; ring
  nonneg u v := by split <;> simp
  diag v := by simp

def publicData (a : QueryIndex V → ℝ) : DirectedData V :=
  ⟨publicSym a, fun v => a (.inl v) - a (.inr (.inl v))⟩

theorem publicSym_correct (G : WeightedDiGraph V) :
    publicSym (fun i : QueryIndex V => G.out (schedule i)) = G.sym := by
  ext u v
  by_cases huv : u = v
  · subst v; simp [publicSym, G.diag]
  · have hp : ({v, u} : Finset V) = {u, v} := by ext x; simp [or_comm]
    simp only [publicSym, ite_eq_right huv, schedule, hp]
    have he := G.sym_w_eq_three_outs huv
    have hn := G.sym.nonneg u v
    have ha : G.out {u} + G.out {v} - (G.out {u, v} + G.out {u, v}) / 2 =
        G.sym.w u v := by rw [he]; ring
    rw [ha, max_eq_right hn]

theorem publicData_correct (G : WeightedDiGraph V) :
    publicData (fun i : QueryIndex V => G.out (schedule i)) =
      (⟨G.sym, G.imbalance⟩ : DirectedData V) := by
  have hi : (fun v => G.out {v} - G.out {v}ᶜ) = G.imbalance := by
    funext v
    rw [G.out_singleton, G.out_compl_singleton]
    rfl
  change DirectedData.mk _ _ = _
  rw [publicSym_correct]
  congr 1

/-- One actual fixed schedule, independent of the hidden weighted digraph. -/
def reconstruct : DTree (Finset V) ℝ (DirectedData V) (queryBudget V) :=
  (DTree.queryAll schedule (fun _ : QueryIndex V => (0 : ℝ))).map publicData

theorem reconstruct_run (read : Finset V → ℝ) :
    DTree.run read (reconstruct (V := V)) =
      (publicData (fun i => read (schedule i)), queryBudget V) := by
  simp [reconstruct, DTree.run_map, DTree.queryAll_run, queryBudget]

theorem reconstruct_correct (G : WeightedDiGraph V) :
    (reconstruct (V := V)).eval G.out = (⟨G.sym, G.imbalance⟩ : DirectedData V) := by
  simp [DTree.eval, reconstruct_run, publicData_correct]

theorem reconstruct_cut_correct (G : WeightedDiGraph V) (S : Finset V) :
    ((reconstruct (V := V)).eval G.out).cut S = G.out S := by
  rw [reconstruct_correct]
  exact DirectedData.cut_correct _ G rfl rfl S

omit [DecidableEq V] in
theorem queryBudget_eq : queryBudget V = Fintype.card V ^ 2 + 2 * Fintype.card V := by
  simp [queryBudget, QueryIndex, Fintype.card_sum, Fintype.card_prod]
  ring

theorem reconstruct_cost (read : Finset V → ℝ) :
    (reconstruct (V := V)).cost read = Fintype.card V ^ 2 + 2 * Fintype.card V := by
  simp [DTree.cost, reconstruct_run, queryBudget_eq]

omit [DecidableEq V] in
theorem queryBudget_quadratic (hn : 1 ≤ Fintype.card V) :
    queryBudget V ≤ 3 * Fintype.card V ^ 2 := by
  rw [queryBudget_eq]
  nlinarith

end
end CutQueryComplexity.Reconstruction.WeightedDirected
