import CutQueryComplexity.DetMinCut.SafePartition
import CutQueryComplexity.DetMinCut.Phase
import CutQueryComplexity.Hierarchy.Existence

/-! # Explicit tree cut sparsifiers and safe quotient outputs

The output contains numerical capacities. Correctness relates this data to the
unknown graph; the graph itself is not an input to the query program.
-/

set_option autoImplicit false

namespace CutQueryComplexity.TreeCutSparsifier

open WeightedGraph Search Search.Comp Hierarchy DetMinCut Finset

variable {V : Type} [Fintype V] [DecidableEq V]

structure TreeData (V : Type) where
  tree : Pkg V
  cap : Fin tree.m → ℝ
  cap_nonneg : ∀ x, 0 ≤ cap x

/-- The terminal cuts of the explicit tree approximate every cut of `G`. -/
structure TreeData.Good (G : WeightedGraph V) (α : ℝ) (out : TreeData V) : Prop where
  size : out.tree.m ≤ 8 * Fintype.card V
  leaves : out.tree.H.LeafChildless
  canonical : out.cap = out.tree.H.canon G
  cuts : ∀ S, G.cut S ≤ out.tree.H.rep out.cap S ∧
    out.tree.H.rep out.cap S ≤ α * G.cut S

theorem TreeData.Good.mono {G : WeightedGraph V} {α β : ℝ} {out : TreeData V}
    (h : out.Good G α) (hab : α ≤ β) : out.Good G β :=
  ⟨h.size, h.leaves, h.canonical, fun S => ⟨(h.cuts S).1,
    (h.cuts S).2.trans (mul_le_mul_of_nonneg_right hab (G.cut_nonneg S))⟩⟩

structure Output (V : Type) [Fintype V] [DecidableEq V] where
  r : V → V
  data : TreeData (Cls r)

def Correct (G : WeightedGraph V) (α : ℝ) (out : Output V) : Prop :=
  SafePartition G out.r ∧ out.data.Good (quot G out.r) α

theorem Correct.size {G : WeightedGraph V} {α : ℝ} {out : Output V}
    (h : Correct G α out) : out.data.tree.m ≤ 8 * Fintype.card V := by
  have hc : Fintype.card (Cls out.r) ≤ Fintype.card V := by
    rw [card_cls]
    exact card_image_le.trans (by simp)
  exact h.2.size.trans (Nat.mul_le_mul_left 8 hc)

/-- Learn canonical capacities, including the zero root capacity. -/
noncomputable def learnTree (P : Pkg V) : Comp (Finset V) ℝ (TreeData V) :=
  (tabulate (fun x => ask (P.H.cluster x)) univ.toList).map fun values =>
    ⟨P, fun x => max 0 ((values x).getD 0), fun _ => le_max_left _ _⟩

noncomputable def canonicalTree (P : Pkg V) (G : WeightedGraph V) : TreeData V :=
  ⟨P, P.H.canon G, fun _ => G.cut_nonneg _⟩

theorem learnTree_eval (P : Pkg V) (G : WeightedGraph V) :
    (learnTree P).eval G.cut = canonicalTree P G := by
  simp only [learnTree, eval_map, eval_tabulate, eval_ask, mem_toList, mem_univ,
    ↓reduceIte, Option.getD_some, max_eq_right (G.cut_nonneg _)]
  rfl

omit [DecidableEq V] in
theorem learnTree_cost (P : Pkg V) (read : Finset V → ℝ) :
    (learnTree P).cost read = P.m := by
  simp [learnTree, cost_map, cost_tabulate, cost_ask]

theorem canonicalTree_good (P : Pkg V) (G : WeightedGraph V) {α : ℝ}
    (hm : P.m ≤ 8 * Fintype.card V) (hl : P.H.LeafChildless)
    (hd : ∀ S, P.H.rep (P.H.canon G) S ≤ α * G.cut S) :
    (canonicalTree P G).Good G α :=
  ⟨hm, hl, rfl, fun S => ⟨P.H.cut_le_rep G S, hd S⟩⟩

/-- The fixed offline hierarchy distortion. -/
def distortion (n : ℕ) : ℝ := 1690 * (logL n : ℝ)^2

theorem distortion_one (n : ℕ) : 1 ≤ distortion n := by
  have h : (1 : ℝ) ≤ (logL n : ℝ)^2 :=
    one_le_pow₀ (by exact_mod_cast one_le_logL' n)
  unfold distortion
  linarith

theorem hierarchyBound : HierarchyBound distortion (fun n => 4 * logL n) :=
  exists_hierarchyBound_sq

theorem distortion_mono : Monotone distortion := by
  intro m n hmn
  have h : (logL m : ℝ) ≤ logL n := by exact_mod_cast logL_mono hmn
  unfold distortion
  gcongr

end CutQueryComplexity.TreeCutSparsifier
