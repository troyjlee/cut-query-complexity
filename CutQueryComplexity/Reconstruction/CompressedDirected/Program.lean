import CutQueryComplexity.DirectedCertificate.Basic
import CutQueryComplexity.StarContraction2022.Recovery.Decode

/-!
# Compressed reconstruction of the outgoing-cut function of a unit digraph

The fixed finite alphabet is `{0,1,2}` for symmetrized capacities. A public
separating family learns each symmetrized row from the three-outgoing-cut star
identity, sharing the singleton answers. Complementary singletons give the
imbalances. No individual directed orientation is reconstructed.
-/

set_option autoImplicit false

namespace CutQueryComplexity.Reconstruction.CompressedDirected

open Finset DirectedCertificate
open scoped Classical
noncomputable section
open StarContraction2022

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Both input and certificate competitor arcs are restricted to 0 or 1. -/
def Unit (G : WeightedDiGraph V) : Prop := ∀ u v, G.c u v = 0 ∨ G.c u v = 1

/-- The alphabet bound is fixed, independent of the vertex count. -/
def family (V : Type) [Fintype V] [DecidableEq V] : Finset (Finset V) :=
  Recovery.denseFamily V 2

abbrev Index (V : Type) [Fintype V] [DecidableEq V] :=
  (V × Bool) ⊕ ((V × ↥(family V)) × Bool)

/-- Singleton/complement singletons and the two remaining star shores. -/
def shore : Index V → Finset V
  | .inl (v, false) => {v}
  | .inl (v, true) => {v}ᶜ
  | .inr ((v, S), false) => S.val.erase v
  | .inr ((v, S), true) => insert v S.val

def budget (V : Type) [Fintype V] [DecidableEq V] : ℕ :=
  2 * Fintype.card V + 2 * Fintype.card V * (family V).card

theorem index_card : Fintype.card (Index V) = budget V := by
  simp [Index, budget, Fintype.card_prod, Fintype.card_sum]
  ring

/-- Natural decoding is total on arbitrary real replies. -/
def measurements (a : Index V → ℝ) (v : V) (S : ↥(family V)) : ℕ :=
  ⌊a (.inl (v, false)) + a (.inr ((v,S),false)) - a (.inr ((v,S),true))⌋₊

/-- Exhaustive decoding over the fixed finite box, with a zero fallback. -/
def row (a : Index V → ℝ) (v : V) : V → ℕ :=
  (Recovery.decode (Recovery.box V 2) (family V) (measurements a v)).getD (fun _ => 0)

/-- Valid undirected output on all replies, including inconsistent replies. -/
def decodeSym (a : Index V → ℝ) : WeightedGraph V where
  w u v := if u = v then 0 else ((row a u v : ℝ) + row a v u) / 2
  symm u v := by
    by_cases h : u = v
    · subst v; rfl
    · simp [h, Ne.symm h, add_comm]
  nonneg u v := by split <;> positivity
  diag v := by simp

def decodeImbalance (a : Index V → ℝ) (v : V) : ℝ :=
  a (.inl (v,false)) - a (.inl (v,true))

/-- Literal public schedule, independent of the hidden graph. -/
def program : DTree (Finset V) ℝ (WeightedGraph V × (V → ℝ)) (budget V) :=
  ((DTree.queryAll shore (fun _ => (0 : ℝ))).map
    (fun a => (decodeSym a, decodeImbalance a))).cast index_card

def arcNat (G : WeightedDiGraph V) (u v : V) : ℕ := if G.c u v = 1 then 1 else 0

def symRow (G : WeightedDiGraph V) (v u : V) : ℕ := arcNat G v u + arcNat G u v

theorem arcNat_cast (G : WeightedDiGraph V) (hG : Unit G) (u v : V) :
    (arcNat G u v : ℝ) = G.c u v := by
  rcases hG u v with h | h <;> simp [arcNat, h]

theorem symRow_cast (G : WeightedDiGraph V) (hG : Unit G) (u v : V) :
    (symRow G u v : ℝ) = G.sym.w u v := by
  simp [symRow, arcNat_cast G hG, WeightedDiGraph.sym_w]

theorem symRow_le (G : WeightedDiGraph V) (u v : V) : symRow G u v ≤ 2 := by
  unfold symRow arcNat
  split <;> split <;> omega

theorem measurements_correct (G : WeightedDiGraph V) (hG : Unit G) (v : V) :
    measurements (fun i => G.out (shore i)) v = Recovery.signature (family V) (symRow G v) := by
  funext S
  have he : G.symStar v S.val = ((Recovery.measure S.val (symRow G v) : ℕ) : ℝ) := by
    simp only [WeightedDiGraph.symStar, Recovery.measure, Nat.cast_sum, symRow_cast G hG]
  simp only [measurements, shore, ← G.symStar_eq_erase, he, Nat.floor_natCast,
    Recovery.signature]

theorem row_correct (G : WeightedDiGraph V) (hG : Unit G) (v : V) :
    row (fun i => G.out (shore i)) v = symRow G v := by
  rw [row, measurements_correct G hG]
  have he := Recovery.box_decode (fun u => symRow_le G v u)
  change Recovery.decode (Recovery.box V 2) (family V)
    (Recovery.signature (family V) (symRow G v)) = some (symRow G v) at he
  rw [he]
  rfl

theorem decodeSym_correct (G : WeightedDiGraph V) (hG : Unit G) :
    decodeSym (fun i => G.out (shore i)) = G.sym := by
  ext u v
  change (if u = v then 0 else _) = _
  by_cases h : u = v
  · subst v; simp [G.diag]
  · rw [if_neg h, row_correct G hG, row_correct G hG,
      symRow_cast G hG, symRow_cast G hG, G.sym.symm v u]
    ring

theorem decodeImbalance_correct (G : WeightedDiGraph V) :
    decodeImbalance (fun i => G.out (shore i)) = G.imbalance := by
  funext v
  simp [decodeImbalance, shore, G.out_singleton, G.out_compl_singleton,
    WeightedDiGraph.imbalance]

/-- Exact output and actual query count of this one public program. -/
theorem program_run (G : WeightedDiGraph V) (hG : Unit G) :
    DTree.run G.out (program (V := V)) = ((G.sym, G.imbalance), budget V) := by
  simp only [program, DTree.run_cast, DTree.run_map, DTree.queryAll_run,
    decodeSym_correct G hG, decodeImbalance_correct G, index_card]

/-- Every real-answer execution obeys the same literal budget. -/
theorem program_cost (oracle : Finset V → ℝ) : (program (V := V)).cost oracle = budget V := by
  simp only [program, DTree.cost, DTree.run_cast, DTree.run_map, DTree.queryAll_run,
    index_card]

/-- Explicit `O(n²/log(2n))` envelope, with natural logarithms. -/
theorem budget_bound (hn : 1 ≤ Fintype.card V) :
    (budget V : ℝ) ≤ (4 + 32768 * Real.log 3) * (Fintype.card V : ℝ)^2 /
      Real.log (2 * (Fintype.card V : ℝ)) := by
  have hf := Recovery.denseFamily_card_bound V 2 hn (by omega)
  change ((family V).card : ℝ) ≤ _ at hf
  norm_num only [Nat.cast_ofNat] at hf
  have hnR : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hlog : 0 < Real.log (2 * (Fintype.card V : ℝ)) := Real.log_pos (by linarith)
  have hlogle := Real.log_le_sub_one_of_pos (show 0 < 2 * (Fintype.card V : ℝ) by positivity)
  have hmul := mul_le_mul_of_nonneg_left hf (show 0 ≤ 2 * (Fintype.card V : ℝ) by positivity)
  unfold budget
  push_cast
  apply (le_div_iff₀ hlog).mpr
  have hmul' := (le_div_iff₀ hlog).mp (show
    2 * (Fintype.card V : ℝ) * ((family V).card : ℝ) ≤
      (32768 * (Fintype.card V : ℝ)^2 * Real.log 3) /
        Real.log (2 * (Fintype.card V : ℝ)) by
    convert hmul using 1 <;> ring)
  nlinarith [mul_nonneg (show 0 ≤ 2 * (Fintype.card V : ℝ) by positivity)
    (show 0 ≤ 2 * (Fintype.card V : ℝ) - Real.log (2 * (Fintype.card V : ℝ)) by linarith)]

end
end CutQueryComplexity.Reconstruction.CompressedDirected
