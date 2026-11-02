import CutQueryComplexity.Problem.Basic
import CutQueryComplexity.Model.Composition

/-! # Public counts and verified cut results

Every constructor below takes only public data or an observed answer. The hidden
graph occurs only in the soundness statements. Rejecting an invalid count does
not require deciding whether an entire transcript comes from a graph.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022

noncomputable section
open scoped Classical

/-- A simple unit-capacity input, with a finite natural cut alphabet. -/
abbrev SimpleInput (V : Type) := CapacityGraph V 1

/-- Decode one observed real as an integer in a public finite range. -/
def validateCount (bound : ℕ) (answer : ℝ) : Option (Fin (bound + 1)) :=
  if h : ∃ k : Fin (bound + 1), ((k : ℕ) : ℝ) = answer then
    some (Classical.choose h)
  else none

theorem validateCount_spec {bound : ℕ} {answer : ℝ} {k : Fin (bound + 1)}
    (h : validateCount bound answer = some k) :
    ((k : ℕ) : ℝ) = answer ∧ (k : ℕ) ≤ bound := by
  unfold validateCount at h
  split_ifs at h with hex
  · have hk : Classical.choose hex = k := Option.some.inj h
    rw [← hk]
    exact ⟨Classical.choose_spec hex, Nat.le_of_lt_succ (Classical.choose hex).isLt⟩

@[simp] theorem validateCount_of_fin (bound : ℕ) (k : Fin (bound + 1)) :
    validateCount bound ((k : ℕ) : ℝ) = some k := by
  have hex : ∃ j : Fin (bound + 1), ((j : ℕ) : ℝ) = ((k : ℕ) : ℝ) := ⟨k, rfl⟩
  rw [validateCount, dif_pos hex]
  congr 1
  apply Fin.ext
  exact_mod_cast Classical.choose_spec hex

theorem validateCount_of_nat (bound k : ℕ) (hk : k ≤ bound) :
    validateCount bound (k : ℝ) = some ⟨k, Nat.lt_succ_of_le hk⟩ :=
  validateCount_of_fin bound ⟨k, Nat.lt_succ_of_le hk⟩

theorem validateCount_reject {bound : ℕ} {answer : ℝ}
    (h : answer < 0 ∨ (bound : ℝ) < answer) :
    validateCount bound answer = none := by
  cases he : validateCount bound answer with
  | none => rfl
  | some k =>
      obtain ⟨hk, hkb⟩ := validateCount_spec he
      have hk0 : (0 : ℝ) ≤ (k : ℕ) := Nat.cast_nonneg _
      have hkbR : ((k : ℕ) : ℝ) ≤ bound := by exact_mod_cast hkb
      rcases h with h | h <;> linarith

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Honest singleton answers satisfy the range needed before taking logarithms. -/
theorem singleton_count_le (G : SimpleInput V) (v : V) :
    G.cut {v} ≤ Fintype.card V - 1 := by
  calc
    G.cut {v} = ∑ u ∈ ({v}ᶜ : Finset V), (G.w v u : ℕ) := by
      simp [CapacityGraph.cut]
    _ ≤ ∑ _u ∈ ({v}ᶜ : Finset V), (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro u _
      have := (G.w v u).isLt
      omega
    _ = Fintype.card V - 1 := by simp [Finset.card_compl]

theorem validate_singleton (G : SimpleInput V) (v : V) :
    validateCount (Fintype.card V - 1) (G.toWeighted.cut {v}) =
      some ⟨G.cut {v}, Nat.lt_succ_of_le (singleton_count_le G v)⟩ := by
  rw [CapacityGraph.toWeighted_cut]
  exact validateCount_of_nat _ _ (singleton_count_le G v)

/-- Public output data. Soundness is deliberately not stored in this structure. -/
structure CutResult (V : Type) where
  shore : Finset V
  value : ℝ

namespace CutResult

/-- A proper shore and its exact observed original cut value. -/
def Sound (out : CutResult V) (G : WeightedGraph V) : Prop :=
  ProperShore out.shore ∧ out.value = G.cut out.shore

theorem Sound.mincut_le {out : CutResult V} {G : WeightedGraph V}
    (h : out.Sound G) : mincutValue G ≤ out.value := by
  rw [h.2]
  exact mincutValue_le G h.1

end CutResult

/-- Test properness offline and, if it passes, query the original value once. -/
def verifyShore (S : Finset V) :
    DTree (Finset V) ℝ (Option (CutResult V)) 1 :=
  if ProperShore S then
    DTree.query S fun answer => DTree.pure (some ⟨S, answer⟩)
  else DTree.pure none

@[simp] theorem verifyShore_eval (S : Finset V) (read : Finset V → ℝ) :
    (verifyShore S).eval read =
      if ProperShore S then some ⟨S, read S⟩ else none := by
  by_cases h : ProperShore S <;> simp [verifyShore, h]

theorem verifyShore_sound (G : WeightedGraph V) (S : Finset V)
    {out : CutResult V} (h : (verifyShore S).eval G.cut = some out) :
    out.Sound G := by
  rw [verifyShore_eval] at h
  split_ifs at h with hS
  · have hout : (⟨S, G.cut S⟩ : CutResult V) = out := Option.some.inj h
    rw [← hout]
    exact ⟨hS, rfl⟩

theorem verifyShore_cost (S : Finset V) (read : Finset V → ℝ) :
    (verifyShore S).cost read ≤ 1 := DTree.cost_le _ _

/-- Keep the best verified candidate; failure preserves the prior result. -/
def retain (old : CutResult V) (candidate : Option (CutResult V)) : CutResult V :=
  match candidate with
  | none => old
  | some out => if out.value < old.value then out else old

@[simp] theorem retain_none (old : CutResult V) : retain old none = old := rfl

theorem retain_value_le (old : CutResult V) (candidate : Option (CutResult V)) :
    (retain old candidate).value ≤ old.value := by
  cases candidate with
  | none => exact le_rfl
  | some out =>
      simp only [retain]
      split_ifs with h
      · exact h.le
      · exact le_rfl

theorem retain_sound {G : WeightedGraph V} {old : CutResult V}
    {candidate : Option (CutResult V)} (hold : old.Sound G)
    (hnew : ∀ out, candidate = some out → out.Sound G) :
    (retain old candidate).Sound G := by
  cases candidate with
  | none => exact hold
  | some out =>
      have hout := hnew out rfl
      simp only [retain]
      split_ifs <;> assumption

/-- A failed internal solver cannot undo a verified optimum. -/
theorem retain_preserves_minimum {G : WeightedGraph V} {old : CutResult V}
    {candidate : Option (CutResult V)} (hold : old.Sound G)
    (hnew : ∀ out, candidate = some out → out.Sound G)
    (hmin : old.value = mincutValue G) :
    (retain old candidate).value = mincutValue G := by
  apply le_antisymm
  · exact (retain_value_le old candidate).trans_eq hmin
  · exact (retain_sound hold hnew).mincut_le

/-- Verified singleton initialization, including the case of minimum value zero. -/
theorem singleton_result_sound (G : WeightedGraph V) (v : V)
    (hn : 2 ≤ Fintype.card V) :
    (⟨{v}, G.cut {v}⟩ : CutResult V).Sound G :=
  ⟨properShore_singleton v hn, rfl⟩

#print axioms validateCount_spec
#print axioms validate_singleton
#print axioms verifyShore_sound
#print axioms verifyShore_cost
#print axioms retain_sound
#print axioms retain_preserves_minimum

end
end CutQueryComplexity.StarContraction2022
