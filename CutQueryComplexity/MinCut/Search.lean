import CutQueryComplexity.Problem.Basic

/-! # Search results

A search result is `Option (ℝ × Finset V)`: a value and a shore. It is *sound* for
`G` when every reported shore is proper and its value is its cut. It *covers* a
number `t` when its value is at most `t`. `bestR` keeps the smaller of two results;
it preserves soundness and covers whatever either argument covers.
-/

namespace CutQueryComplexity
namespace CutSearch

noncomputable section
open scoped Classical
variable {V : Type} [Fintype V]

abbrev Res (V : Type) := Option (ℝ × Finset V)

def Sound (G : WeightedGraph V) (r : Res V) : Prop := ∀ x ∈ r, ProperShore x.2 ∧ x.1 = G.cut x.2

def Covers (r : Res V) (t : ℝ) : Prop := ∃ x ∈ r, x.1 ≤ t

def bestR : Res V → Res V → Res V
  | none, b => b
  | some x, none => some x
  | some x, some y => if y.1 < x.1 then some y else some x

theorem sound_bestR {G : WeightedGraph V} {a b : Res V} (ha : Sound G a) (hb : Sound G b) :
    Sound G (bestR a b) := by
  intro x hx
  rcases a with _ | a <;> rcases b with _ | b
  · simp [bestR] at hx
  · exact hb x hx
  · exact ha x hx
  · simp only [bestR] at hx
    split_ifs at hx
    · exact hb x hx
    · exact ha x hx

omit [Fintype V] in
theorem covers_bestR_left {a b : Res V} {t : ℝ} (h : Covers a t) : Covers (bestR a b) t := by
  obtain ⟨x, hx, hxt⟩ := h
  rcases a with _ | a
  · simp at hx
  · obtain rfl : a = x := Option.some_inj.mp hx
    rcases b with _ | b
    · exact ⟨a, rfl, hxt⟩
    · simp only [bestR]
      split_ifs with hlt
      · exact ⟨b, rfl, by linarith⟩
      · exact ⟨a, rfl, hxt⟩

omit [Fintype V] in
theorem covers_bestR_right {a b : Res V} {t : ℝ} (h : Covers b t) : Covers (bestR a b) t := by
  obtain ⟨x, hx, hxt⟩ := h
  rcases b with _ | b
  · simp at hx
  · obtain rfl : b = x := Option.some_inj.mp hx
    rcases a with _ | a
    · exact ⟨b, rfl, hxt⟩
    · simp only [bestR]
      split_ifs with hlt
      · exact ⟨b, rfl, hxt⟩
      · exact ⟨a, rfl, by push Not at hlt; linarith⟩

theorem sound_none (G : WeightedGraph V) : Sound G (none : Res V) := by simp [Sound]

end
end CutSearch
end CutQueryComplexity
