import CutQueryComplexity.Model.RandomizedComposition
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Fintype.Prod

/-! # Forgetting the orientation of a sampled edge -/

namespace CutQueryComplexity.Probability
noncomputable section
open scoped Classical ENNReal
variable {V : Type} [Fintype V]

/-- Retain the original endpoints as an unordered pair; preserve absence. -/
def forgetOrientation (p : PMF (Option (V × V))) : PMF (Option (Sym2 V)) :=
  p.map (Option.map fun uv => s(uv.1, uv.2))

@[simp] theorem forgetOrientation_none (p : PMF (Option (V × V))) :
    forgetOrientation p none = p none := by
  simp [forgetOrientation, PMF.map_apply, tsum_fintype, Fintype.sum_option]

/-- Distinct endpoints have exactly two oriented preimages. -/
theorem forgetOrientation_some (p : PMF (Option (V × V))) {u v : V} (hne : u ≠ v) :
    forgetOrientation p (some s(u, v)) = p (some (u, v)) + p (some (v, u)) := by
  have hp : (u, v) ≠ (v, u) := fun h => hne (congrArg Prod.fst h)
  have hterm (ab : V × V) :
      (if s(ab.1, ab.2) = s(u, v) then p (some ab) else 0) =
        (if ab = (u, v) then p (some (u, v)) else 0) +
        (if ab = (v, u) then p (some (v, u)) else 0) := by
    by_cases h : ab = (u, v)
    · subst ab; simp [hp]
    · by_cases h' : ab = (v, u)
      · subst ab; simp [h, Sym2.eq_swap]
      · have hs : s(ab.1, ab.2) ≠ s(u, v) := by
          intro hs
          rcases Sym2.eq_iff.mp hs with he | he
          · exact h (Prod.ext he.1 he.2)
          · exact h' (Prod.ext he.1 he.2)
        simp [h, h', hs]
  simp only [forgetOrientation, PMF.map_apply, tsum_fintype, Fintype.sum_option,
    Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq, ite_false,
    zero_add, add_zero]
  simp only [eq_comm (a := s(u, v)), hterm, Finset.sum_add_distrib]
  simp

theorem forgetOrientation_diag (p : PMF (Option (V × V))) (u : V) :
    forgetOrientation p (some s(u, u)) = p (some (u, u)) := by
  simp [forgetOrientation, PMF.map_apply, tsum_fintype, Fintype.sum_option,
    Sym2.mk_eq_mk_iff]

@[simp] theorem forgetOrientation_pure_none :
    forgetOrientation (PMF.pure (none : Option (V × V))) = PMF.pure none := by
  simp [forgetOrientation, PMF.pure_map]

end
end CutQueryComplexity.Probability
