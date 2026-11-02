import CutQueryComplexity.Model.RandomizedComposition

/-! # Conditional sampling with explicit absence -/

namespace CutQueryComplexity.Probability
noncomputable section
open scoped Classical ENNReal
variable {α β : Type} [Fintype α]

/-- Continue from a successful sample, propagating absence. -/
def bindOption (p : PMF (Option α)) (f : α → PMF (Option β)) : PMF (Option β) :=
  p.bind fun o => match o with
    | none => PMF.pure none
    | some a => f a

@[simp] theorem bindOption_some (p : PMF (Option α)) (f : α → PMF (Option β)) (b : β) :
    bindOption p f (some b) = ∑ a, p (some a) * f a (some b) := by
  simp [bindOption, PMF.bind_apply, PMF.pure_apply, tsum_fintype, Fintype.sum_option]

@[simp] theorem bindOption_none (p : PMF (Option α)) (f : α → PMF (Option β)) :
    bindOption p f none = p none + ∑ a, p (some a) * f a none := by
  simp [bindOption, PMF.bind_apply, PMF.pure_apply, tsum_fintype, Fintype.sum_option, add_comm]

@[simp] theorem bindOption_pure_none (f : α → PMF (Option β)) :
    bindOption (PMF.pure none) f = PMF.pure none := by simp [bindOption]

end
end CutQueryComplexity.Probability
