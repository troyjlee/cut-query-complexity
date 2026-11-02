import CutQueryComplexity.Model.RandomizedComposition

/-! # Dependent sampling with an explicit absence outcome -/
namespace CutQueryComplexity.Probability
noncomputable section
open scoped Classical ENNReal
variable {α β : Type} [Fintype α] [Fintype β]

/-- Preserve the first endpoint when sampling the second, propagating absence. -/
def pairSample (p : PMF (Option α)) (f : α → PMF (Option β)) : PMF (Option (α × β)) :=
  p.bind fun o => match o with
    | none => PMF.pure none
    | some a => (f a).map (Option.map (fun b => (a, b)))

@[simp] theorem pairSample_some (p : PMF (Option α)) (f : α → PMF (Option β)) (a : α) (b : β) :
    pairSample p f (some (a, b)) = p (some a) * f a (some b) := by
  simp [pairSample, PMF.bind_apply, PMF.map_apply, PMF.pure_apply,
    tsum_fintype, Fintype.sum_option, ite_and, Finset.mul_sum, eq_comm]

@[simp] theorem pairSample_none (p : PMF (Option α)) (f : α → PMF (Option β)) :
    pairSample p f none = p none + ∑ a, p (some a) * f a none := by
  simp [pairSample, PMF.bind_apply, PMF.map_apply, PMF.pure_apply,
    tsum_fintype, Fintype.sum_option, add_comm]

end
end CutQueryComplexity.Probability
