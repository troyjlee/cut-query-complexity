import CutQueryComplexity.Hierarchy.GuardConstant
import CutQueryComplexity.Hierarchy.Existence.Majority

/-! # From retraction distributions to cut guards (log-seven plan, Milestone 6, transfer)

A *terminal-fixing map* (retraction) of a hierarchy is `f : N → V` with `f (leaf v) = v`. It
pushes each tree edge `x` (below `parent x`) onto the terminal pair `f x, f (parent x)` with
capacity `cap x`, giving the graph `J_f = pushGraph` on the terminals. For a finite
distribution `p` over retractions, `J = ∑_f p_f J_f` (`mixGraph`).

* **Lower bound** (`rep_le_cut_pushGraph`, `rep_le_cut_mixGraph`): pulling the labels of `S`
  back through `f` is an extension of `S` of cost exactly `c_{J_f}(S)`, so
  `R(S) ≤ c_{J_f}(S)`; averaging gives `R(S) ≤ c_J(S)`.
* **Upper bound** (`cut_mixGraph_le`): if `c_J(cluster x) ≤ ρ₀ cap x` for every tree edge `x`
  — the expected load of `x` when each `J_f` edge is routed along its tree path — then
  `c_J(S) ≤ ρ₀ R(S)`, by `cut_le_labelCost` at a minimizing extension. No flow argument is
  used.

`RetractionBound ρ₀` states that such a distribution exists for every hierarchy with
childless leaves, every nonnegative capacity function, and a nonempty terminal set.
`constantCutGuard_of_retractionBound` derives `ConstantCutGuard ρ₀`; the empty terminal set,
where no retraction exists, is handled directly.
-/

namespace CutQueryComplexity
namespace Hierarchy

open WeightedGraph Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The indicator of the ordered pair `(a, b)` being one orientation of the pair `{u, w}`,
for `u ≠ w`. -/
def pairInd (a b u w : V) : ℝ :=
  if u ≠ w then (if a = u ∧ b = w then 1 else 0) + (if a = w ∧ b = u then 1 else 0) else 0

omit [Fintype V] in
theorem pairInd_symm (a b u w : V) : pairInd a b u w = pairInd b a u w := by
  unfold pairInd
  split_ifs <;> simp_all

omit [Fintype V] in
theorem pairInd_diag (a u w : V) : pairInd a a u w = 0 := by
  unfold pairInd
  by_cases h : u = w
  · simp [h]
  · rw [ite_eq_left h, ite_eq_right (fun hh => h (hh.1.symm.trans hh.2)),
      ite_eq_right (fun hh => h (hh.2.symm.trans hh.1)), add_zero]

omit [Fintype V] in
theorem pairInd_nonneg (a b u w : V) : 0 ≤ pairInd a b u w := by
  unfold pairInd; split_ifs <;> norm_num

/-- Summing the pair indicator over a cut. -/
theorem sum_pairInd (S : Finset V) (u w : V) :
    ∑ a ∈ S, ∑ b ∈ Sᶜ, pairInd a b u w = if (u ∈ S) = (w ∈ S) then 0 else 1 := by
  by_cases huw : u = w
  · subst huw; simp [pairInd]
  have h1 : ∀ T : Finset V, ∑ a ∈ S, ∑ b ∈ T, (if a = u ∧ b = w then (1 : ℝ) else 0) =
      if u ∈ S ∧ w ∈ T then 1 else 0 := by
    intro T
    simp only [ite_and, sum_ite_irrel, sum_const_zero, sum_ite_eq']
  have h2 : ∀ T : Finset V, ∑ a ∈ S, ∑ b ∈ T, (if a = w ∧ b = u then (1 : ℝ) else 0) =
      if w ∈ S ∧ u ∈ T then 1 else 0 := by
    intro T
    simp only [ite_and, sum_ite_irrel, sum_const_zero, sum_ite_eq']
  simp only [pairInd, ite_eq_left huw, sum_add_distrib, h1, h2, mem_compl]
  by_cases hu : u ∈ S <;> by_cases hw : w ∈ S <;> simp [hu, hw]

namespace Hier

variable {N : Type} [Fintype N] [DecidableEq N]

/-- A terminal-fixing map. -/
def Fixing (H : Hier V N) (f : N → V) : Prop := ∀ v, f (H.leaf v) = v

/-- The terminal graph of a retraction: each tree edge `x` becomes the pair
`f x, f (parent x)` with capacity `cap x` (loops are dropped). -/
noncomputable def pushGraph (H : Hier V N) (cap : N → ℝ) (hcap : ∀ x, 0 ≤ cap x) (f : N → V) :
    WeightedGraph V where
  w a b := ∑ x ∈ H.edges, cap x * pairInd a b (f x) (f (H.T.parent x))
  symm a b := sum_congr rfl fun x _ => by rw [pairInd_symm]
  nonneg a b := sum_nonneg fun x _ => mul_nonneg (hcap x) (pairInd_nonneg _ _ _ _)
  diag a := by simp [pairInd_diag]

/-- The cut of `J_f`: the capacity of the tree edges whose endpoints `f` sends to different
sides of `S`. -/
theorem cut_pushGraph (H : Hier V N) (cap : N → ℝ) (hcap : ∀ x, 0 ≤ cap x) (f : N → V)
    (S : Finset V) :
    (H.pushGraph cap hcap f).cut S =
      ∑ x ∈ H.edges, if (f x ∈ S) = (f (H.T.parent x) ∈ S) then 0 else cap x := by
  show ∑ a ∈ S, ∑ b ∈ Sᶜ, ∑ x ∈ H.edges, cap x * pairInd a b (f x) (f (H.T.parent x)) = _
  rw [sum_congr rfl fun a _ => sum_comm, sum_comm]
  refine sum_congr rfl fun x _ => ?_
  simp_rw [← mul_sum]
  rw [sum_pairInd]
  split_ifs <;> simp

/-- **Lower bound for one retraction.** -/
theorem rep_le_cut_pushGraph (H : Hier V N) (cap : N → ℝ) (hcap : ∀ x, 0 ≤ cap x)
    {f : N → V} (hf : H.Fixing f) (S : Finset V) :
    H.rep cap S ≤ (H.pushGraph cap hcap f).cut S := by
  have hext : H.Extends S fun y => decide (f y ∈ S) := fun v => by simp [hf v]
  refine (H.rep_le cap hext).trans (le_of_eq ?_)
  rw [labelCost_toReal_bool, cut_pushGraph]
  refine sum_congr rfl fun x _ => ?_
  by_cases h1 : f x ∈ S <;> by_cases h2 : f (H.T.parent x) ∈ S <;> simp [h1, h2]

/-- The mixture `J = ∑_f p_f J_f` over a finite family of retractions. -/
noncomputable def mixGraph (H : Hier V N) (cap : N → ℝ) (hcap : ∀ x, 0 ≤ cap x)
    (F : Finset (N → V)) (p : (N → V) → ℝ) (hp : ∀ f ∈ F, 0 ≤ p f) : WeightedGraph V where
  w a b := ∑ f ∈ F, p f * (H.pushGraph cap hcap f).w a b
  symm a b := sum_congr rfl fun f _ => by rw [(H.pushGraph cap hcap f).symm]
  nonneg a b := sum_nonneg fun f hf => mul_nonneg (hp f hf) ((H.pushGraph cap hcap f).nonneg _ _)
  diag a := by simp [(H.pushGraph cap hcap _).diag]

theorem cut_mixGraph (H : Hier V N) (cap : N → ℝ) (hcap : ∀ x, 0 ≤ cap x)
    (F : Finset (N → V)) (p : (N → V) → ℝ) (hp : ∀ f ∈ F, 0 ≤ p f) (S : Finset V) :
    (H.mixGraph cap hcap F p hp).cut S = ∑ f ∈ F, p f * (H.pushGraph cap hcap f).cut S := by
  show ∑ a ∈ S, ∑ b ∈ Sᶜ, ∑ f ∈ F, p f * (H.pushGraph cap hcap f).w a b = _
  simp_rw [sum_comm (s := Sᶜ) (t := F)]
  rw [sum_comm]
  refine sum_congr rfl fun f _ => ?_
  simp_rw [← mul_sum]
  rfl

/-- **Lower bound for a distribution.** -/
theorem rep_le_cut_mixGraph (H : Hier V N) (cap : N → ℝ) (hcap : ∀ x, 0 ≤ cap x)
    {F : Finset (N → V)} {p : (N → V) → ℝ} (hp : ∀ f ∈ F, 0 ≤ p f) (hsum : ∑ f ∈ F, p f = 1)
    (hfix : ∀ f ∈ F, H.Fixing f) (S : Finset V) :
    H.rep cap S ≤ (H.mixGraph cap hcap F p hp).cut S := by
  rw [cut_mixGraph]
  calc H.rep cap S = ∑ f ∈ F, p f * H.rep cap S := by rw [← sum_mul, hsum, one_mul]
    _ ≤ ∑ f ∈ F, p f * (H.pushGraph cap hcap f).cut S := sum_le_sum fun f hf =>
        mul_le_mul_of_nonneg_left (rep_le_cut_pushGraph H cap hcap (hfix f hf) S) (hp f hf)

/-- **Upper bound.** If every tree edge carries expected load at most `ρ₀` times its
capacity, then `c_J(S) ≤ ρ₀ R(S)`. -/
theorem cut_le_of_load (H : Hier V N) {cap : N → ℝ} (J : WeightedGraph V) {ρ0 : ℝ}
    (_hρ0 : 0 ≤ ρ0) (hload : ∀ x ∈ H.edges, J.cut (H.cluster x) ≤ ρ0 * cap x) (S : Finset V) :
    J.cut S ≤ ρ0 * H.rep cap S := by
  obtain ⟨ℓ, hℓ, hR⟩ := H.exists_rep_eq cap S
  rw [hR]
  refine (cut_le_labelCost J hℓ).trans ?_
  unfold labelCost
  rw [mul_sum]
  refine sum_le_sum fun x hx => ?_
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hload x hx) (abs_nonneg _)

theorem cut_mixGraph_le (H : Hier V N) (cap : N → ℝ) (hcap : ∀ x, 0 ≤ cap x)
    {F : Finset (N → V)} {p : (N → V) → ℝ} (hp : ∀ f ∈ F, 0 ≤ p f) {ρ0 : ℝ} (hρ0 : 0 ≤ ρ0)
    (hload : ∀ x ∈ H.edges,
      ∑ f ∈ F, p f * (H.pushGraph cap hcap f).cut (H.cluster x) ≤ ρ0 * cap x)
    (S : Finset V) :
    (H.mixGraph cap hcap F p hp).cut S ≤ ρ0 * H.rep cap S :=
  cut_le_of_load H _ hρ0 (fun x hx => by rw [cut_mixGraph]; exact hload x hx) S

end Hier

/-- **The remaining input of Milestone 6**: a finite distribution of retractions with expected
load at most `ρ₀` times the capacity on every tree edge, for every hierarchy with childless
leaves, every nonnegative capacity function, and a nonempty terminal set. -/
def RetractionBound (ρ0 : ℝ) : Prop :=
  ∀ (V M : Type) [Fintype V] [DecidableEq V] [Nonempty V] [Fintype M] [DecidableEq M]
    (H : Hier V M), H.LeafChildless → ∀ cap : M → ℝ, ∀ hcap : ∀ x, 0 ≤ cap x,
      ∃ F : Finset (M → V), ∃ p : (M → V) → ℝ, ∃ _hp : ∀ f ∈ F, 0 ≤ p f,
        (∀ f ∈ F, H.Fixing f) ∧ ∑ f ∈ F, p f = 1 ∧
        ∀ x ∈ H.edges, ∑ f ∈ F, p f * (H.pushGraph cap hcap f).cut (H.cluster x) ≤ ρ0 * cap x

/-- **Transfer.** A retraction bound gives a constant-quality cut guard. -/
theorem constantCutGuard_of_retractionBound {ρ0 : ℝ} (hρ0 : 0 ≤ ρ0)
    (h : RetractionBound ρ0) : ConstantCutGuard ρ0 := by
  intro V M _ _ _ _ H hlc cap hcap
  rcases isEmpty_or_nonempty V with hV | hV
  · -- no terminals: every shore is empty and every extension cost is attained by a constant
    refine ⟨0, fun S => ?_⟩
    have hS : S = ∅ := Subsingleton.elim _ _
    subst hS
    have hext : H.Extends ∅ fun _ => false := fun v => isEmptyElim v
    have h0 : H.rep cap ∅ ≤ 0 := (H.rep_le cap hext).trans (by
      rw [Hier.labelCost_toReal_bool]; simp)
    have h1 := H.rep_nonneg hcap ∅
    simp only [cut_zero]
    constructor <;> nlinarith
  · obtain ⟨F, p, hp, hfix, hsum, hload⟩ := h V M H hlc cap hcap
    exact ⟨H.mixGraph cap hcap F p hp, fun S =>
      ⟨Hier.rep_le_cut_mixGraph H cap hcap hp hsum hfix S,
        Hier.cut_mixGraph_le H cap hcap hp hρ0 hload S⟩⟩

end Hierarchy
end CutQueryComplexity
