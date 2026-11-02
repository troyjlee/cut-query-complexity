import CutQueryComplexity.GHReduction.RandomPrograms

/-! # Adding supported realized costs through adaptive composition -/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section

variable {I A O P : Type} {q r : ℕ}

theorem random_bind_cost (T : RTree I A O q) (f : O → RTree I A P r)
    (read : I → A) (scale firstBudget nextBudget : ℕ)
    (hfirst : ∀ p ∈ (RTree.run read T).support, scale * p.2 ≤ firstBudget)
    (hnext : ∀ p ∈ (RTree.run read T).support,
      ∀ s ∈ (RTree.run read (f p.1)).support, scale * s.2 ≤ nextBudget)
    {p : P × ℕ} (hp : p ∈ (RTree.run read (T.bind f)).support) :
    scale * p.2 ≤ firstBudget + nextBudget := by
  rw [RTree.run_bind] at hp
  obtain ⟨first, hf, hMapped⟩ := (PMF.mem_support_bind_iff _ _ _).mp hp
  obtain ⟨next, hn, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hMapped
  rw [← heq, Nat.mul_add]
  exact Nat.add_le_add (hfirst first hf) (hnext first hf next hn)

theorem random_map_cost (T : RTree I A O q) (f : O → P) (read : I → A)
    (scale budget : ℕ)
    (hcost : ∀ p ∈ (RTree.run read T).support, scale * p.2 ≤ budget)
    {p : P × ℕ} (hp : p ∈ (RTree.run read (T.map f)).support) : scale * p.2 ≤ budget := by
  rw [random_run_map] at hp
  obtain ⟨out, hout, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
  rw [← heq]
  exact hcost out hout

theorem run_output_support (T : RTree I A O q) (read : I → A)
    {p : O × ℕ} (hp : p ∈ (RTree.run read T).support) : p.1 ∈ (T.eval read).support :=
  (PMF.mem_support_map_iff _ _ _).mpr ⟨p, hp, rfl⟩

end
end CutQueryComplexity.GHReduction
