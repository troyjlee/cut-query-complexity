import CutQueryComplexity.Graph.RespectingCuts

/-! # Weighted averaging for cut counting

The number of shores surviving a contraction is averaged with the quotient's
edge weights. A shore loses exactly twice its cut weight in the ordered-pair
sum. The minimum-cut promise bounds the total degree of the live blocks.
No random contraction process or integrality of weights is needed.
-/

namespace CutQueryComplexity
noncomputable section
open scoped Classical
open WeightedGraph
variable {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]

def survivingShores (π : V → B) (A : Finset (Finset V)) (a b : B) : Finset (Finset V) :=
  A.filter (fun S => a ∈ S.image π ↔ b ∈ S.image π)

namespace WeightedGraph

def totalDegree (G : WeightedGraph V) : ℝ := ∑ u, ∑ v, G.w u v

def sameSideMass (G : WeightedGraph V) (S : Finset V) : ℝ :=
  ∑ u, ∑ v, if (u ∈ S ↔ v ∈ S) then G.w u v else 0

theorem sameSideMass_add_cut (G : WeightedGraph V) (S : Finset V) :
    G.sameSideMass S + 2 * G.cut S = G.totalDegree := by
  have h : G.sameSideMass S + G.cut S + G.cut Sᶜ = G.totalDegree := by
    simp only [sameSideMass, cut_eq_sum_ite, totalDegree, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp [hu, hv]
  rw [cut_compl] at h
  linarith

theorem totalDegree_contract_ge (G : WeightedGraph V) (π : V → B) {κ : ℝ}
    (hκ : ∀ S, ProperShore S → κ ≤ G.cut S) (hn : 2 ≤ (liveBlocks π).card) :
    (liveBlocks π).card * κ ≤ (G.contract π).totalDegree := by
  calc
    _ = ∑ a ∈ liveBlocks π, κ := by simp [mul_comm]
    _ ≤ ∑ a ∈ liveBlocks π, (G.contract π).degree a :=
      Finset.sum_le_sum (fun a ha => G.contract_degree_ge π hκ hn ha)
    _ ≤ ∑ a, (G.contract π).degree a :=
      Finset.sum_le_univ_sum_of_nonneg (fun a =>
        Finset.sum_nonneg (fun b _ => (G.contract π).nonneg a b))
    _ = _ := rfl

end WeightedGraph

theorem weighted_survivors_eq_sum (G : WeightedGraph V) (π : V → B)
    (A : Finset (Finset V)) :
    (∑ a, ∑ b, (G.contract π).w a b * ((survivingShores π A a b).card : ℝ)) =
      ∑ S ∈ A, (G.contract π).sameSideMass (S.image π) := by
  calc
    _ = ∑ a, ∑ b, ∑ S ∈ A, if (a ∈ S.image π ↔ b ∈ S.image π)
        then (G.contract π).w a b else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      simp [survivingShores, Finset.sum_ite, mul_comm]
    _ = ∑ a, ∑ S ∈ A, ∑ b, if (a ∈ S.image π ↔ b ∈ S.image π)
        then (G.contract π).w a b else 0 := Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

/-- The exact weighted double-counting identity behind contraction survival. -/
theorem weighted_survivors_add_cuts (G : WeightedGraph V) (π : V → B)
    (A : Finset (Finset V)) (hA : ∀ S ∈ A, RespectsBlocks π S) :
    (∑ a, ∑ b, (G.contract π).w a b * ((survivingShores π A a b).card : ℝ)) +
      2 * (∑ S ∈ A, G.cut S) = (G.contract π).totalDegree * A.card := by
  rw [weighted_survivors_eq_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  have he (S : Finset V) (hS : S ∈ A) :
      (G.contract π).sameSideMass (S.image π) + 2 * G.cut S = (G.contract π).totalDegree := by
    have hc : (G.contract π).cut (S.image π) = G.cut S := by
      rw [cut_contract, (hA S hS).pull_image]
    rw [← hc]
    exact (G.contract π).sameSideMass_add_cut _
  simp only [Finset.sum_congr rfl he, Finset.sum_const, nsmul_eq_mul]
  ring

/-- A one-step recurrence, with a common bound on all positive-edge contractions. -/
theorem contraction_count_step (G : WeightedGraph V) (π : V → B)
    (A : Finset (Finset V)) {κ k C : ℝ} (hκpos : 0 < κ) (hk : 0 ≤ k)
    (hκ : ∀ S, ProperShore S → κ ≤ G.cut S) (hn : 2 ≤ (liveBlocks π).card)
    (hA : ∀ S ∈ A, RespectsBlocks π S) (hcut : ∀ S ∈ A, G.cut S ≤ k * κ)
    (hsurv : ∀ a b, 0 < (G.contract π).w a b →
      ((survivingShores π A a b).card : ℝ) ≤ C) :
    ((liveBlocks π).card - 2 * k) * (A.card : ℝ) ≤ (liveBlocks π).card * C := by
  have hsum : (∑ S ∈ A, G.cut S) ≤ A.card * (k * κ) := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hcut
  have hw : (∑ a, ∑ b, (G.contract π).w a b * ((survivingShores π A a b).card : ℝ)) ≤
      (G.contract π).totalDegree * C := by
    simp only [WeightedGraph.totalDegree, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro a _
    apply Finset.sum_le_sum
    intro b _
    by_cases hp : 0 < (G.contract π).w a b
    · exact mul_le_mul_of_nonneg_left (hsurv a b hp) hp.le
    · have hz := le_antisymm (le_of_not_gt hp) ((G.contract π).nonneg a b)
      simp [hz]
  have hid := weighted_survivors_add_cuts G π A hA
  by_cases hN : (A.card : ℝ) ≤ C
  · have h1 := mul_le_mul_of_nonneg_left hN (Nat.cast_nonneg (liveBlocks π).card : (0 : ℝ) ≤ _)
    have h2 := mul_nonneg hk (Nat.cast_nonneg A.card : (0 : ℝ) ≤ _)
    nlinarith
  · have hW := mul_le_mul_of_nonneg_right (G.totalDegree_contract_ge π hκ hn)
      (sub_nonneg.mpr (lt_of_not_ge hN).le)
    apply (mul_le_mul_iff_right₀ hκpos).mp
    nlinarith

end
end CutQueryComplexity
