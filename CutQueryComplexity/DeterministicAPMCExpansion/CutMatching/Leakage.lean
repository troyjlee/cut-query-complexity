import CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.Basic

/-!
# Leakage of the public lazy matching walk

The total mass starting in a shore and ending outside it is at most half
the number of matching edges crossing that shore, with all rounds counted
with multiplicity. This is the combinatorial input to balanced-game entropy
progress. It concerns the explicit matching history and uses no graph query.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.CutMatching

open Finset WeightedGraph
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

theorem sum_indicator (S : Finset V) (p : V → ℝ) :
    (∑ v, if v ∈ S then p v else 0) = ∑ v ∈ S, p v := by
  symm
  calc
    _ = ∑ v ∈ S, if v ∈ S then p v else 0 := by
      apply sum_congr rfl
      intro v hv
      simp only [hv, ↓reduceIte]
    _ = _ := sum_subset (subset_univ S) (by intro v _ hv; simp only [hv, ↓reduceIte])

theorem Matching.cut_eq_indicator (M : Matching V) (S : Finset V) :
    M.graph.cut S = ∑ v ∈ S, if M.mate v ∉ S then (1 : ℝ) else 0 := by
  simp only [cut, Matching.graph, sum_ite_eq, mem_compl]

theorem Matching.compl_mass_average (M : Matching V) (S : Finset V) (p : V → ℝ)
    (hp : ∀ v, 0 ≤ p v) (hpone : ∀ v, p v ≤ 1) :
    (∑ v ∈ Sᶜ, average M p v) ≤ (∑ v ∈ Sᶜ, p v) + M.graph.cut S / 2 := by
  have hperm : (∑ v ∈ Sᶜ, p (M.mate v)) =
      ∑ v, if M.mate v ∈ Sᶜ then p v else 0 := by
    calc
      _ = ∑ v, if v ∈ Sᶜ then p (M.mate v) else 0 := (sum_indicator _ _).symm
      _ = ∑ v, if M.mate v ∈ Sᶜ then p (M.mate (M.mate v)) else 0 :=
        (Equiv.sum_comp M.mate (fun v => if v ∈ Sᶜ then p (M.mate v) else 0)).symm
      _ = _ := by
        apply sum_congr rfl
        intro v _
        rw [M.involutive v]
  have hpoint (v : V) :
      (if M.mate v ∈ Sᶜ then p v else 0) ≤
        (if v ∈ Sᶜ then p v else 0) +
          (if v ∈ S ∧ M.mate v ∉ S then (1 : ℝ) else 0) := by
    by_cases hv : v ∈ S <;> by_cases hm : M.mate v ∈ S <;>
      simp [hv, hm, hp, hpone]
  have hsum := sum_le_sum (s := (univ : Finset V)) (fun v _ => hpoint v)
  have hcross : (∑ v, if v ∈ S ∧ M.mate v ∉ S then (1 : ℝ) else 0) =
      M.graph.cut S := by
    rw [Matching.cut_eq_indicator]
    simpa only [ite_and] using sum_indicator S (fun v => if M.mate v ∉ S then (1 : ℝ) else 0)
  rw [sum_add_distrib, sum_indicator, hcross, ← hperm] at hsum
  simp only [average, ← sum_div, sum_add_distrib]
  linarith

def startMass (history : List (Matching V)) (S : Finset V) (v : V) : ℝ :=
  ∑ u ∈ S, walk history u v

def leakage (history : List (Matching V)) (S : Finset V) : ℝ :=
  ∑ v ∈ Sᶜ, startMass history S v

theorem startMass_nonneg (history : List (Matching V)) (S : Finset V) (v : V) :
    0 ≤ startMass history S v :=
  sum_nonneg fun u _ => walk_nonneg history u v

theorem startMass_le_one (history : List (Matching V)) (S : Finset V) (v : V) :
    startMass history S v ≤ 1 := by
  calc
    _ ≤ ∑ u, walk history u v := sum_le_sum_of_subset_of_nonneg (subset_univ S)
      (fun u _ _ => walk_nonneg history u v)
    _ = 1 := walk_column_sum history v

theorem startMass_cons (M : Matching V) (history : List (Matching V)) (S : Finset V) (v : V) :
    startMass (M :: history) S v = average M (startMass history S) v := by
  simp only [startMass, walk, average, ← sum_div, sum_add_distrib]

theorem leakage_nonneg (history : List (Matching V)) (S : Finset V) :
    0 ≤ leakage history S := sum_nonneg fun v _ => startMass_nonneg history S v

@[simp] theorem leakage_nil (S : Finset V) : leakage ([] : List (Matching V)) S = 0 := by
  unfold leakage startMass
  apply sum_eq_zero
  intro v hv
  simp only [walk, sum_ite_eq', mem_compl.mp hv, ↓reduceIte]

theorem leakage_cons_le (M : Matching V) (history : List (Matching V)) (S : Finset V) :
    leakage (M :: history) S ≤ leakage history S + M.graph.cut S / 2 := by
  simp only [leakage, startMass_cons]
  exact M.compl_mass_average S (startMass history S)
    (startMass_nonneg history S) (startMass_le_one history S)

/-- The factor one-half comes from the lazy matching transition. -/
theorem twice_leakage_le_cut (history : List (Matching V)) (S : Finset V) :
    2 * leakage history S ≤ (historyGraph history).cut S := by
  induction history with
  | nil => simp
  | cons M history ih =>
      rw [historyGraph_cons_cut]
      have h := leakage_cons_le M history S
      linarith

theorem leakage_eq_start_sum (history : List (Matching V)) (S : Finset V) :
    leakage history S = ∑ u ∈ S, ∑ v ∈ Sᶜ, walk history u v := by
  exact sum_comm

end
end CutQueryComplexity.DeterministicAPMCExpansion.CutMatching

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.leakage_cons_le
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.twice_leakage_le_cut
