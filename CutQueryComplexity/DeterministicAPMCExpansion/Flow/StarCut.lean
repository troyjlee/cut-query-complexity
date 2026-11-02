import CutQueryComplexity.DeterministicAPMCExpansion.Flow.Network
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

/-! # Exact cut arithmetic for the two public terminal stars -/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.Flow

open Finset WeightedGraph AllPairsAudit
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

theorem sum_shore_ite (S : Finset V) (f : V → ℝ) :
    (∑ v ∈ S, f v) = ∑ v, if v ∈ S then f v else 0 := by
  rw [← sum_filter]
  congr 1
  ext v
  simp

theorem knownStars_source_cut (a z : V → ℕ) (A : Finset (NetworkVertex V))
    (hs : source ∈ A) (ht : sink ∉ A) :
    (knownStars a z).cut A =
      (∑ v ∈ (originalShore A)ᶜ, (a v : ℝ)) +
        ∑ v ∈ originalShore A, (z v : ℝ) := by
  have hs' : Sum.inr (0 : Fin 2) ∈ A := hs
  have ht' : Sum.inr (1 : Fin 2) ∉ A := ht
  rw [sum_shore_ite (originalShore A)ᶜ (fun v => (a v : ℝ)),
    sum_shore_ite (originalShore A) (fun v => (z v : ℝ))]
  simp [cut_eq_sum_ite, Fintype.sum_sum_type, Fin.sum_univ_two,
    knownStars, terminalCapacity, hs', ht', add_comm]

theorem twoStar_source_cut (G : WeightedGraph V) (a z : V → ℕ)
    (A : Finset (NetworkVertex V)) (hs : source ∈ A) (ht : sink ∉ A) :
    (twoStar G a z).cut A = G.cut (originalShore A) +
      (∑ v ∈ (originalShore A)ᶜ, (a v : ℝ)) +
        ∑ v ∈ originalShore A, (z v : ℝ) := by
  rw [twoStar_cut, knownStars_source_cut a z A hs ht]
  ring

theorem sum_shore_add_compl (p : V → ℝ) (S : Finset V) :
    (∑ v ∈ S, p v) + (∑ v ∈ Sᶜ, p v) = ∑ v, p v := by
  rw [← sum_union disjoint_compl_right, union_compl]

end
end CutQueryComplexity.DeterministicAPMCExpansion.Flow

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.twoStar_source_cut
