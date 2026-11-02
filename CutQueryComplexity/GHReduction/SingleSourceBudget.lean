import CutQueryComplexity.GHReduction.SingleSource

/-! # The single-source query budget and hard-capped endpoint

The actual graph size multiplies the complete guide cost, then the public
number of samples and buckets. Both sampling and offline bucket computation
make zero input queries. Exact truncation coupling preserves the failure bound.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical ENNReal BigOperators
open Probability

variable {V : Type} [Fintype V] [DecidableEq V]

theorem sampledGuideContinuation_cost_scaled {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q)
    (samples trials levels scale exponent : ℕ) (G : WeightedGraph V) (hG : InputPromise M G)
    (U : Finset V) (s : U) (hvn : Fintype.card V ≤ n) (L : List (RootedTree U))
    {p : (V → Option ℝ) × ℕ}
    (hp : p ∈ (RTree.run G.cut
      (sampledGuideContinuation family n samples trials levels scale exponent U s hvn L)).support) :
    n * p.2 ≤ Fintype.card V * (samples *
      guideTwoSharpBudget M Q n trials levels scale exponent (Nat.clog 2 (n + 1))) := by
  by_cases hlen : L.length = samples
  · simp only [sampledGuideContinuation, hlen, dite_true, RTree.run_cast] at hp
    apply random_map_cost _ _ G.cut n _ ?_ hp
    intro out hout
    have h := randomTable_cost (fun _ => none)
      (fun i : Fin samples => guideTwoTree family n trials levels scale exponent
        (Nat.clog 2 (n + 1)) (terminalGuide U s (guideListEntry L hlen i)) hvn)
      G.cut n (fun _ => Fintype.card V * guideTwoSharpBudget M Q n trials levels scale exponent
        (Nat.clog 2 (n + 1)))
      (fun i p hp => guideTwoTree_cost_linear family hQ trials levels scale exponent _ G hG
        (terminalGuide U s (guideListEntry L hlen i)) hvn hp) hout
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id,
      Nat.mul_assoc, Nat.mul_left_comm] using h
  · simp only [sampledGuideContinuation, hlen, dite_false, RTree.run_pure, PMF.pure_map] at hp
    have heq := (PMF.mem_support_pure_iff _ _).mp hp
    rw [heq]
    simp

theorem sampledGuideTree_cost_scaled {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q)
    (samples trials levels scale exponent : ℕ) (G K : WeightedGraph V) (hG : InputPromise M G)
    (U : Finset V) (s : U) (hU : 2 ≤ U.card) (hpos : 0 < terminalMin K U)
    (hvn : Fintype.card V ≤ n) {p : (V → Option ℝ) × ℕ}
    (hp : p ∈ (RTree.run G.cut
      (sampledGuideTree family n samples trials levels scale exponent K U s hU hpos hvn)).support) :
    n * p.2 ≤ Fintype.card V * (samples *
      guideTwoSharpBudget M Q n trials levels scale exponent (Nat.clog 2 (n + 1))) := by
  rw [sampledGuideTree, RTree.run_cast] at hp
  have h := random_bind_cost _ _ G.cut n 0 _
    (fun p hp => by rw [guideSampleProgram_cost K U hU hpos samples G.cut hp]; simp)
    (fun first _ p hp => sampledGuideContinuation_cost_scaled family hQ samples trials levels scale
      exponent G hG U s hvn first.1 hp) hp
  simpa only [zero_add] using h

theorem bucketSourceTree_cost_scaled {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q)
    (samples trials levels scale exponent : ℕ) (G K : WeightedGraph V) (hG : InputPromise M G)
    (U : Finset V) (s : V) (hvn : Fintype.card V ≤ n) (j : ℕ) {p : (V → Option ℝ) × ℕ}
    (hp : p ∈ (RTree.run G.cut
      (bucketSourceTree family n samples trials levels scale exponent K U s hvn j)).support) :
    n * p.2 ≤ Fintype.card V * (samples *
      guideTwoSharpBudget M Q n trials levels scale exponent (Nat.clog 2 (n + 1))) := by
  by_cases hne : (sourceBucket K U s j).Nonempty
  · simp only [bucketSourceTree, hne, dite_true] at hp
    exact sampledGuideTree_cost_scaled family hQ samples trials levels scale exponent G K hG
      _ _ _ _ hvn hp
  · simp only [bucketSourceTree, hne, dite_false, RTree.run_pure, PMF.pure_map] at hp
    have heq := (PMF.mem_support_pure_iff _ _).mp hp
    rw [heq]
    simp

def singleSourceSharpBudget (M : ℕ) (Q : ℕ → ℕ) (n samples trials levels scale exponent : ℕ) : ℕ :=
  bucketCount M * (samples * guideTwoSharpBudget M Q n trials levels scale exponent (Nat.clog 2 (n + 1)))

theorem singleSourceTree_cost_scaled {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q)
    (samples trials levels scale exponent : ℕ) (G K : WeightedGraph V) (hG : InputPromise M G)
    (U : Finset V) (s : V) (hvn : Fintype.card V ≤ n) {p : (V → Option ℝ) × ℕ}
    (hp : p ∈ (RTree.run G.cut
      (singleSourceTree family n samples trials levels scale exponent K U s hvn)).support) :
    n * p.2 ≤ Fintype.card V * singleSourceSharpBudget M Q n samples trials levels scale exponent := by
  unfold singleSourceTree singleSourceBudget at hp
  rw [RTree.run_cast] at hp
  apply random_map_cost _ _ G.cut n _ ?_ hp
  intro out hout
  have h := randomTable_cost (fun _ => none)
    (fun j : Fin (bucketCount M) => bucketSourceTree family n samples trials levels scale exponent K U s hvn j.val)
    G.cut n (fun _ => Fintype.card V * (samples *
      guideTwoSharpBudget M Q n trials levels scale exponent (Nat.clog 2 (n + 1))))
    (fun j p hp => bucketSourceTree_cost_scaled family hQ samples trials levels scale exponent G K hG
      U s hvn j.val hp) hout
  simpa only [singleSourceSharpBudget, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_id, Nat.mul_assoc, Nat.mul_left_comm] using h

def singleSourceCappedTree {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n samples trials levels scale exponent : ℕ) (K : WeightedGraph V)
    (U : Finset V) (s : V) (hvn : Fintype.card V ≤ n) :
    RTree (Finset V) ℝ (Option (V → Option ℝ))
      (singleSourceSharpBudget M Q n samples trials levels scale exponent) :=
  (singleSourceTree family n samples trials levels scale exponent K U s hvn).truncate
    (singleSourceSharpBudget M Q n samples trials levels scale exponent)

theorem singleSourceCappedTree_failure_le {M n scale : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q) (hnscale : n ≤ scale)
    (samples trials levels exponent : ℕ) (hlevels : thresholdLevels n ≤ levels)
    (G K : WeightedGraph V) (hG : InputPromise M G) (U : Finset V) (s : V) (hs : s ∈ U)
    (hvn : Fintype.card V ≤ n)
    (happrox : ∀ S, (99 / 100 : ℝ) * G.cut S ≤ K.cut S ∧
      K.cut S ≤ (101 / 100 : ℝ) * G.cut S) :
    mass ((singleSourceCappedTree family n samples trials levels scale exponent K U s hvn).eval G.cut)
      (fun output => ¬output.elim False (SourceValuesSuccess G U s)) ≤
      singleSourceError M n samples trials scale exponent := by
  haveI : Nonempty V := ⟨s⟩
  have hfailure := singleSourceTree_failure_le family hQ hnscale samples trials levels exponent hlevels
    G K hG U s hs hvn happrox
  rw [RTree.eval, mass_map] at hfailure
  rw [singleSourceCappedTree, RTree.eval_truncate, mass_map]
  apply le_trans (mass_mono_on_support _ ?_) hfailure
  intro p hp hbad
  have hcost := cost_le_of_scaled (Fintype.card_pos.trans_le hvn) hvn
    (singleSourceTree_cost_scaled family hQ samples trials levels scale exponent G K hG U s hvn hp)
  simpa only [hcost, ite_true, Option.elim_some] using hbad

end
end CutQueryComplexity.GHReduction
