import CutQueryComplexity.Sparsification.EstimationCharge
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! # The query budget of a successful estimation run

On a successful finished run the accounting sum is bounded explicitly:

```text
runAcc ≤ 2(n−1)·log₂(2n⁴) + residualDrawCost·8ρ(n−1) + n.
```

* **Calls.** Each logged call charges a forest edge, the forest has at most
  `2(n−1)` ordered edges, and a merged forest edge has charge at most
  `log₂(2n⁴)`.
* **Draws.** A sampling call makes at most `2ρM/κ` draws. Summed over calls,
  `Σ M/κ` equals `(1/2) Σ_{u,v} w_uv·chargeW(u,v)`, which is at most
  `2 Σ w/k ≤ 4(n−1)` by the strength sum.
* **Group queries** equal the number of events, at most `n`.
-/

namespace CutQueryComplexity.WeightedGraph
noncomputable section
open scoped Classical
open Probability
variable {V : Type} [Fintype V]

/-! ### Counting calls -/

theorem length_le_sum_countP {α β : Type} (L : List α) (E : Finset β) (P : α → β → Prop)
    (h : ∀ c ∈ L, ∃ p ∈ E, P c p) :
    L.length ≤ ∑ p ∈ E, L.countP (fun c => decide (P c p)) := by
  induction L with
  | nil => simp
  | cons c L ih =>
      obtain ⟨p, hp, hcp⟩ := h c List.mem_cons_self
      have hL := ih (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))
      simp only [List.length_cons, List.countP_cons, Finset.sum_add_distrib]
      have h1 : 1 ≤ ∑ q ∈ E, (if P c q then 1 else 0) :=
        le_trans (by simp [hcp]) (Finset.single_le_sum (f := fun q => if P c q then 1 else 0)
          (fun _ _ => Nat.zero_le _) hp)
      have : ∑ q ∈ E, (if decide (P c q) = true then 1 else 0) = ∑ q ∈ E, (if P c q then 1 else 0) := by
        simp
      omega

/-- Ordered pairs joined by a forest edge. -/
def forestPairs (H : WeightedGraph V) : Finset (V × V) :=
  Finset.univ.filter (fun p => 0 < H.w p.1 p.2)

theorem card_forestPairs_le {H : WeightedGraph V} (hacyc : H.support.IsAcyclic) :
    (forestPairs H).card ≤ 2 * (Fintype.card V - 1) := by
  have hdart : (forestPairs H).card = Fintype.card H.support.Dart := by
    rw [← Fintype.card_coe]
    apply Fintype.card_congr
    exact {
      toFun := fun p => ⟨p.1, by
        have := (Finset.mem_filter.mp p.2).2
        exact ne_of_gt this⟩
      invFun := fun d => ⟨d.toProd, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        lt_of_le_of_ne (H.nonneg _ _) (Ne.symm d.adj)⟩⟩
      left_inv := fun p => rfl
      right_inv := fun d => rfl }
  rw [hdart, SimpleGraph.dart_card_eq_twice_card_edges]
  exact Nat.mul_le_mul_left 2 (forest_card_le _ hacyc)

theorem chargeN_le_of_merged {G H : WeightedGraph V} {s : EstState V} (hc : ChargeGood G H s)
    {a b : V} (hab : 0 < H.w a b) (hm : s.π a = s.π b) :
    chargeN H s.calls a b ≤ Nat.log 2 (2 * Fintype.card V ^ 4) := by
  have h := hc.n2 a b hab hm
  apply Nat.le_log_of_pow_le (by norm_num)
  have : ((2 ^ chargeN H s.calls a b : ℕ) : ℝ) ≤ ((2 * Fintype.card V ^ 4 : ℕ) : ℝ) := by
    push_cast
    simpa [nPow4] using h
  exact_mod_cast this

/-- **Number of calls** on a successful run. -/
theorem calls_length_le {G H : WeightedGraph V} (hH : IsApproxKruskalForest G H)
    {s : EstState V} (h : EstSuccess' G H s) :
    s.calls.length ≤ 2 * (Fintype.card V - 1) * Nat.log 2 (2 * Fintype.card V ^ 4) := by
  have hlen := length_le_sum_countP s.calls (forestPairs H) (fun c p => ForestCharged H c p.1 p.2)
    (fun c hc => by
      obtain ⟨-, -, a, b, hfc⟩ := h.2.records c hc
      exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfc.2.1⟩, hfc⟩)
  refine hlen.trans ?_
  calc
    _ ≤ ∑ p ∈ forestPairs H, Nat.log 2 (2 * Fintype.card V ^ 4) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpos := (Finset.mem_filter.mp hp).2
      have hk : 0 < G.strength p.1 p.2 :=
        hpos.trans_le ((hH.original.subgraph p.1 p.2).trans (G.weight_le_strength _ _))
      exact chargeN_le_of_merged h.2 hpos (h.1.same_block hH hk)
    _ = (forestPairs H).card * Nat.log 2 (2 * Fintype.card V ^ 4) := by
      rw [Finset.sum_const, smul_eq_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ (card_forestPairs_le hH.forest.2.1)

/-! ### Counting draws -/

theorem internalMass_eq_sum (G : WeightedGraph V) (π : V → V) (T : Finset V) :
    (G.contract π).internalMass T =
      (∑ u, ∑ v, if π u ∈ T ∧ π v ∈ T ∧ π u ≠ π v then G.w u v else 0) / 2 := by
  rw [← residual_internalMass, internalMass, cross]
  congr 1
  simp only [pull, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : π u ∈ T
  · simp only [hu, ↓reduceIte, true_and]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : π v ∈ T
    · by_cases he : π u = π v <;> simp [residual, hv, he]
    · simp [hv]
  · simp [hu]

/-- Logged residual mass, by the program's cached formula. -/
def callMass (G : WeightedGraph V) (c : CallRecord V) : ℝ :=
  cachedMass c.cache c.T (G.cut (pull c.π c.T))

theorem callDraws_le (G : WeightedGraph V) {ρ : ℝ} (hρ : 2 ≤ ρ) (R : ℕ) {c : CallRecord V}
    (hκ : 0 < c.κ) (hM : 0 ≤ callMass G c) :
    (callDraws G ρ R c : ℝ) ≤ 2 * ρ * (callMass G c / c.κ) := by
  have hnn : 0 ≤ 2 * ρ * (callMass G c / c.κ) := by
    have : 0 ≤ ρ := by linarith
    positivity
  unfold callDraws
  split_ifs with h1 h2
  · simpa using hnn
  · have := drawCount_le hρ hκ (not_lt.mp h1)
    simp only [callMass] at *
    calc (⌈ρ * cachedMass c.cache c.T (G.cut (pull c.π c.T)) / c.κ⌉₊ : ℝ)
        ≤ 2 * (ρ * cachedMass c.cache c.T (G.cut (pull c.π c.T)) / c.κ) := this
      _ = _ := by ring
  · simpa using hnn


theorem mass_sum_eq (G : WeightedGraph V) (L : List (CallRecord V)) :
    (L.map (fun c => (G.contract c.π).internalMass c.T / c.κ)).sum =
      (∑ u, ∑ v, G.w u v * chargeW L u v) / 2 := by
  induction L with
  | nil => simp [chargeW]
  | cons c L ih =>
      rw [List.map_cons, List.sum_cons, ih, internalMass_eq_sum]
      have hW : ∀ u v, chargeW (c :: L) u v =
          (if InCall c u v then 1 / c.κ else 0) + chargeW L u v := by
        intro u v
        simp [chargeW]
      have hterm : ∀ u v, G.w u v * (if InCall c u v then 1 / c.κ else 0) =
          (if c.π u ∈ c.T ∧ c.π v ∈ c.T ∧ c.π u ≠ c.π v then G.w u v else 0) / c.κ := by
        intro u v
        by_cases hP : c.π u ∈ c.T ∧ c.π v ∈ c.T ∧ c.π u ≠ c.π v
        · rw [ite_eq_left_of_eq_true _ _ (eq_true (show InCall c u v from hP)),
            ite_eq_left_of_eq_true _ _ (eq_true hP)]
          ring
        · have hP' : ¬InCall c u v := hP
          simp only [hP, hP', ↓reduceIte, mul_zero, zero_div]
      simp only [hW, mul_add, Finset.sum_add_distrib, add_div, hterm]
      congr 1
      simp only [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro v _
      ring

/-- **Total estimation draws** on a successful run. -/
theorem draws_sum_le {G H : WeightedGraph V} (hH : IsApproxKruskalForest G H)
    {s : EstState V} (h : EstSuccess' G H s) {ρ : ℝ} (hρ : 2 ≤ ρ) (R : ℕ) :
    (s.calls.map (fun c => (callDraws G ρ R c : ℝ))).sum ≤
      8 * ρ * (Fintype.card V - 1 : ℕ) := by
  have hrec := h.2.records
  -- Draws per call against mass per scale.
  have h1 : (s.calls.map (fun c => (callDraws G ρ R c : ℝ))).sum ≤
      2 * ρ * (s.calls.map (fun c => (G.contract c.π).internalMass c.T / c.κ)).sum := by
    rw [← List.sum_map_mul_left]
    apply List.sum_le_sum
    intro c hc
    obtain ⟨hcache, hκ, -⟩ := hrec c hc
    have hm : callMass G c = (G.contract c.π).internalMass c.T :=
      cachedMass_eq G c.π c.cache hcache c.T
    have := callDraws_le G hρ R hκ (hm ▸ (G.contract c.π).internalMass_nonneg c.T)
    rw [hm] at this
    linarith
  rw [mass_sum_eq] at h1
  -- Per-pair charges against strengths.
  have h2 : ∑ u, ∑ v, G.w u v * chargeW s.calls u v ≤ ∑ u, ∑ v, 4 * (G.w u v / G.strength u v) := by
    apply Finset.sum_le_sum
    intro u _
    apply Finset.sum_le_sum
    intro v _
    by_cases hw : G.w u v = 0
    · simp [hw]
    · have hpos : 0 < G.w u v := lt_of_le_of_ne (G.nonneg u v) (Ne.symm hw)
      have huv : u ≠ v := by
        rintro rfl
        simp [G.diag] at hw
      have hk : 0 < G.strength u v := hpos.trans_le (G.weight_le_strength u v)
      have hc := h.2.w2 u v huv (h.1.same_block hH hk)
      calc G.w u v * chargeW s.calls u v ≤ G.w u v * (4 / G.strength u v) :=
            mul_le_mul_of_nonneg_left hc hpos.le
        _ = 4 * (G.w u v / G.strength u v) := by ring
  have h3 := G.strength_sum_le
  have h4 : ∑ u, ∑ v, 4 * (G.w u v / G.strength u v) =
      4 * ∑ u, ∑ v, G.w u v / G.strength u v := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.mul_sum]
  have hρ0 : 0 ≤ 2 * ρ := by linarith
  calc
    _ ≤ 2 * ρ * ((∑ u, ∑ v, G.w u v * chargeW s.calls u v) / 2) := h1
    _ ≤ 2 * ρ * ((4 * ∑ u, ∑ v, G.w u v / G.strength u v) / 2) := by
      rw [← h4]
      exact mul_le_mul_of_nonneg_left (by linarith) hρ0
    _ = 8 * ρ * ((∑ u, ∑ v, G.w u v / G.strength u v) / 2) := by ring
    _ ≤ 8 * ρ * (Fintype.card V - 1 : ℕ) :=
      mul_le_mul_of_nonneg_left h3 (by linarith)

theorem runAcc_split (G : WeightedGraph V) (ρ : ℝ) (R : ℕ) (L : List (CallRecord V)) :
    ((L.map (callCost G ρ R)).sum : ℝ) = L.length +
      residualDrawCost (searchDepth V) (searchDepth V) * (L.map (fun c => (callDraws G ρ R c : ℝ))).sum +
        ((L.map CallRecord.groups).sum : ℝ) := by
  induction L with
  | nil => simp
  | cons c L ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_succ, ih,
        callCost, Nat.cast_mul]
      ring

/-- **The query budget of a successful estimation run.** -/
theorem runAcc_le {G H : WeightedGraph V} (hH : IsApproxKruskalForest G H) {s : EstState V}
    (h : EstSuccess' G H s) {ρ : ℝ} (hρ : 2 ≤ ρ) (R : ℕ) :
    (runAcc G ρ R s : ℝ) ≤
      2 * (Fintype.card V - 1 : ℕ) * Nat.log 2 (2 * Fintype.card V ^ 4) +
        residualDrawCost (searchDepth V) (searchDepth V) * (8 * ρ * (Fintype.card V - 1 : ℕ)) +
          Fintype.card V := by
  rw [runAcc, runAcc_split]
  have hcalls : (s.calls.length : ℝ) ≤
      2 * (Fintype.card V - 1 : ℕ) * Nat.log 2 (2 * Fintype.card V ^ 4) := by
    exact_mod_cast calls_length_le hH h
  have hdraws := draws_sum_le hH h hρ R
  have hgroups : ((s.calls.map CallRecord.groups).sum : ℝ) ≤ Fintype.card V := by
    rw [h.2.groups]
    have := h.1.2.1.length
    exact_mod_cast (Nat.le_add_right _ _).trans this
  have hcost : (0 : ℝ) ≤ residualDrawCost (searchDepth V) (searchDepth V) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hdraws hcost]

end
end CutQueryComplexity.WeightedGraph
