import CutQueryComplexity.MinCut.Contraction
import CutQueryComplexity.MinCut.SpanTree
import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Algebra.BigOperators.Field
import CutQueryComplexity.Probability.Events

/-! # A tree distribution from the minimax theorem

Let every proper cut of `H` weigh at least `λ > 0`. A *good* edge set uses only
positive edges and crosses every proper cut. We play the zero-sum game where the
minimizer picks a good set `F`, the maximizer picks an ordered pair `e`, and the
payoff is `[F joins e] / w(e)`.

* For any mixed maximizer `b`, the contraction bound with lengths
  `ℓ(u,v) = (b(u,v) + b(v,u)) / w(u,v)` gives a good `F` with payoff at most `2/λ`.
* Sion's theorem (`Sion.exists_isSaddlePointOn`) gives a mixed minimizer `a` with
  every pure payoff at most `2/λ`, so `Pr_a[F joins u,v] ≤ 2w(u,v)/λ`.

Replacing each good set by a BFS tree inside it (`SpanTree.bfsTree`), the expected
number of tree edges crossing `S` is at most `2·cut_H(S)/λ` (`exists_tree_family`).
-/

namespace CutQueryComplexity
namespace TreePacking

noncomputable section
open scoped Classical
open SpanTree Contraction
variable {V : Type} [Fintype V]

/-- Positive edges crossing every proper cut. -/
def Good (H : WeightedGraph V) (F : Finset (V × V)) : Prop :=
  (∀ e ∈ F, 0 < H.w e.1 e.2) ∧ Spans F

abbrev Strat (H : WeightedGraph V) := {F : Finset (V × V) // Good H F}

def ind (F : Finset (V × V)) (e : V × V) : ℝ := if Adj F e.1 e.2 then 1 else 0

def payoff (H : WeightedGraph V) (x : Strat H → ℝ) (y : V × V → ℝ) : ℝ :=
  ∑ F, ∑ e, x F * y e * (ind F.1 e / H.w e.1 e.2)

def linX (H : WeightedGraph V) (y : V × V → ℝ) : (Strat H → ℝ) →ₗ[ℝ] ℝ where
  toFun x := payoff H x y
  map_add' x x' := by
    simp only [payoff, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [payoff, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

def linY (H : WeightedGraph V) (x : Strat H → ℝ) : (V × V → ℝ) →ₗ[ℝ] ℝ where
  toFun y := payoff H x y
  map_add' y y' := by
    simp only [payoff, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' c y := by
    simp only [payoff, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

omit [Fintype V] in
theorem ind_nonneg (F : Finset (V × V)) (e : V × V) : 0 ≤ ind F e := by
  unfold ind; split_ifs <;> norm_num

theorem ind_zero_of_good {H : WeightedGraph V} {F : Finset (V × V)} (hF : Good H F) {u v : V}
    (h : H.w u v = 0) : ind F (u, v) = 0 := by
  unfold ind Adj
  split_ifs with hadj
  swap; · rfl
  rcases hadj with h' | h'
  · exact ((hF.1 _ h').ne' h).elim
  · exact ((hF.1 _ h').ne' (by rw [H.symm]; exact h)).elim

set_option linter.deprecated false in
/-- Payoff of a pure good set against a mixed maximizer, via the contraction bound. -/
theorem best_response (H : WeightedGraph V) {lam : ℝ} (hlam : 0 < lam)
    (hcut : ∀ S, ProperShore S → lam ≤ H.cut S) {b : V × V → ℝ}
    (hb : b ∈ stdSimplex ℝ (V × V)) :
    ∃ F : Strat H, ∑ e, b e * (ind F.1 e / H.w e.1 e.2) ≤ 2 / lam := by
  set ℓ : V → V → ℝ := fun u v => (b (u, v) + b (v, u)) / H.w u v
  have hb0 : ∀ e, 0 ≤ b e := hb.1
  obtain ⟨F, hpos, hspan, hbound⟩ := exists_connector H hlam hcut ℓ
    (fun u v => by simp only [ℓ]; rw [H.symm, add_comm])
    (fun u v _ => div_nonneg (add_nonneg (hb0 _) (hb0 _)) (H.nonneg u v))
  refine ⟨⟨F, hpos, hspan⟩, ?_⟩
  -- Union bound over the two orientations.
  have h1 : ∑ e, b e * (ind F e / H.w e.1 e.2) ≤
      ∑ e, (if e ∈ F then b e / H.w e.1 e.2 else 0) +
        ∑ e, (if e.swap ∈ F then b e / H.w e.1 e.2 else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun e _ => ?_
    have hq : 0 ≤ b e / H.w e.1 e.2 := div_nonneg (hb0 e) (H.nonneg _ _)
    unfold ind Adj
    by_cases h1 : e ∈ F <;> by_cases h2 : e.swap ∈ F <;>
      simp_all [Prod.swap, div_eq_mul_inv]
  have h2 : ∑ e, (if e.swap ∈ F then b e / H.w e.1 e.2 else 0) =
      ∑ e, (if e ∈ F then b e.swap / H.w e.1 e.2 else 0) := by
    rw [← Equiv.sum_comp (Equiv.prodComm V V)]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp [Prod.swap, H.symm e.2 e.1]
  have h3 : ∑ e, (if e ∈ F then b e / H.w e.1 e.2 else 0) +
      ∑ e, (if e ∈ F then b e.swap / H.w e.1 e.2 else 0) = lenF ℓ F := by
    rw [← Finset.sum_add_distrib, lenF, ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (· ∈ F)]
    rw [show Finset.univ.filter (· ∈ F) = F by ext; simp]
    rw [Finset.sum_eq_zero (s := Finset.univ.filter fun e => e ∉ F) (fun e he => by
      simp only [Finset.mem_filter] at he; simp [he.2]), add_zero]
    refine Finset.sum_congr rfl fun e he => ?_
    simp only [he, ↓reduceIte, ℓ, Prod.swap, add_div]
  -- The total weighted length is at most `2`.
  have h4 : ∑ u, ∑ v, H.w u v * ℓ u v ≤ 2 := by
    have hle : ∀ u v, H.w u v * ℓ u v ≤ b (u, v) + b (v, u) := by
      intro u v
      simp only [ℓ]
      rcases (H.nonneg u v).eq_or_lt with h0 | h0
      · rw [← h0, zero_mul]; exact add_nonneg (hb0 _) (hb0 _)
      · rw [mul_div_cancel₀ _ h0.ne']
    have hsum : ∑ u, ∑ v, (b (u, v) + b (v, u)) = 2 := by
      simp only [Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun u v => b (v, u))]
      have : ∑ u, ∑ v, b (u, v) = 1 := by rw [← Fintype.sum_prod_type']; exact hb.2
      rw [this]; norm_num
    calc _ ≤ ∑ u, ∑ v, (b (u, v) + b (v, u)) :=
          Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => hle u v
      _ = 2 := hsum
  rw [le_div_iff₀ hlam]
  calc _ ≤ lenF ℓ F * lam := by rw [← h3, ← h2]; exact mul_le_mul_of_nonneg_right h1 hlam.le
    _ = lam * lenF ℓ F := mul_comm _ _
    _ ≤ 2 := hbound.trans h4

set_option linter.deprecated false in
/-- **Mixed strategy.** Some distribution on good sets joins each pair `u, v` with
probability at most `2w(u,v)/λ`. -/
theorem exists_good_dist (H : WeightedGraph V) {lam : ℝ} (hlam : 0 < lam)
    (hcut : ∀ S, ProperShore S → lam ≤ H.cut S) (hV : Nonempty V) :
    ∃ a ∈ stdSimplex ℝ (Strat H), ∀ u v, ∑ F, a F * ind F.1 (u, v) ≤ 2 * H.w u v / lam := by
  obtain ⟨F0, hpos0, hspan0, -⟩ := exists_connector H hlam hcut (fun _ _ => 0) (fun _ _ => rfl)
    (fun _ _ _ => le_rfl)
  have : Nonempty (Strat H) := ⟨⟨F0, hpos0, hspan0⟩⟩
  obtain ⟨v0⟩ := hV
  have : Nonempty (V × V) := ⟨(v0, v0)⟩
  obtain ⟨a, ha, b, hb, hsad⟩ := Sion.exists_isSaddlePointOn
    (X := stdSimplex ℝ (Strat H)) (Y := stdSimplex ℝ (V × V)) (f := payoff H)
    (ne_X := ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary _)⟩)
    (cX := convex_stdSimplex ℝ _) (kX := isCompact_stdSimplex ℝ _)
    (hfy := fun y _ => (linX H y).continuous_of_finiteDimensional.continuousOn.lowerSemicontinuousOn)
    (hfy' := fun y _ => ((linX H y).convexOn (convex_stdSimplex ℝ _)).quasiconvexOn)
    (cY := convex_stdSimplex ℝ _) (ne_Y := ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary _)⟩)
    (kY := isCompact_stdSimplex ℝ _)
    (hfx := fun x _ => (linY H x).continuous_of_finiteDimensional.continuousOn.upperSemicontinuousOn)
    (hfx' := fun x _ => ((linY H x).concaveOn (convex_stdSimplex ℝ _)).quasiconcaveOn)
  refine ⟨a, ha, fun u v => ?_⟩
  rcases (H.nonneg u v).eq_or_lt with h0 | h0
  · rw [← h0, mul_zero, zero_div]
    exact le_of_eq (Finset.sum_eq_zero fun F _ => by rw [ind_zero_of_good F.2 h0.symm, mul_zero])
  obtain ⟨F, hF⟩ := best_response H hlam hcut hb
  have hs := hsad _ (single_mem_stdSimplex ℝ F) _ (single_mem_stdSimplex ℝ (u, v))
  have hl : payoff H a (Pi.single (u, v) 1) = (∑ F, a F * ind F.1 (u, v)) / H.w u v := by
    simp only [payoff, Pi.single_apply, Finset.sum_div]
    refine Finset.sum_congr rfl fun F _ => ?_
    simp [mul_div_assoc]
  have hr : payoff H (Pi.single F 1) b = ∑ e, b e * (ind F.1 e / H.w e.1 e.2) := by
    simp only [payoff, Pi.single_apply]
    rw [Finset.sum_eq_single F (fun F' _ h => by simp [h]) (by simp)]
    simp
  rw [hl, hr, div_le_iff₀ h0] at hs
  calc _ ≤ 2 / lam * H.w u v := hs.trans (mul_le_mul_of_nonneg_right hF h0.le)
    _ = 2 * H.w u v / lam := by ring

set_option linter.deprecated false in
/-- **Tree distribution.** A finite family of rooted spanning trees with weights
`p` such that the expected number of tree edges crossing any `S` is at most
`2·cut_H(S)/λ`. -/
theorem exists_tree_family (H : WeightedGraph V) {lam : ℝ} (hlam : 0 < lam)
    (hcut : ∀ S, ProperShore S → lam ≤ H.cut S) (hV : Nonempty V) :
    ∃ (ι : Type) (_ : Fintype ι) (p : ι → ℝ) (T : ι → RootedTree V),
      (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧
      ∀ S, ∑ i, p i * ((T i).crossSet S).card ≤ 2 * H.cut S / lam := by
  obtain ⟨a, ha, hbound⟩ := exists_good_dist H hlam hcut hV
  obtain ⟨r⟩ := hV
  refine ⟨Strat H, inferInstance, a, fun F => bfsTree F.1 r F.2.2, ha.1, ha.2, fun S => ?_⟩
  have hcount : ∀ F : Strat H, (((bfsTree F.1 r F.2.2).crossSet S).card : ℝ) ≤
      ∑ e ∈ S ×ˢ Sᶜ, ind F.1 e := by
    intro F
    have := card_crossSet_le (bfsTree F.1 r F.2.2) F.1 (fun v hv => bfsTree_adj F.2.2 hv) S
    calc _ ≤ (((S ×ˢ Sᶜ).filter fun e => Adj F.1 e.1 e.2).card : ℝ) := by exact_mod_cast this
      _ = _ := by rw [Finset.natCast_card_filter]; rfl
  calc ∑ F, a F * (((bfsTree F.1 r F.2.2).crossSet S).card : ℝ)
      ≤ ∑ F, a F * ∑ e ∈ S ×ˢ Sᶜ, ind F.1 e :=
        Finset.sum_le_sum fun F _ => mul_le_mul_of_nonneg_left (hcount F) (ha.1 F)
    _ = ∑ e ∈ S ×ˢ Sᶜ, ∑ F, a F * ind F.1 e := by
        simp only [Finset.mul_sum]; exact Finset.sum_comm
    _ ≤ ∑ e ∈ S ×ˢ Sᶜ, 2 * H.w e.1 e.2 / lam := Finset.sum_le_sum fun e _ => hbound e.1 e.2
    _ = 2 * H.cut S / lam := by
        rw [← Finset.sum_div, ← Finset.mul_sum, Finset.sum_product, WeightedGraph.cut]

/-- **Markov.** The weight on trees crossing `S` at least three times. -/
theorem markov_three {ι : Type} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (X : ι → ℕ) :
    ∑ i, (if 3 ≤ X i then p i else 0) ≤ (∑ i, p i * X i) / 3 := by
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3), Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  split_ifs with h
  · have : (3 : ℝ) ≤ X i := by exact_mod_cast h
    nlinarith [hp i]
  · simp only [zero_mul]; exact mul_nonneg (hp i) (Nat.cast_nonneg _)

/-- **Tree distribution as a PMF.** Trees crossing `S` at least three times have
mass at most `2·cut_H(S)/(3λ)`. -/
theorem exists_tree_pmf (H : WeightedGraph V) {lam : ℝ} (hlam : 0 < lam)
    (hcut : ∀ S, ProperShore S → lam ≤ H.cut S) (hV : Nonempty V) :
    ∃ P : PMF (RootedTree V), ∀ S, Probability.mass P (fun T => 3 ≤ (T.crossSet S).card) ≤
      ENNReal.ofReal (2 * H.cut S / (3 * lam)) := by
  obtain ⟨ι, _, p, T, hp0, hp1, hE⟩ := exists_tree_family H hlam hcut hV
  have hsum : ∑ i, ENNReal.ofReal (p i) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hp0 i), hp1, ENNReal.ofReal_one]
  refine ⟨(PMF.ofFintype (fun i => ENNReal.ofReal (p i)) hsum).map T, fun S => ?_⟩
  rw [Probability.mass_map, Probability.mass_eq_tsum, tsum_fintype]
  have hconv : ∀ b, (PMF.ofFintype (fun i => ENNReal.ofReal (p i)) hsum) b =
      ENNReal.ofReal (p b) := fun b => rfl
  simp only [hconv]
  rw [Finset.sum_congr rfl (g := fun i => ENNReal.ofReal
    (if 3 ≤ ((T i).crossSet S).card then p i else 0)) (fun i _ => by split_ifs <;> simp),
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => by split_ifs <;> simp [hp0 i])]
  apply ENNReal.ofReal_le_ofReal
  calc _ ≤ (∑ i, p i * ((T i).crossSet S).card) / 3 :=
        markov_three p hp0 fun i => ((T i).crossSet S).card
    _ ≤ (2 * H.cut S / lam) / 3 := by gcongr; exact hE S
    _ = _ := by field_simp

end
end TreePacking
end CutQueryComplexity
