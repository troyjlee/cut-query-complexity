import CutQueryComplexity.Hierarchy.Completion

/-! # Lemma 18 for real-valued labellings

The completion error bound of Lemma 18 holds with the representation cost replaced by
the cost of any real-valued labelling that extends the indicator of `S` on the leaves.
Fractional labellings are what the elementary guard graph of `Hierarchy.Guard`
produces, so this form avoids a rounding (coarea) argument.
-/

namespace CutQueryComplexity
namespace Hierarchy

open TwoRespecting WeightedGraph

variable {V : Type} [Fintype V] [DecidableEq V]

namespace Hier

variable {N : Type} [Fintype N] [DecidableEq N] {H : Hier V N}

/-- A real labelling extends `S` when it is the indicator of `S` on the leaves. -/
def ExtendsR (H : Hier V N) (S : Finset V) (a : N → ℝ) : Prop :=
  ∀ v, a (H.leaf v) = ind S v

theorem indicator_decomp_real {S : Finset V} {a : N → ℝ} (h : H.ExtendsR S a) (v : V) :
    ind S v = a H.T.root +
      ∑ x ∈ H.edges, ind (H.cluster x) v * (a x - a (H.T.parent x)) := by
  have := telescope (H := H) a _ (H.leaf v) le_rfl
  rw [← h v, this]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [ind, mem_cluster]
  split_ifs <;> ring

omit [Fintype V] [Fintype N] [DecidableEq N] in
theorem extendsR_toReal {S : Finset V} {ℓ : N → Bool} (h : H.Extends S ℓ) :
    H.ExtendsR S (toReal ℓ) := fun v => by
  simp only [toReal, h v, ind, decide_eq_true_eq]

/-- **Lemma 18, real labellings.** -/
theorem cut_error_le_real (F G : WeightedGraph V) {η lam : ℝ} (hη : 0 ≤ η) (hlam : 0 < lam)
    (hd : ∀ x, ProperCluster (H.cluster x) → lam ≤ H.canon G x)
    (hM : ∀ x ∈ H.edges, ∀ y ∈ H.edges,
      |interact F (H.cluster x) (H.cluster y) - interact G (H.cluster x) (H.cluster y)| ≤
        η * min (H.canon G x) (H.canon G y))
    {S : Finset V} {a : N → ℝ} (ha : H.ExtendsR S a) :
    |F.cut S - G.cut S| ≤ η * H.labelCost (H.canon G) a ^ 2 / lam := by
  classical
  set δ : N → ℝ := fun x => a x - a (H.T.parent x)
  set L := H.labelCost (H.canon G) a
  have hdec : ∀ u, ind S u = a H.T.root + ∑ x ∈ H.edges, ind (H.cluster x) u * δ x :=
    fun u => indicator_decomp_real ha u
  have hF := cutForm_expand F H.edges (fun x => ind (H.cluster x)) δ _ (ind S) hdec
  have hG := cutForm_expand G H.edges (fun x => ind (H.cluster x)) δ _ (ind S) hdec
  rw [cutForm_ind_self] at hF hG
  have hcap : ∀ x, 0 ≤ H.canon G x := fun x => G.cut_nonneg _
  set P := H.edges.filter fun x => ProperCluster (H.cluster x)
  have hterm : ∀ x ∈ H.edges, ∀ y ∈ H.edges,
      |δ x * δ y * (interact F (H.cluster x) (H.cluster y) -
          interact G (H.cluster x) (H.cluster y))| ≤
        if x ∈ P ∧ y ∈ P then η * (|δ x| * (|δ y| * H.canon G y)) else 0 := by
    intro x hx y hy
    split_ifs with hxy
    · rw [abs_mul, abs_mul]
      calc |δ x| * |δ y| * |interact F (H.cluster x) (H.cluster y) -
              interact G (H.cluster x) (H.cluster y)|
          ≤ |δ x| * |δ y| * (η * min (H.canon G x) (H.canon G y)) := by
            gcongr
            exact hM x hx y hy
        _ ≤ |δ x| * |δ y| * (η * H.canon G y) := by
            gcongr
            exact min_le_right _ _
        _ = η * (|δ x| * (|δ y| * H.canon G y)) := by ring
    · rw [abs_nonpos_iff]
      have hx' : x ∈ P ↔ ProperCluster (H.cluster x) := by simp [P, hx]
      have hy' : y ∈ P ↔ ProperCluster (H.cluster y) := by simp [P, hy]
      rw [hx', hy'] at hxy
      by_cases h3 : ProperCluster (H.cluster x)
      · have h4 : ¬ ProperCluster (H.cluster y) := fun h4 => hxy ⟨h3, h4⟩
        have hc := ind_const_of_not_proper h4
        simp only [interact]
        rw [cutForm_comm F, cutForm_comm G, cutForm_const_left F hc, cutForm_const_left G hc]
        ring
      · have hc := ind_const_of_not_proper h3
        simp only [interact]
        rw [cutForm_const_left F hc, cutForm_const_left G hc]
        ring
  have hPE : P ⊆ H.edges := Finset.filter_subset _ _
  have hdiff : |F.cut S - G.cut S| ≤
      ∑ x ∈ P, ∑ y ∈ P, η * (|δ x| * (|δ y| * H.canon G y)) := by
    have h2 : 2 * (F.cut S - G.cut S) = ∑ x ∈ H.edges, ∑ y ∈ H.edges,
        δ x * δ y * (2 * (interact F (H.cluster x) (H.cluster y) -
          interact G (H.cluster x) (H.cluster y))) := by
      rw [mul_sub, hF, hG, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only [interact]; ring
    have hbound : |∑ x ∈ H.edges, ∑ y ∈ H.edges, δ x * δ y *
        (interact F (H.cluster x) (H.cluster y) - interact G (H.cluster x) (H.cluster y))| ≤
        ∑ x ∈ H.edges, ∑ y ∈ H.edges,
          (if x ∈ P ∧ y ∈ P then η * (|δ x| * (|δ y| * H.canon G y)) else 0) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x hx => ?_)
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y hy => hterm x hx y hy)
    have hconv : ∑ x ∈ H.edges, ∑ y ∈ H.edges,
        (if x ∈ P ∧ y ∈ P then η * (|δ x| * (|δ y| * H.canon G y)) else 0) =
        ∑ x ∈ P, ∑ y ∈ P, η * (|δ x| * (|δ y| * H.canon G y)) := by
      rw [← Finset.sum_subset hPE (fun x _ hx => Finset.sum_eq_zero fun y _ => by simp [hx])]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [← Finset.sum_subset hPE (fun y _ hy => by simp [hy])]
      exact Finset.sum_congr rfl fun y hy => by simp [hx, hy]
    have heq : F.cut S - G.cut S = ∑ x ∈ H.edges, ∑ y ∈ H.edges, δ x * δ y *
        (interact F (H.cluster x) (H.cluster y) - interact G (H.cluster x) (H.cluster y)) := by
      have : ∑ x ∈ H.edges, ∑ y ∈ H.edges, δ x * δ y * (2 * (interact F (H.cluster x)
          (H.cluster y) - interact G (H.cluster x) (H.cluster y))) =
          2 * ∑ x ∈ H.edges, ∑ y ∈ H.edges, δ x * δ y *
            (interact F (H.cluster x) (H.cluster y) - interact G (H.cluster x) (H.cluster y)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => by ring
      linarith
    rw [heq, ← hconv]
    exact hbound
  -- `∑_P |δ| d ≤ L` and `λ ∑_P |δ| ≤ L`
  have hsumP : ∑ y ∈ P, |δ y| * H.canon G y ≤ L := by
    unfold L labelCost
    calc ∑ y ∈ P, |δ y| * H.canon G y ≤ ∑ y ∈ H.edges, |δ y| * H.canon G y :=
          Finset.sum_le_sum_of_subset_of_nonneg hPE
            fun y _ _ => mul_nonneg (abs_nonneg _) (hcap y)
      _ = _ := Finset.sum_congr rfl fun y _ => mul_comm _ _
  have hmassP : (∑ x ∈ P, |δ x|) * lam ≤ L := by
    rw [Finset.sum_mul]
    refine (Finset.sum_le_sum fun x hx => ?_).trans hsumP
    exact mul_le_mul_of_nonneg_left (hd x (Finset.mem_filter.mp hx).2) (abs_nonneg _)
  have hA0 : 0 ≤ ∑ x ∈ P, |δ x| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hL0 : 0 ≤ L := le_trans (by positivity) hmassP
  calc |F.cut S - G.cut S| ≤ ∑ x ∈ P, ∑ y ∈ P, η * (|δ x| * (|δ y| * H.canon G y)) := hdiff
    _ = (∑ x ∈ P, |δ x|) * (η * ∑ y ∈ P, |δ y| * H.canon G y) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => by ring
    _ ≤ (L / lam) * (η * L) := by
        have h1 : ∑ x ∈ P, |δ x| ≤ L / lam := by rw [le_div_iff₀ hlam]; exact hmassP
        have h2 : η * ∑ y ∈ P, |δ y| * H.canon G y ≤ η * L :=
          mul_le_mul_of_nonneg_left hsumP hη
        have h3 : 0 ≤ η * ∑ y ∈ P, |δ y| * H.canon G y :=
          mul_nonneg hη (Finset.sum_nonneg fun y _ => mul_nonneg (abs_nonneg _) (hcap y))
        exact mul_le_mul h1 h2 h3 (div_nonneg hL0 hlam.le)
    _ = η * L ^ 2 / lam := by ring

variable [LinearOrder N]

/-- The completion error against any real extension of `S`. -/
theorem completion_cut_error_real (G : WeightedGraph V) {q : ℕ} (hq : 1 ≤ q)
    (hlam : 0 < mincutValue G) {S : Finset V} {a : N → ℝ} (ha : H.ExtendsR S a) :
    |((H.completion q).eval G.cut).cut S - G.cut S| ≤
      2 / q * H.labelCost (H.canon G) a ^ 2 / mincutValue G := by
  obtain ⟨-, hM, -⟩ := completion_spec (H := H) G hq
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have := cut_error_le_real (H := H) ((H.completion q).eval G.cut) G (η := 2 / q)
    (by positivity) hlam (fun x hx => mincutValue_le G hx) hM ha
  simpa [mul_div_assoc] using this

end Hier
end Hierarchy
end CutQueryComplexity
