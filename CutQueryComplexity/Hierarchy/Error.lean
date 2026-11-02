import CutQueryComplexity.Hierarchy.Basic

/-! # Representation cost controls completion error (Lemma 18)

The cut form of a weighted graph is the Laplacian bilinear form
`Q(f,g) = ½ ∑ w(u,v) (f u − f v)(g u − g v)`, so `Q(1_S, 1_S) = c(S)` and
`M(A,B) = Q(1_A, 1_B)`. If a graph `F` matches `G` on these cluster interactions up
to `η · min(d_A, d_B)`, then every cut differs by at most `η R(S)² / λ`, where every
proper cluster has canonical capacity at least `λ`. The bound has no dependence on
the depth of the hierarchy.
-/

namespace CutQueryComplexity
namespace Hierarchy

open TwoRespecting WeightedGraph

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Twice the Laplacian bilinear form of a weighted graph. -/
def cutForm (G : WeightedGraph V) (f g : V → ℝ) : ℝ :=
  ∑ u, ∑ v, G.w u v * ((f u - f v) * (g u - g v))

/-- Indicator of a vertex set. -/
def ind (S : Finset V) : V → ℝ := fun v => if v ∈ S then 1 else 0

/-- Cluster interaction `M(A,B) = 1_Aᵀ L 1_B`. -/
noncomputable def interact (G : WeightedGraph V) (A B : Finset V) : ℝ :=
  cutForm G (ind A) (ind B) / 2

theorem cutForm_ind_self (G : WeightedGraph V) (S : Finset V) :
    cutForm G (ind S) (ind S) = 2 * G.cut S := by
  have h := Hier.two_mul_cut_eq_sum_abs G S
  unfold cutForm ind
  have : ∀ u v, G.w u v * (((if u ∈ S then (1 : ℝ) else 0) - (if v ∈ S then 1 else 0)) *
      ((if u ∈ S then (1 : ℝ) else 0) - (if v ∈ S then 1 else 0))) =
      G.w u v * |(if u ∈ S then (1 : ℝ) else 0) - (if v ∈ S then 1 else 0)| := by
    intro u v
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp [hu, hv]
  simp only [this]
  linarith

omit [DecidableEq V] in
theorem cutForm_const_left (G : WeightedGraph V) {g : V → ℝ} (hg : ∀ u v, g u = g v)
    (h : V → ℝ) : cutForm G g h = 0 :=
  Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun v _ => by rw [hg u v]; ring

omit [DecidableEq V] in
theorem cutForm_comm (G : WeightedGraph V) (f g : V → ℝ) : cutForm G f g = cutForm G g f := by
  unfold cutForm
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring

omit [DecidableEq V] in
/-- Expanding the form of a signed combination of functions. -/
theorem cutForm_expand (G : WeightedGraph V) {ι : Type} (I : Finset ι) (g : ι → V → ℝ)
    (a : ι → ℝ) (c : ℝ) (f : V → ℝ) (hf : ∀ u, f u = c + ∑ i ∈ I, g i u * a i) :
    cutForm G f f = ∑ i ∈ I, ∑ j ∈ I, a i * a j * cutForm G (g i) (g j) := by
  have hd : ∀ u v, f u - f v = ∑ i ∈ I, a i * (g i u - g i v) := by
    intro u v
    rw [hf u, hf v, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hterm : ∀ u v, G.w u v * ((f u - f v) * (f u - f v)) =
      ∑ i ∈ I, ∑ j ∈ I, a i * a j * (G.w u v * ((g i u - g i v) * (g j u - g j v))) := by
    intro u v
    rw [hd u v, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  unfold cutForm
  simp only [hterm]
  calc ∑ u, ∑ v, ∑ i ∈ I, ∑ j ∈ I, a i * a j * (G.w u v * ((g i u - g i v) * (g j u - g j v)))
      = ∑ u, ∑ i ∈ I, ∑ j ∈ I, ∑ v, a i * a j * (G.w u v * ((g i u - g i v) * (g j u - g j v))) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i ∈ I, ∑ j ∈ I, ∑ u, ∑ v,
          a i * a j * (G.w u v * ((g i u - g i v) * (g j u - g j v))) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.mul_sum]

namespace Hier

variable {N : Type} [Fintype N] [DecidableEq N] {H : Hier V N}

/-- A cluster is proper when it is neither empty nor everything. -/
def ProperCluster (A : Finset V) : Prop := A.Nonempty ∧ A ≠ Finset.univ

theorem ind_const_of_not_proper {A : Finset V} (h : ¬ ProperCluster A) :
    ∀ u v, ind A u = ind A v := by
  intro u v
  unfold ProperCluster at h
  by_cases hne : A.Nonempty
  · have hA : A = Finset.univ := by by_contra h'; exact h ⟨hne, h'⟩
    simp [ind, hA]
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    simp [ind, hne]

/-- **Lemma 18.** If `F` matches `G` on all cluster interactions up to
`η · min(d_x, d_y)`, and every proper cluster has canonical capacity at least `λ > 0`,
then `|c_F(S) − c_G(S)| ≤ η R(S)² / λ` for every shore. -/
theorem cut_error_le (F G : WeightedGraph V) {η lam : ℝ} (hη : 0 ≤ η) (hlam : 0 < lam)
    (hd : ∀ x, ProperCluster (H.cluster x) → lam ≤ H.canon G x)
    (hM : ∀ x ∈ H.edges, ∀ y ∈ H.edges,
      |interact F (H.cluster x) (H.cluster y) - interact G (H.cluster x) (H.cluster y)| ≤
        η * min (H.canon G x) (H.canon G y))
    (S : Finset V) :
    |F.cut S - G.cut S| ≤ η * H.rep (H.canon G) S ^ 2 / lam := by
  classical
  obtain ⟨ℓ, hℓ, hR⟩ := H.exists_rep_eq (H.canon G) S
  set δ : N → ℝ := fun x => toReal ℓ x - toReal ℓ (H.T.parent x)
  set R := H.rep (H.canon G) S
  have hdec : ∀ u, ind S u = toReal ℓ H.T.root + ∑ x ∈ H.edges, ind (H.cluster x) u * δ x :=
    fun u => indicator_decomp hℓ u
  have hF := cutForm_expand F H.edges (fun x => ind (H.cluster x)) δ _ (ind S) hdec
  have hG := cutForm_expand G H.edges (fun x => ind (H.cluster x)) δ _ (ind S) hdec
  rw [cutForm_ind_self] at hF hG
  have hδcases : ∀ x, δ x = 0 ∨ |δ x| = 1 := fun x => by
    simp only [δ, toReal]
    cases ℓ x <;> cases ℓ (H.T.parent x) <;> norm_num
  have hδ : ∀ x, |δ x| ≤ 1 := fun x => by
    rcases hδcases x with h | h
    · rw [h]; norm_num
    · rw [h]
  have hcap : ∀ x, 0 ≤ H.canon G x := fun x => G.cut_nonneg _
  -- the relevant edges: labelled change and proper cluster
  set P := H.edges.filter fun x => δ x ≠ 0 ∧ ProperCluster (H.cluster x)
  have hterm : ∀ x ∈ H.edges, ∀ y ∈ H.edges,
      |δ x * δ y * (interact F (H.cluster x) (H.cluster y) -
          interact G (H.cluster x) (H.cluster y))| ≤
        if x ∈ P ∧ y ∈ P then η * H.canon G y else 0 := by
    intro x hx y hy
    split_ifs with hxy
    · rw [abs_mul, abs_mul]
      calc |δ x| * |δ y| * |interact F (H.cluster x) (H.cluster y) -
              interact G (H.cluster x) (H.cluster y)|
          ≤ 1 * 1 * (η * min (H.canon G x) (H.canon G y)) := by
            gcongr
            · exact hδ x
            · exact hδ y
            · exact hM x hx y hy
        _ ≤ η * H.canon G y := by
            rw [one_mul, one_mul]
            exact mul_le_mul_of_nonneg_left (min_le_right _ _) hη
    · -- one of the two factors vanishes
      rw [abs_nonpos_iff]
      have hx' : x ∈ P ↔ δ x ≠ 0 ∧ ProperCluster (H.cluster x) := by simp [P, hx]
      have hy' : y ∈ P ↔ δ y ≠ 0 ∧ ProperCluster (H.cluster y) := by simp [P, hy]
      rw [hx', hy'] at hxy
      by_cases h1 : δ x = 0
      · simp [h1]
      by_cases h2 : δ y = 0
      · simp [h2]
      by_cases h3 : ProperCluster (H.cluster x)
      · have h4 : ¬ ProperCluster (H.cluster y) := fun h4 => hxy ⟨⟨h1, h3⟩, h2, h4⟩
        have hc := ind_const_of_not_proper h4
        simp only [interact]
        rw [cutForm_comm F, cutForm_comm G, cutForm_const_left F hc, cutForm_const_left G hc]
        ring
      · have hc := ind_const_of_not_proper h3
        simp only [interact]
        rw [cutForm_const_left F hc, cutForm_const_left G hc]
        ring
  have hPE : P ⊆ H.edges := Finset.filter_subset _ _
  have hdiff : |F.cut S - G.cut S| ≤ ∑ x ∈ P, ∑ y ∈ P, η * H.canon G y := by
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
        ∑ x ∈ H.edges, ∑ y ∈ H.edges, (if x ∈ P ∧ y ∈ P then η * H.canon G y else 0) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x hx => ?_)
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y hy => hterm x hx y hy)
    have hconv : ∑ x ∈ H.edges, ∑ y ∈ H.edges, (if x ∈ P ∧ y ∈ P then η * H.canon G y else 0) =
        ∑ x ∈ P, ∑ y ∈ P, η * H.canon G y := by
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
  -- `∑_{P} d ≤ R` and `|P| λ ≤ R`
  have hsumP : ∑ y ∈ P, H.canon G y ≤ R := by
    rw [hR]
    unfold labelCost
    calc ∑ y ∈ P, H.canon G y = ∑ y ∈ P, H.canon G y * |δ y| := by
          refine Finset.sum_congr rfl fun y hy => ?_
          have hy' := (Finset.mem_filter.mp hy).2.1
          have : |δ y| = 1 := (hδcases y).resolve_left hy'
          rw [this, mul_one]
      _ ≤ ∑ y ∈ H.edges, H.canon G y * |δ y| :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun y _ _ => mul_nonneg (hcap y) (abs_nonneg _)
  have hcardP : (P.card : ℝ) * lam ≤ R := by
    have : (P.card : ℝ) * lam = ∑ _y ∈ P, lam := by rw [Finset.sum_const, nsmul_eq_mul]
    rw [this]
    exact (Finset.sum_le_sum fun y hy => hd y (Finset.mem_filter.mp hy).2.2).trans hsumP
  have hR0 : 0 ≤ R := le_trans (by positivity) hcardP
  calc |F.cut S - G.cut S| ≤ ∑ x ∈ P, ∑ y ∈ P, η * H.canon G y := hdiff
    _ = (P.card : ℝ) * (η * ∑ y ∈ P, H.canon G y) := by
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
    _ ≤ (R / lam) * (η * R) := by
        have h1 : (P.card : ℝ) ≤ R / lam := by rw [le_div_iff₀ hlam]; exact hcardP
        have h2 : η * ∑ y ∈ P, H.canon G y ≤ η * R := mul_le_mul_of_nonneg_left hsumP hη
        have h3 : 0 ≤ η * ∑ y ∈ P, H.canon G y :=
          mul_nonneg hη (Finset.sum_nonneg fun y _ => hcap y)
        exact mul_le_mul h1 h2 h3 (div_nonneg hR0 hlam.le)
    _ = η * R ^ 2 / lam := by ring

end Hier
end Hierarchy
end CutQueryComplexity
