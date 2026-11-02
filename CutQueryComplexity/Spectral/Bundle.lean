import CutQueryComplexity.Spectral.Energy
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # Pair-disjoint paths dominate a pair Laplacian (D2; source `lem:leverage`)

A pair set `S` is a graph (`pairGraph S`). Along any walk, `|x_u − x_v|` is at most the sum of
`|x_a − x_b|` over its edges (`abs_sub_le_walk`); along a trail every edge counts once
(`abs_sub_le_trail`).

`sq_le_of_disjoint_paths` is weighted Cauchy–Schwarz over `t` pair-disjoint edge sets, each of
total resistance at most `R`: `t² (x_u − x_v)² ≤ t R Σ_{f∈S} (x_a − x_b)²/r_f`.

`pair_dominated` is the bundle bound used by sampling, proved directly without effective
resistances: if conductances are `ω_f = s c_f w_f` with `1 ≤ c_f` on the current support `E'`
and `c_e ≤ C`, and each of `t` pair-disjoint spanners `S_j ⊆ E'` contains a `u`–`v` trail of
length `Σ 1/w_f ≤ α / w_e`, then for every real vector

  `ω_e (x_u − x_v)² ≤ (C α / t) Σ_{f∈E'} ω_f (x_a − x_b)²`,

that is `L_e ⪯ (C α / t) L'` (`pair_dominated_loewner`). Trails may share vertices.
-/

namespace CutQueryComplexity
namespace Spectral

open Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-- `|x u − x v|`, a function of the unordered pair. -/
def pairAbs (x : V → ℝ) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun u v => |x u - x v|, fun _ _ => abs_sub_comm _ _⟩

omit [Fintype V] [DecidableEq V] in
@[simp] theorem pairAbs_mk (x : V → ℝ) (u v : V) : pairAbs x s(u, v) = |x u - x v| := rfl

omit [Fintype V] [DecidableEq V] in
theorem pairAbs_nonneg (x : V → ℝ) (e : Sym2 V) : 0 ≤ pairAbs x e := by
  induction e using Sym2.ind with | h u v => exact abs_nonneg _

omit [Fintype V] [DecidableEq V] in
theorem pairAbs_sq (x : V → ℝ) (e : Sym2 V) : pairAbs x e ^ 2 = pairSq x e := by
  induction e using Sym2.ind with | h u v => simp [sq_abs]

/-- The graph whose edges are the (non-diagonal) pairs of `S`. -/
abbrev pairGraph (S : Finset (Sym2 V)) : SimpleGraph V := SimpleGraph.fromEdgeSet (S : Set (Sym2 V))

omit [Fintype V] [DecidableEq V] in
theorem mem_of_mem_edges {S : Finset (Sym2 V)} {u v : V} (p : (pairGraph S).Walk u v)
    {f : Sym2 V} (hf : f ∈ p.edges) : f ∈ S := by
  have := p.edges_subset_edgeSet hf
  rw [SimpleGraph.edgeSet_fromEdgeSet] at this
  exact this.1

omit [Fintype V] [DecidableEq V] in
/-- The triangle inequality along a walk. -/
theorem abs_sub_le_walk {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (x : V → ℝ) :
    |x u - x v| ≤ (p.edges.map (pairAbs x)).sum := by
  induction p with
  | nil => simp
  | @cons a b c h p ih =>
      rw [SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons, pairAbs_mk]
      calc |x a - x c| = |(x a - x b) + (x b - x c)| := by ring_nf
        _ ≤ |x a - x b| + |x b - x c| := abs_add_le _ _
        _ ≤ _ := by linarith

omit [Fintype V] in
/-- Along a trail every edge counts once. -/
theorem abs_sub_le_trail {G : SimpleGraph V} {u v : V} {p : G.Walk u v} (hp : p.IsTrail)
    (x : V → ℝ) : |x u - x v| ≤ ∑ f ∈ p.edges.toFinset, pairAbs x f := by
  rw [List.sum_toFinset _ hp.edges_nodup]
  exact abs_sub_le_walk p x

omit [Fintype V] in
/-- **Weighted Cauchy–Schwarz over pair-disjoint paths.** -/
theorem sq_le_of_disjoint_paths {ι : Type} (J : Finset ι) (F : ι → Finset (Sym2 V))
    (hdisj : (J : Set ι).PairwiseDisjoint F) {S : Finset (Sym2 V)} (hFS : ∀ j ∈ J, F j ⊆ S)
    {r : Sym2 V → ℝ} (hr : ∀ f ∈ S, 0 < r f) {R : ℝ} (hR : ∀ j ∈ J, ∑ f ∈ F j, r f ≤ R)
    {x : V → ℝ} {u v : V} (hpath : ∀ j ∈ J, |x u - x v| ≤ ∑ f ∈ F j, pairAbs x f) :
    (J.card : ℝ) ^ 2 * (x u - x v) ^ 2 ≤ J.card * R * ∑ f ∈ S, pairSq x f / r f := by
  set B := J.biUnion F
  have hBS : B ⊆ S := biUnion_subset.mpr hFS
  have hX : 0 ≤ ∑ f ∈ S, pairSq x f / r f :=
    sum_nonneg fun f hf => div_nonneg (pairSq_nonneg x f) (hr f hf).le
  -- the sum of absolute differences over the union
  have h1 : (J.card : ℝ) * |x u - x v| ≤ ∑ f ∈ B, pairAbs x f := by
    rw [sum_biUnion hdisj]
    calc (J.card : ℝ) * |x u - x v| = ∑ j ∈ J, |x u - x v| := by simp
      _ ≤ _ := sum_le_sum hpath
  have h2 : ∑ f ∈ B, r f ≤ J.card * R := by
    rw [sum_biUnion hdisj]
    calc ∑ j ∈ J, ∑ f ∈ F j, r f ≤ ∑ j ∈ J, R := sum_le_sum hR
      _ = J.card * R := by simp
  have hRJ : 0 ≤ (J.card : ℝ) * R := by
    rcases J.eq_empty_or_nonempty with hJ | ⟨j, hj⟩
    · simp [hJ]
    · exact le_trans (sum_nonneg fun f hf => (hr f (hFS j hj hf)).le)
        ((sum_le_sum_of_subset_of_nonneg (subset_biUnion_of_mem F hj)
          fun f hf _ => (hr f (hBS hf)).le).trans h2)
  have hLHS : (J.card : ℝ) ^ 2 * (x u - x v) ^ 2 = ((J.card : ℝ) * |x u - x v|) ^ 2 := by
    rw [mul_pow, sq_abs]
  rw [hLHS]
  rcases B.eq_empty_or_nonempty with hB | hB
  · have : (J.card : ℝ) * |x u - x v| ≤ 0 := by simpa [hB] using h1
    have h0 : 0 ≤ (J.card : ℝ) * |x u - x v| := by positivity
    have : (J.card : ℝ) * |x u - x v| = 0 := le_antisymm this h0
    rw [this]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact mul_nonneg hRJ hX
  · have hrB : 0 < ∑ f ∈ B, r f := sum_pos (fun f hf => hr f (hBS hf)) hB
    have hcs := sq_sum_div_le_sum_sq_div B (pairAbs x) (fun f hf => hr f (hBS hf))
    rw [div_le_iff₀ hrB] at hcs
    have hsub : ∑ f ∈ B, pairAbs x f ^ 2 / r f ≤ ∑ f ∈ S, pairSq x f / r f := by
      simp only [pairAbs_sq]
      exact sum_le_sum_of_subset_of_nonneg hBS fun f hf _ =>
        div_nonneg (pairSq_nonneg x f) (hr f hf).le
    have hsq : ((J.card : ℝ) * |x u - x v|) ^ 2 ≤ (∑ f ∈ B, pairAbs x f) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    calc ((J.card : ℝ) * |x u - x v|) ^ 2 ≤ (∑ f ∈ B, pairAbs x f) ^ 2 := hsq
      _ ≤ (∑ f ∈ B, pairAbs x f ^ 2 / r f) * ∑ f ∈ B, r f := hcs
      _ ≤ (∑ f ∈ S, pairSq x f / r f) * (J.card * R) :=
          mul_le_mul hsub h2 hrB.le hX
      _ = _ := by ring

omit [Fintype V] in
/-- **Bundle domination.** `t` pair-disjoint spanners give `L_e ⪯ (C α / t) L'`. -/
theorem pair_dominated {ι : Type} (J : Finset ι) (hJ : J.Nonempty) (S : ι → Finset (Sym2 V))
    (hdisj : (J : Set ι).PairwiseDisjoint S) {E' : Finset (Sym2 V)} (hSE : ∀ j ∈ J, S j ⊆ E')
    {s : ℝ} (hs : 0 < s) {w c : Sym2 V → ℝ} (hw : ∀ f ∈ E', 0 < w f) (hc : ∀ f ∈ E', 1 ≤ c f)
    {C α : ℝ} {u v : V} (he : s(u, v) ∈ E') (hcC : c s(u, v) ≤ C)
    (hpaths : ∀ j ∈ J, ∃ p : (pairGraph (S j)).Walk u v,
      p.IsTrail ∧ (p.edges.map fun f => 1 / w f).sum ≤ α / w s(u, v))
    (x : V → ℝ) :
    s * c s(u, v) * w s(u, v) * pairSq x s(u, v) ≤
      C * α / J.card * energy (fun f => s * c f * w f) E' x := by
  classical
  have hwe := hw _ he
  have hce : 0 ≤ c s(u, v) := le_trans zero_le_one (hc _ he)
  have hJc : (0 : ℝ) < J.card := by exact_mod_cast hJ.card_pos
  choose p hp using fun j (hj : j ∈ J) => hpaths j hj
  -- the edge sets of the chosen trails
  let F : ι → Finset (Sym2 V) := fun j =>
    if hj : j ∈ J then (p j hj).edges.toFinset else ∅
  have hFS : ∀ j ∈ J, F j ⊆ S j := fun j hj f hf => by
    simp only [F, hj, ↓reduceDIte, List.mem_toFinset] at hf
    exact mem_of_mem_edges _ hf
  have hFdisj : (J : Set ι).PairwiseDisjoint F := fun i hi j hj hij =>
    (hdisj hi hj hij).mono (hFS i hi) (hFS j hj)
  set R := (1 / s) * (α / w s(u, v))
  have hr : ∀ f ∈ E', 0 < 1 / (s * w f) := fun f hf => by
    have := hw f hf; positivity
  have hR : ∀ j ∈ J, ∑ f ∈ F j, 1 / (s * w f) ≤ R := fun j hj => by
    simp only [F, hj, ↓reduceDIte]
    rw [List.sum_toFinset _ (hp j hj).1.edges_nodup]
    have hsum : ((p j hj).edges.map fun f => 1 / (s * w f)).sum =
        (1 / s) * ((p j hj).edges.map fun f => 1 / w f).sum := by
      rw [← List.sum_map_mul_left]; congr 1
      exact List.map_congr_left fun f _ => by field_simp
    rw [hsum]
    exact mul_le_mul_of_nonneg_left (hp j hj).2 (by positivity)
  have hpath : ∀ j ∈ J, |x u - x v| ≤ ∑ f ∈ F j, pairAbs x f := fun j hj => by
    simp only [F, hj, ↓reduceDIte]
    exact abs_sub_le_trail (hp j hj).1 x
  have hcore := sq_le_of_disjoint_paths J F hFdisj
    (fun j hj => (hFS j hj).trans (hSE j hj)) hr hR hpath
  -- compare the resistance-weighted energy with the conductance energy
  have hcmp : ∑ f ∈ E', pairSq x f / (1 / (s * w f)) ≤ energy (fun f => s * c f * w f) E' x := by
    unfold energy
    refine sum_le_sum fun f hf => ?_
    have hwf := hw f hf; have hcf := hc f hf; have hq := pairSq_nonneg x f
    rw [one_div, div_inv_eq_mul]
    show pairSq x f * (s * w f) ≤ s * c f * w f * pairSq x f
    have hk : 0 ≤ s * w f * pairSq x f := mul_nonneg (mul_nonneg hs.le hwf.le) hq
    nlinarith [mul_nonneg (sub_nonneg.mpr hcf) hk]
  have hd : (x u - x v) ^ 2 ≤ R / J.card * energy (fun f => s * c f * w f) E' x := by
    have hR0 : 0 ≤ R := by
      obtain ⟨j, hj⟩ := hJ
      exact le_trans (sum_nonneg fun f hf => (hr f (hSE j hj (hFS j hj hf))).le) (hR j hj)
    have := hcore.trans (mul_le_mul_of_nonneg_left hcmp (by positivity))
    rw [div_mul_eq_mul_div, le_div_iff₀ hJc]
    nlinarith
  rw [pairSq_mk]
  calc s * c s(u, v) * w s(u, v) * (x u - x v) ^ 2
      ≤ s * C * w s(u, v) * (x u - x v) ^ 2 := by
        have := sq_nonneg (x u - x v)
        have : s * c s(u, v) * w s(u, v) ≤ s * C * w s(u, v) := by
          have := mul_le_mul_of_nonneg_left hcC hs.le
          nlinarith
        nlinarith
    _ ≤ s * C * w s(u, v) * (R / J.card * energy (fun f => s * c f * w f) E' x) := by
        refine mul_le_mul_of_nonneg_left hd ?_
        have : 0 ≤ C := hce.trans hcC
        positivity
    _ = C * α / J.card * energy (fun f => s * c f * w f) E' x := by
        simp only [R]; field_simp

/-- **Bundle domination, Loewner form.** -/
theorem pair_dominated_loewner {ι : Type} (J : Finset ι) (hJ : J.Nonempty)
    (S : ι → Finset (Sym2 V)) (hdisj : (J : Set ι).PairwiseDisjoint S) {E' : Finset (Sym2 V)}
    (hSE : ∀ j ∈ J, S j ⊆ E') {s : ℝ} (hs : 0 < s) {w c : Sym2 V → ℝ}
    (hw : ∀ f ∈ E', 0 < w f) (hc : ∀ f ∈ E', 1 ≤ c f) {C α : ℝ} {u v : V}
    (he : s(u, v) ∈ E') (hcC : c s(u, v) ≤ C)
    (hpaths : ∀ j ∈ J, ∃ p : (pairGraph (S j)).Walk u v,
      p.IsTrail ∧ (p.edges.map fun f => 1 / w f).sum ≤ α / w s(u, v)) :
    ((C * α / J.card) • lap (fun f => s * c f * w f) E' -
      (s * c s(u, v) * w s(u, v)) • pairMat s(u, v)).PosSemidef := by
  have hH : ((C * α / J.card) • lap (fun f => s * c f * w f) E' -
      (s * c s(u, v) * w s(u, v)) • pairMat s(u, v)).IsHermitian := by
    refine Matrix.IsHermitian.sub ?_ ?_
    · ext i j
      have := congrFun (congrFun (lap_isHermitian (fun f => s * c f * w f) E') i) j
      simp only [Matrix.conjTranspose_apply, star_trivial, Matrix.smul_apply] at this ⊢
      rw [this]
    · ext i j
      simp only [Matrix.conjTranspose_apply, star_trivial, Matrix.smul_apply]
      rw [pairMat_symm]
  rw [posSemidef_iff_of_isHermitian hH]
  intro x
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.smul_mulVec,
    dotProduct_smul, dotProduct_smul, quad_lap, quad_pairMat, smul_eq_mul, smul_eq_mul,
    sub_nonneg]
  exact pair_dominated J hJ S hdisj hSE hs hw hc he hcC hpaths x

end Spectral
end CutQueryComplexity
