import CutQueryComplexity.Certificate.Main
import CutQueryComplexity.Certificate.LowerBound
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Matrix.Notation

/-! # The `2n − 2` lower bound on `cert(G)`: the windmill graph

For `k ≥ 1` the windmill `W_k` consists of `k` copies of `K₄` with unit edge weights sharing
one hub vertex, so `n = 3k + 1`. Every minimum-cut certificate of `W_k` has at least
`6k = 2n − 2` shores (Lee, Li, Santha and Zhang, *On the cut dimension of a graph*, CCC 2021;
their proof goes through the `ℓ₁`-approximate cut dimension and LP duality). The proof here
is direct.

The answers of a certificate `Q` define a linear map `Φ : ℝ^E → ℝ^Q` on edge perturbations
`δ`, where `E` is the set of `6k` edges. If `Φ δ = 0` and `|δ| ≤ 1` entrywise, then the
graph with weights `1 + δ` is a nonnegative competitor consistent with `W_k` on `Q`, so every
proper shore has cut at least `λ(W_k) = 3` in it. Scaling `δ` to sup norm one and using both
`δ` and `-δ` gives, in each copy, that the four minimum cuts `{a}, {b}, {c}, {a, b, c}` see
`δ` as zero and that the three weight-`4` cuts `{a, b}, {a, c}, {b, c}` see it with absolute
value at most one. The first leaves two free parameters per copy and the second bounds every
entry by `1/2`, contradicting sup norm one. Hence `Φ` is injective and `|Q| ≥ 6k`.

* `windmill φ`: the windmill on a vertex type `V` identified with `Option (Fin k × Fin 3)`
  by `φ` (`none` is the hub).
* `mincutValue_windmill`: `λ(W_k) = 3` for `k ≥ 1`.
* `six_mul_le_certificateComplexity`: `6k ≤ cert(W_k)`.
* `two_mul_card_sub_two_le_certificateComplexity`: `2n − 2 ≤ cert(W_k)` with `n = |V|`.
* `exists_two_mul_sub_two_le_certificateComplexity`: a graph on `Fin (3k + 1)` with
  `cert(G) ≥ 2(3k + 1) − 2`.
* `two_mul_sub_two_le_budget`, `two_mul_sub_two_le_minCutValueComplexity`: hence every
  deterministic cut-query algorithm for the minimum-cut value on `3k + 1` vertices uses at
  least `2(3k + 1) − 2` queries; `two_mul_sub_three_le_shore_budget` is the shore-output
  form, one query weaker.
-/

namespace CutQueryComplexity
namespace Certificate
namespace Windmill

open Finset

noncomputable section

/-- The `7 × 6` table of the seven tracked cuts of `K₄` against its six edges
`ab, ac, av, bc, bv, cv` (`v` the hub): rows `0`–`3` are the shores `{a}, {b}, {c}, {a, b, c}`
of value `3`, rows `4`–`6` the shores `{a, b}, {a, c}, {b, c}` of value `4`. -/
def table : Matrix (Fin 7) (Fin 6) ℝ :=
  !![1, 1, 1, 0, 0, 0;
     1, 0, 0, 1, 1, 0;
     0, 1, 0, 1, 0, 1;
     0, 0, 1, 0, 1, 1;
     0, 1, 1, 1, 1, 0;
     1, 0, 1, 1, 0, 1;
     1, 1, 0, 0, 1, 1]

theorem rowsum (t : Fin 7) : ∑ e, table t e = if t.val < 4 then 3 else 4 := by
  fin_cases t <;> norm_num [table, Fin.sum_univ_six]

/-- Rows `0`–`3` vanishing leaves two free parameters per copy; rows `4`–`6` bounded by one
then bound every entry by `1/2`. -/
theorem abs_le_half (v : Fin 6 → ℝ)
    (h0 : ∑ e, table 0 e * v e = 0) (h1 : ∑ e, table 1 e * v e = 0)
    (h2 : ∑ e, table 2 e * v e = 0) (h3 : ∑ e, table 3 e * v e = 0)
    (h4 : |∑ e, table 4 e * v e| ≤ 1) (h5 : |∑ e, table 5 e * v e| ≤ 1)
    (h6 : |∑ e, table 6 e * v e| ≤ 1) (e : Fin 6) : |v e| ≤ 1 / 2 := by
  rw [abs_le] at h4 h5 h6 ⊢
  obtain ⟨h4a, h4b⟩ := h4
  obtain ⟨h5a, h5b⟩ := h5
  obtain ⟨h6a, h6b⟩ := h6
  norm_num [table, Fin.sum_univ_six] at h0 h1 h2 h3 h4a h4b h5a h5b h6a h6b
  fin_cases e <;> simp only [Fin.reduceFinMk] <;> constructor <;> linarith

/-- Vertices: the hub `none` and the three vertices `some (i, l)` of copy `i`. -/
abbrev Vtx (k : ℕ) := Option (Fin k × Fin 3)

theorem card_vtx (k : ℕ) : Fintype.card (Vtx k) = 3 * k + 1 := by
  simp [Fintype.card_option, Fintype.card_prod, mul_comm]

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- Endpoints of edge `e` of copy `i`, ordered `ab, ac, av, bc, bv, cv`. -/
def ends (φ : Vtx k ≃ V) (i : Fin k) : Fin 6 → V × V :=
  ![(φ (some (i, 0)), φ (some (i, 1))), (φ (some (i, 0)), φ (some (i, 2))),
    (φ (some (i, 0)), φ none), (φ (some (i, 1)), φ (some (i, 2))),
    (φ (some (i, 1)), φ none), (φ (some (i, 2)), φ none)]

omit [Fintype V] [DecidableEq V] in
theorem ends_ne (φ : Vtx k ≃ V) (i : Fin k) (e : Fin 6) :
    (ends φ i e).1 ≠ (ends φ i e).2 := by
  fin_cases e <;> simp [ends]

/-- Ordered indicator of the pair `p`. -/
def ind (p : V × V) (u v : V) : ℝ := (if u = p.1 then 1 else 0) * (if v = p.2 then 1 else 0)

omit [Fintype V] in
theorem ind_nonneg (p : V × V) (u v : V) : 0 ≤ ind p u v := by
  unfold ind; split_ifs <;> norm_num

omit [Fintype V] in
theorem ind_self {p : V × V} (hp : p.1 ≠ p.2) (v : V) : ind p v v = 0 := by
  unfold ind
  split_ifs with h1 h2
  · exact absurd (h1.symm.trans h2) hp
  all_goals simp

omit [Fintype V] in
theorem sum_ind (p : V × V) (A B : Finset V) :
    ∑ u ∈ A, ∑ v ∈ B, ind p u v = (if p.1 ∈ A then 1 else 0) * (if p.2 ∈ B then 1 else 0) := by
  simp only [ind]
  rw [← Finset.sum_mul_sum, Finset.sum_ite_eq', Finset.sum_ite_eq']

/-- The windmill with edge weights `c`: weight `c (i, e)` on edge `e` of copy `i`. -/
def graph (φ : Vtx k ≃ V) (c : Fin k × Fin 6 → ℝ) (hc : ∀ x, 0 ≤ c x) : WeightedGraph V where
  w u v := ∑ x, c x * (ind (ends φ x.1 x.2) u v + ind (ends φ x.1 x.2) v u)
  symm u v := Finset.sum_congr rfl fun x _ => by ring
  nonneg u v := Finset.sum_nonneg fun x _ =>
    mul_nonneg (hc x) (add_nonneg (ind_nonneg _ _ _) (ind_nonneg _ _ _))
  diag v := Finset.sum_eq_zero fun x _ => by rw [ind_self (ends_ne φ x.1 x.2)]; ring

/-- The windmill `W_k`: unit weights on the `6k` edges. -/
def windmill (φ : Vtx k ≃ V) : WeightedGraph V := graph φ (fun _ => 1) (fun _ => zero_le_one)

/-- Whether edge `x` crosses the shore `S`. -/
def chi (φ : Vtx k ≃ V) (S : Finset V) (x : Fin k × Fin 6) : ℝ :=
  (if (ends φ x.1 x.2).1 ∈ S then 1 else 0) * (if (ends φ x.1 x.2).2 ∈ Sᶜ then 1 else 0) +
  (if (ends φ x.1 x.2).2 ∈ S then 1 else 0) * (if (ends φ x.1 x.2).1 ∈ Sᶜ then 1 else 0)

theorem chi_nonneg (φ : Vtx k ≃ V) (S : Finset V) (x : Fin k × Fin 6) : 0 ≤ chi φ S x := by
  unfold chi; split_ifs <;> norm_num

/-- Cuts of the weighted windmill are sums of edge weights over crossing edges. -/
theorem cut_graph (φ : Vtx k ≃ V) (c : Fin k × Fin 6 → ℝ) (hc : ∀ x, 0 ≤ c x) (S : Finset V) :
    (graph φ c hc).cut S = ∑ x, c x * chi φ S x := by
  simp only [WeightedGraph.cut, graph]
  have hswap : ∀ u, ∑ v ∈ Sᶜ, ∑ x, c x * (ind (ends φ x.1 x.2) u v + ind (ends φ x.1 x.2) v u)
      = ∑ x, ∑ v ∈ Sᶜ, c x * (ind (ends φ x.1 x.2) u v + ind (ends φ x.1 x.2) v u) :=
    fun u => Finset.sum_comm
  simp_rw [hswap]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp_rw [← Finset.mul_sum]
  congr 1
  simp_rw [Finset.sum_add_distrib]
  rw [sum_ind, Finset.sum_comm, sum_ind, chi, mul_comm (if (ends φ x.1 x.2).1 ∈ Sᶜ then _ else _)]

/-- The seven tracked shores of copy `i`, in the order of the rows of `table`. -/
def shore (φ : Vtx k ≃ V) (i : Fin k) : Fin 7 → Finset V :=
  ![{φ (some (i, 0))}, {φ (some (i, 1))}, {φ (some (i, 2))},
    {φ (some (i, 0)), φ (some (i, 1)), φ (some (i, 2))},
    {φ (some (i, 0)), φ (some (i, 1))}, {φ (some (i, 0)), φ (some (i, 2))},
    {φ (some (i, 1)), φ (some (i, 2))}]

theorem shore_proper (φ : Vtx k ≃ V) (i : Fin k) (t : Fin 7) : ProperShore (shore φ i t) := by
  refine ⟨?_, fun h => ?_⟩
  · fin_cases t <;> simp [shore]
  · have hmem : φ none ∈ shore φ i t := h ▸ Finset.mem_univ _
    fin_cases t <;> simp [shore] at hmem

theorem chi_shore (φ : Vtx k ≃ V) (i j : Fin k) (t : Fin 7) (e : Fin 6) :
    chi φ (shore φ i t) (j, e) = if j = i then table t e else 0 := by
  rcases eq_or_ne j i with rfl | hji
  · fin_cases t <;> fin_cases e <;> simp [chi, shore, ends, table]
  · fin_cases t <;> fin_cases e <;> simp [chi, shore, ends, hji]

theorem sum_chi_shore (φ : Vtx k ≃ V) (i : Fin k) (t : Fin 7) :
    ∑ x, chi φ (shore φ i t) x = ∑ e, table t e := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
  · simp [chi_shore]
  · intro j _ hji; simp [chi_shore, hji]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem sum_mul_chi_shore (φ : Vtx k ≃ V) (i : Fin k) (t : Fin 7) (δ : Fin k × Fin 6 → ℝ) :
    ∑ x, δ x * chi φ (shore φ i t) x = ∑ e, table t e * δ (i, e) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
  · simp [chi_shore, mul_comm]
  · intro j _ hji; simp [chi_shore, hji]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- A copy split by `S` contributes at least `3` crossing edges. -/
theorem three_le_copy_sum (φ : Vtx k ≃ V) (S : Finset V) (i : Fin k) (l : Fin 3)
    (h : (φ none ∈ S ∧ φ (some (i, l)) ∉ S) ∨ (φ none ∉ S ∧ φ (some (i, l)) ∈ S)) :
    3 ≤ ∑ e, chi φ S (i, e) := by
  by_cases hH : φ none ∈ S <;> by_cases hA : φ (some (i, 0)) ∈ S <;>
    by_cases hB : φ (some (i, 1)) ∈ S <;> by_cases hC : φ (some (i, 2)) ∈ S <;>
    first
    | (norm_num [Fin.sum_univ_six, chi, ends, hH, hA, hB, hC]; done)
    | (exfalso; fin_cases l <;> simp_all)

/-- Every proper shore of the windmill has cut at least `3`. -/
theorem three_le_cut (φ : Vtx k ≃ V) (S : Finset V) (hS : ProperShore S) :
    3 ≤ (windmill φ).cut S := by
  obtain ⟨i, l, hil⟩ : ∃ i l,
      (φ none ∈ S ∧ φ (some (i, l)) ∉ S) ∨ (φ none ∉ S ∧ φ (some (i, l)) ∈ S) := by
    by_cases hH : φ none ∈ S
    · obtain ⟨v, hv⟩ : ∃ v, v ∉ S := by
        by_contra h
        exact hS.2 (Finset.eq_univ_iff_forall.mpr fun v => by_contra fun hv => h ⟨v, hv⟩)
      obtain ⟨w, rfl⟩ := φ.surjective v
      rcases w with _ | ⟨i, l⟩
      · exact absurd hH hv
      · exact ⟨i, l, Or.inl ⟨hH, hv⟩⟩
    · obtain ⟨v, hv⟩ := hS.1
      obtain ⟨w, rfl⟩ := φ.surjective v
      rcases w with _ | ⟨i, l⟩
      · exact absurd hv hH
      · exact ⟨i, l, Or.inr ⟨hH, hv⟩⟩
  calc (3 : ℝ) ≤ ∑ e, chi φ S (i, e) := three_le_copy_sum φ S i l hil
    _ ≤ ∑ j, ∑ e, chi φ S (j, e) :=
        Finset.single_le_sum (f := fun j => ∑ e, chi φ S (j, e))
          (fun j _ => Finset.sum_nonneg fun e _ => chi_nonneg φ S (j, e)) (Finset.mem_univ i)
    _ = (windmill φ).cut S := by
        rw [windmill, cut_graph, Fintype.sum_prod_type]; simp

theorem cut_windmill_shore (φ : Vtx k ≃ V) (i : Fin k) (t : Fin 7) :
    (windmill φ).cut (shore φ i t) = if t.val < 4 then 3 else 4 := by
  rw [windmill, cut_graph, ← rowsum, ← sum_chi_shore φ i t]; simp

/-- `λ(W_k) = 3` for `k ≥ 1`. -/
theorem mincutValue_windmill (φ : Vtx k ≃ V) (hk : 0 < k) : mincutValue (windmill φ) = 3 := by
  have hne : (properShores V).Nonempty :=
    ⟨_, (mem_properShores _).mpr (shore_proper φ ⟨0, hk⟩ 0)⟩
  obtain ⟨S, hS, hval⟩ := exists_isMinCut (windmill φ) hne
  refine le_antisymm ?_ ?_
  · calc mincutValue (windmill φ) ≤ (windmill φ).cut (shore φ ⟨0, hk⟩ 0) :=
          mincutValue_le _ (shore_proper _ _ _)
      _ = 3 := by rw [cut_windmill_shore]; simp
  · rw [← hval]; exact three_le_cut φ S hS.1

theorem one_add_nonneg {δ : Fin k × Fin 6 → ℝ} (h : ∀ x, |δ x| ≤ 1) (x : Fin k × Fin 6) :
    0 ≤ 1 + δ x := by
  have := (abs_le.mp (h x)).1; linarith

/-- A certificate forces the row inequalities on every perturbation of sup norm at most one
whose query answers vanish. -/
theorem row_bounds (φ : Vtx k ≃ V) {Q : Finset (Finset V)}
    (hQ : IsMinCutCertificate (windmill φ) Q) (hlam : mincutValue (windmill φ) = 3)
    (δ : Fin k × Fin 6 → ℝ) (hδ : ∀ x, |δ x| ≤ 1) (hker : ∀ S ∈ Q, ∑ x, δ x * chi φ S x = 0)
    (i : Fin k) (t : Fin 7) :
    3 ≤ (if t.val < 4 then 3 else 4) + ∑ e, table t e * δ (i, e) := by
  set G' := graph φ (fun x => 1 + δ x) (one_add_nonneg hδ) with hG'
  have hcons : Consistent (windmill φ) G' Q := by
    intro S hS
    rw [hG', windmill, cut_graph, cut_graph]
    simp only [add_mul, one_mul, Finset.sum_add_distrib, hker S hS, add_zero]
  have hle := mincutValue_le G' (shore_proper φ i t)
  rw [hQ G' hcons, hlam, hG', cut_graph] at hle
  simpa only [add_mul, one_mul, Finset.sum_add_distrib, sum_chi_shore, sum_mul_chi_shore,
    rowsum] using hle

/-- The core of the lower bound: on a certificate `Q`, a perturbation whose query answers all
vanish is zero. -/
theorem eq_zero_of_forall_sum_eq_zero (φ : Vtx k ≃ V) (hk : 0 < k) {Q : Finset (Finset V)}
    (hQ : IsMinCutCertificate (windmill φ) Q) (δ : Fin k × Fin 6 → ℝ)
    (hker : ∀ S ∈ Q, ∑ x, δ x * chi φ S x = 0) : δ = 0 := by
  have hlam := mincutValue_windmill φ hk
  by_contra hne
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨⟨i₀, e₀⟩, -, hmax⟩ :=
    Finset.exists_max_image Finset.univ (fun x => |δ x|) Finset.univ_nonempty
  have hM : 0 < |δ (i₀, e₀)| := by
    by_contra h0
    have h0 : |δ (i₀, e₀)| ≤ 0 := not_lt.mp h0
    apply hne
    funext x
    exact abs_eq_zero.mp (le_antisymm ((hmax x (Finset.mem_univ x)).trans h0) (abs_nonneg _))
  set M := |δ (i₀, e₀)| with hMdef
  set δ' : Fin k × Fin 6 → ℝ := fun x => δ x / M with hδ'def
  have hδ' : ∀ x, |δ' x| ≤ 1 := fun x => by
    simp only [hδ'def, abs_div, hMdef, abs_abs]
    rw [div_le_one hM]
    exact hmax x (Finset.mem_univ x)
  have hδ'₀ : |δ' (i₀, e₀)| = 1 := by
    simp only [hδ'def, abs_div, hMdef, abs_abs]
    exact div_self hM.ne'
  have hker' : ∀ S ∈ Q, ∑ x, δ' x * chi φ S x = 0 := fun S hS => by
    have hx : ∀ x, δ' x * chi φ S x = δ x * chi φ S x * M⁻¹ := fun x => by
      simp only [hδ'def]; ring
    simp only [hx, ← Finset.sum_mul, hker S hS, zero_mul]
  have hkerneg : ∀ S ∈ Q, ∑ x, (-δ') x * chi φ S x = 0 := fun S hS => by
    simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, hker' S hS, neg_zero]
  have hδ'neg : ∀ x, |(-δ') x| ≤ 1 := fun x => by simp only [Pi.neg_apply, abs_neg]; exact hδ' x
  have hp := row_bounds φ hQ hlam δ' hδ' hker' i₀
  have hm := row_bounds φ hQ hlam (-δ') hδ'neg hkerneg i₀
  simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib] at hm
  have h0 := hp 0; have h0' := hm 0
  have h1 := hp 1; have h1' := hm 1
  have h2 := hp 2; have h2' := hm 2
  have h3 := hp 3; have h3' := hm 3
  have h4 := hp 4; have h4' := hm 4
  have h5 := hp 5; have h5' := hm 5
  have h6 := hp 6; have h6' := hm 6
  norm_num at h0 h0' h1 h1' h2 h2' h3 h3' h4 h4' h5 h5' h6 h6'
  have key := abs_le_half (fun e => δ' (i₀, e)) (by linarith) (by linarith) (by linarith)
    (by linarith) (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_le.mpr ⟨by linarith, by linarith⟩)
    (abs_le.mpr ⟨by linarith, by linarith⟩) e₀
  linarith

/-- Every certificate of `W_k` has at least `6k` shores. -/
theorem six_mul_le_card (φ : Vtx k ≃ V) {Q : Finset (Finset V)}
    (hQ : IsMinCutCertificate (windmill φ) Q) : 6 * k ≤ Q.card := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  let M : Matrix Q (Fin k × Fin 6) ℝ := Matrix.of fun S x => chi φ S.1 x
  have hinj : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro δ hδ
    apply eq_zero_of_forall_sum_eq_zero φ hk hQ δ
    intro S hS
    have := congrFun hδ ⟨S, hS⟩
    simpa [M, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, mul_comm] using this
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin, Fintype.card_coe] at this
  omega

/-- **The `2n − 2` lower bound**, as `6k ≤ cert(W_k)` on `n = 3k + 1` vertices. -/
theorem six_mul_le_certificateComplexity (φ : Vtx k ≃ V) :
    6 * k ≤ certificateComplexity (windmill φ) := by
  obtain ⟨Q, hQ, hcard⟩ := exists_certificate_card_eq (windmill φ)
  rw [← hcard]
  exact six_mul_le_card φ hQ

/-- **The `2n − 2` lower bound** with `n = |V|`. -/
theorem two_mul_card_sub_two_le_certificateComplexity (φ : Vtx k ≃ V) :
    2 * Fintype.card V - 2 ≤ certificateComplexity (windmill φ) := by
  rw [← Fintype.card_congr φ, card_vtx]
  have := six_mul_le_certificateComplexity φ
  omega

/-- For every `k` there is a graph on `n = 3k + 1` vertices with `cert(G) ≥ 2n − 2`. -/
theorem exists_two_mul_sub_two_le_certificateComplexity (k : ℕ) :
    ∃ G : WeightedGraph (Fin (3 * k + 1)),
      2 * (3 * k + 1) - 2 ≤ certificateComplexity G :=
  ⟨windmill (Fintype.equivFinOfCardEq (card_vtx k)), by
    have := two_mul_card_sub_two_le_certificateComplexity (Fintype.equivFinOfCardEq (card_vtx k))
    simpa using this⟩

/-- **Deterministic cut-query lower bound, value form.** Every deterministic decision tree that
outputs the minimum-cut value of every nonnegative weighted graph on `3k + 1` vertices has
budget at least `2(3k + 1) − 2`. -/
theorem two_mul_sub_two_le_budget (k : ℕ) {q : ℕ} {T : DTree (Finset (Fin (3 * k + 1))) ℝ ℝ q}
    (hT : T.Solves minCutValueRead MinCutValueGood) : 2 * (3 * k + 1) - 2 ≤ q := by
  obtain ⟨G, hG⟩ := exists_two_mul_sub_two_le_certificateComplexity k
  exact hG.trans (certificateComplexity_le_budget hT G)

/-- The deterministic cut-query complexity of the minimum-cut value on `3k + 1` vertices is at
least `2(3k + 1) − 2`. -/
theorem two_mul_sub_two_le_minCutValueComplexity (k : ℕ) :
    ((2 * (3 * k + 1) - 2 : ℕ) : WithTop ℕ) ≤ minCutValueComplexity (Fin (3 * k + 1)) := by
  obtain ⟨G, hG⟩ := exists_two_mul_sub_two_le_certificateComplexity k
  exact (WithTop.coe_le_coe.mpr hG).trans (certificateComplexity_le_minCutValueComplexity G)

/-- **Shore form.** A deterministic decision tree returning a minimum cut of every nonnegative
weighted graph on `3k + 1` vertices (the output convention of the `deterministic_mincut_*`
theorems) has budget at least `2(3k + 1) − 3`. -/
theorem two_mul_sub_three_le_shore_budget (k : ℕ) {q : ℕ}
    {T : DTree (Finset (Fin (3 * k + 1))) ℝ (Option (Finset (Fin (3 * k + 1)))) q}
    (hT : ∀ G : WeightedGraph (Fin (3 * k + 1)), ∃ S, T.eval G.cut = some S ∧ IsMinCut G S) :
    2 * (3 * k + 1) - 3 ≤ q := by
  obtain ⟨G, hG⟩ := exists_two_mul_sub_two_le_certificateComplexity k
  have := hG.trans (certificateComplexity_le_shore_budget hT G)
  omega

end

end Windmill
end Certificate
end CutQueryComplexity
