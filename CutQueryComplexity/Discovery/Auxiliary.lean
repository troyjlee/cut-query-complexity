import CutQueryComplexity.Graph.Integral

/-! # Keeping known edges and rounding only the residual (Lemma 31, hierarchy-free core)

Let `K ≤ G` be explicit, `R = G - K` with degrees `r_v`, and let a partition into parts
be given by a map `π : V → ι`. Following `eq:general-J-formula`, define
`Ψ(S) = c_K(S) + min_{Ŝ} (c_G(Ŝ) + vol_R(S ∆ Ŝ))` over unions `Ŝ` of parts (`psi`).

* `cut_le_cut_add_vol` and `cut_symmDiff_le` are the two inequalities `eq:cut-triangle`.
* `psi_lower`: `c_G(S) ≤ Ψ(S)`.
* `auxGraph` is the explicit graph `J`; `cut_auxGraph` computes its terminal-extension cuts
  and `psi_eq_auxGraph` shows that `Ψ(S)` is its minimum terminal-extension cut.
* `centerGraph R C` is `H_C^R`, the edges of `R` incident to `C`. `residual_rounding` is
  `eq:general-residual-rounding`: if every vertex outside `C` has `r_v ≤ t` or
  `w_R(v, C) ≥ r_v / k` (`eq:center-coverage`), and `Ŝ` agrees with `S` on `C` and satisfies
  `c_H(Ŝ) ≤ α c_H(S)` for `H = K + H_C^R`, then `vol_R(S ∆ Ŝ) ≤ k (1 + α) c_G(S) + N t`.
* `psi_upper`: under the same hypotheses, with `Ŝ` a union of parts,
  `Ψ(S) ≤ A c_G(S) + 2 N t` for `A = (1 + α)(2k + 1)` (`eq:general-J-bounds`).
-/

namespace CutQueryComplexity
namespace Discovery

open WeightedGraph Finset
open scoped symmDiff

variable {V : Type} [Fintype V] [DecidableEq V]

section Volume

/-- `vol_H(X) = ∑_{v ∈ X} d_H(v)`. -/
def vol (H : WeightedGraph V) (X : Finset V) : ℝ := ∑ v ∈ X, H.degree v

theorem vol_eq_left (H : WeightedGraph V) (X : Finset V) :
    vol H X = ∑ u, ∑ v, if u ∈ X then H.w u v else 0 := by
  have hX : X = univ.filter (· ∈ X) := by ext; simp
  simp only [vol, degree, Finset.sum_ite_irrel]
  conv_lhs => rw [hX]
  rw [Finset.sum_filter]
  simp

theorem vol_eq_right (H : WeightedGraph V) (X : Finset V) :
    vol H X = ∑ u, ∑ v, if v ∈ X then H.w u v else 0 := by
  rw [vol_eq_left, Finset.sum_comm]
  exact sum_congr rfl fun u _ => sum_congr rfl fun v _ => by rw [H.symm]

/-- Twice a cut counts each ordered pair separated by the shore. -/
theorem two_cut (H : WeightedGraph V) (S : Finset V) :
    2 * H.cut S = ∑ u, ∑ v, if (u ∈ S ∧ v ∉ S) ∨ (v ∈ S ∧ u ∉ S) then H.w u v else 0 := by
  have h2 : H.cut S = ∑ u, ∑ v, if v ∈ S ∧ u ∉ S then H.w u v else 0 := by
    rw [cut_eq_sum_ite, Finset.sum_comm]
    exact sum_congr rfl fun u _ => sum_congr rfl fun v _ => by rw [H.symm]
  rw [two_mul]
  nth_rewrite 1 [H.cut_eq_sum_ite S]
  rw [h2, ← sum_add_distrib]
  refine sum_congr rfl fun u _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun v _ => ?_
  by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp [hu, hv]

/-- `eq:cut-triangle`, second part: `c(S) ≤ c(T) + vol(S ∆ T)`. -/
theorem cut_le_cut_add_vol (H : WeightedGraph V) (S T : Finset V) :
    H.cut S ≤ H.cut T + vol H (S ∆ T) := by
  have h := two_cut H S
  have h' := two_cut H T
  have hl := vol_eq_left H (S ∆ T)
  have hr := vol_eq_right H (S ∆ T)
  have : ∑ u, ∑ v, (if (u ∈ S ∧ v ∉ S) ∨ (v ∈ S ∧ u ∉ S) then H.w u v else 0) ≤
      ∑ u, ∑ v, ((if (u ∈ T ∧ v ∉ T) ∨ (v ∈ T ∧ u ∉ T) then H.w u v else 0) +
        (if u ∈ S ∆ T then H.w u v else 0) + (if v ∈ S ∆ T then H.w u v else 0)) := by
    refine sum_le_sum fun u _ => sum_le_sum fun v _ => ?_
    have := H.nonneg u v
    simp only [mem_symmDiff]
    by_cases huS : u ∈ S <;> by_cases huT : u ∈ T <;> by_cases hvS : v ∈ S <;>
      by_cases hvT : v ∈ T <;> simp [huS, huT, hvS, hvT] <;> linarith
  simp only [sum_add_distrib] at this
  linarith

/-- `eq:cut-triangle`, first part: `c(S ∆ T) ≤ c(S) + c(T)`. -/
theorem cut_symmDiff_le (H : WeightedGraph V) (S T : Finset V) :
    H.cut (S ∆ T) ≤ H.cut S + H.cut T := by
  have h := two_cut H (S ∆ T)
  have hS := two_cut H S
  have hT := two_cut H T
  have : ∑ u, ∑ v, (if (u ∈ S ∆ T ∧ v ∉ S ∆ T) ∨ (v ∈ S ∆ T ∧ u ∉ S ∆ T) then H.w u v
      else 0) ≤
      ∑ u, ∑ v, ((if (u ∈ S ∧ v ∉ S) ∨ (v ∈ S ∧ u ∉ S) then H.w u v else 0) +
        (if (u ∈ T ∧ v ∉ T) ∨ (v ∈ T ∧ u ∉ T) then H.w u v else 0)) := by
    refine sum_le_sum fun u _ => sum_le_sum fun v _ => ?_
    have := H.nonneg u v
    simp only [mem_symmDiff]
    by_cases huS : u ∈ S <;> by_cases huT : u ∈ T <;> by_cases hvS : v ∈ S <;>
      by_cases hvT : v ∈ T <;> simp [huS, huT, hvS, hvT] <;> linarith
  simp only [sum_add_distrib] at this
  linarith

end Volume

section Psi

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `eq:general-J-formula`: `Ψ(S) = c_K(S) + min_{Ŝ} (c_G(Ŝ) + vol_R(S ∆ Ŝ))`, the minimum
over unions `Ŝ = π⁻¹(T)` of parts, with `R = G - K`. -/
noncomputable def psi (G K : WeightedGraph V) (π : V → ι) (S : Finset V) : ℝ :=
  K.cut S + Finset.inf' (univ : Finset (Finset ι)) univ_nonempty
    (fun T : Finset ι => (G.cut (pull π T) + vol (G.subtract K) (S ∆ pull π T) : ℝ))

theorem cut_subtract_le (G K : WeightedGraph V) (hKG : ∀ u v, K.w u v ≤ G.w u v)
    (S : Finset V) : (G.subtract K).cut S ≤ G.cut S := by
  rw [cut_subtract G K hKG]; linarith [K.cut_nonneg S]

/-- Lower bound of `eq:general-J-bounds`: `c_G(S) ≤ Ψ(S)`. -/
theorem psi_lower (G K : WeightedGraph V) (hKG : ∀ u v, K.w u v ≤ G.w u v) (π : V → ι)
    (S : Finset V) : G.cut S ≤ psi G K π S := by
  have hG : G.cut S = K.cut S + (G.subtract K).cut S := by
    rw [cut_subtract G K hKG]; ring
  rw [hG, psi]
  gcongr
  apply Finset.le_inf'
  intro T _
  have h1 := cut_le_cut_add_vol (G.subtract K) S (pull π T)
  have h2 := cut_subtract_le G K hKG (pull π T)
  linarith

theorem psi_le (G K : WeightedGraph V) (π : V → ι) (S : Finset V) (T : Finset ι) :
    psi G K π S ≤ K.cut S + (G.cut (pull π T) + vol (G.subtract K) (S ∆ pull π T)) := by
  unfold psi
  gcongr
  exact Finset.inf'_le _ (mem_univ T)

/-- The explicit auxiliary graph `J` on `V ⊕ ι`: `K` on the original vertices, the quotient
`G / π` on the part vertices `z_i`, and an edge `v z_{π v}` of weight `r_v`. -/
noncomputable def auxGraph (G K : WeightedGraph V) (π : V → ι) : WeightedGraph (V ⊕ ι) where
  w
    | .inl a, .inl b => K.w a b
    | .inr i, .inr j => (G.contract π).w i j
    | .inl a, .inr i => if π a = i then (G.subtract K).degree a else 0
    | .inr i, .inl a => if π a = i then (G.subtract K).degree a else 0
  symm x y := by
    rcases x with a | i <;> rcases y with b | j
    · exact K.symm a b
    · rfl
    · rfl
    · exact (G.contract π).symm i j
  nonneg x y := by
    have := fun a => Finset.sum_nonneg fun u (_ : u ∈ univ) => (G.subtract K).nonneg a u
    rcases x with a | i <;> rcases y with b | j
    · exact K.nonneg a b
    · dsimp only; split <;> simp [degree, this]
    · dsimp only; split <;> simp [degree, this]
    · exact (G.contract π).nonneg i j
  diag x := by
    rcases x with a | i
    · exact K.diag a
    · exact (G.contract π).diag i

omit [DecidableEq V] [Fintype ι] [DecidableEq ι] in
theorem sum_sum_type_sq {α β : Type} [Fintype α] [Fintype β] (f : α ⊕ β → α ⊕ β → ℝ) :
    ∑ x, ∑ y, f x y = (∑ a, ∑ b, f (.inl a) (.inl b)) + (∑ a, ∑ j, f (.inl a) (.inr j)) +
      (∑ i, ∑ b, f (.inr i) (.inl b)) + ∑ i, ∑ j, f (.inr i) (.inr j) := by
  simp only [Fintype.sum_sum_type, sum_add_distrib]; ring

/-- A terminal-extension cut of `J` is `c_K(S) + c_G(π⁻¹ T) + vol_R(S ∆ π⁻¹ T)`. -/
theorem cut_auxGraph (G K : WeightedGraph V) (π : V → ι) (S : Finset V) (T : Finset ι) :
    (auxGraph G K π).cut (S.disjSum T) =
      K.cut S + G.cut (pull π T) + vol (G.subtract K) (S ∆ pull π T) := by
  rw [cut_eq_sum_ite, sum_sum_type_sq]
  have hA : (∑ a, ∑ b, if Sum.inl a ∈ S.disjSum T ∧ Sum.inl b ∉ S.disjSum T then
      (auxGraph G K π).w (.inl a) (.inl b) else 0) = K.cut S := by
    rw [cut_eq_sum_ite]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by simp [auxGraph]
  have hD : (∑ i, ∑ j, if Sum.inr i ∈ S.disjSum T ∧ Sum.inr j ∉ S.disjSum T then
      (auxGraph G K π).w (.inr i) (.inr j) else 0) = G.cut (pull π T) := by
    rw [← cut_contract, cut_eq_sum_ite]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by simp [auxGraph]
  have hB : (∑ a, ∑ j, if Sum.inl a ∈ S.disjSum T ∧ Sum.inr j ∉ S.disjSum T then
      (auxGraph G K π).w (.inl a) (.inr j) else 0) =
      ∑ a, if a ∈ S ∧ π a ∉ T then (G.subtract K).degree a else 0 := by
    refine sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single (π a) (fun j _ hj => by simp [auxGraph, Ne.symm hj])
      (by simp)]
    simp [auxGraph]
  have hC : (∑ i, ∑ b, if Sum.inr i ∈ S.disjSum T ∧ Sum.inl b ∉ S.disjSum T then
      (auxGraph G K π).w (.inr i) (.inl b) else 0) =
      ∑ b, if π b ∈ T ∧ b ∉ S then (G.subtract K).degree b else 0 := by
    rw [Finset.sum_comm]
    refine sum_congr rfl fun b _ => ?_
    rw [Finset.sum_eq_single (π b) (fun j _ hj => by simp [auxGraph, Ne.symm hj])
      (by simp)]
    simp [auxGraph]
  have hvol : vol (G.subtract K) (S ∆ pull π T) = (∑ a, if a ∈ S ∧ π a ∉ T then (G.subtract K).degree a else 0) +
      ∑ b, if π b ∈ T ∧ b ∉ S then (G.subtract K).degree b else 0 := by
    rw [vol, ← sum_add_distrib, show S ∆ pull π T = univ.filter (· ∈ S ∆ pull π T) by
      ext; simp, Finset.sum_filter]
    refine sum_congr rfl fun x _ => ?_
    by_cases hS : x ∈ S <;> by_cases hT : π x ∈ T <;> simp [hS, hT, mem_symmDiff]
  rw [hA, hB, hC, hD, hvol]
  ring

/-- `eq:general-J-formula`: `Ψ(S)` is the minimum terminal-extension cut of `J`. -/
theorem psi_eq_auxGraph (G K : WeightedGraph V) (π : V → ι) (S : Finset V) :
    psi G K π S = Finset.inf' (univ : Finset (Finset ι)) univ_nonempty
      (fun T : Finset ι => (auxGraph G K π).cut (S.disjSum T)) := by
  apply le_antisymm
  · obtain ⟨T, -, hT⟩ := Finset.exists_mem_eq_inf' (univ_nonempty (α := Finset ι))
      (fun T : Finset ι => (auxGraph G K π).cut (S.disjSum T))
    rw [hT, cut_auxGraph, add_assoc]
    exact psi_le G K π S T
  · obtain ⟨T, -, hT⟩ := Finset.exists_mem_eq_inf' (univ_nonempty (α := Finset ι))
      (fun T : Finset ι => (G.cut (pull π T) + vol (G.subtract K) (S ∆ pull π T) : ℝ))
    calc _ ≤ (auxGraph G K π).cut (S.disjSum T) := Finset.inf'_le _ (mem_univ T)
      _ = psi G K π S := by rw [cut_auxGraph, psi, hT, add_assoc]

end Psi

section Rounding

/-- `H_C^R`: the edges of `R` incident to the center set `C`. -/
noncomputable def centerGraph (R : WeightedGraph V) (C : Finset V) : WeightedGraph V where
  w a b := if a ∈ C ∨ b ∈ C then R.w a b else 0
  symm a b := by
    by_cases ha : a ∈ C <;> by_cases hb : b ∈ C <;> simp [ha, hb, R.symm a b]
  nonneg a b := by split <;> simp [R.nonneg]
  diag a := by simp [R.diag]

omit [Fintype V] in
theorem centerGraph_le (R : WeightedGraph V) (C : Finset V) (a b : V) :
    (centerGraph R C).w a b ≤ R.w a b := by
  simp only [centerGraph]; split <;> simp [R.nonneg]

/-- Since `V \ C` is independent in `H_C^R`, a shore avoiding `C` has cut equal to its
`H_C^R`-volume, namely `∑_{v ∈ X} w_R(v, C)`. -/
theorem cut_centerGraph (R : WeightedGraph V) {C X : Finset V} (hX : Disjoint X C) :
    (centerGraph R C).cut X = ∑ v ∈ X, ∑ c ∈ C, R.w v c := by
  unfold cut
  refine sum_congr rfl fun v hv => ?_
  have hvC : v ∉ C := disjoint_left.mp hX hv
  have hCX : C ⊆ Xᶜ := fun c hc => mem_compl.mpr fun h => disjoint_left.mp hX h hc
  simp only [centerGraph, hvC, false_or]
  rw [← sum_filter, show Xᶜ.filter (· ∈ C) = C by
    ext c; simp only [mem_filter, mem_compl, and_iff_right_iff_imp]
    exact fun h => mem_compl.mp (hCX h)]

/-- `eq:general-residual-rounding`, first line: with center coverage, a set `X` disjoint
from `C` has `vol_R(X) ≤ k c_{H_C^R}(X) + |X| t`. -/
theorem vol_le_center_cut (R : WeightedGraph V) {C X : Finset V} (hX : Disjoint X C)
    {t : ℝ} (ht : 0 ≤ t) {k : ℕ} (hk : 0 < k)
    (hcov : ∀ v ∉ C, R.degree v ≤ t ∨ R.degree v / k ≤ ∑ c ∈ C, R.w v c) :
    vol R X ≤ k * (centerGraph R C).cut X + X.card * t := by
  rw [cut_centerGraph R hX, vol, mul_sum]
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have : ∀ v ∈ X, R.degree v ≤ k * ∑ c ∈ C, R.w v c + t := by
    intro v hv
    have h0 : 0 ≤ ∑ c ∈ C, R.w v c := sum_nonneg fun c _ => R.nonneg v c
    rcases hcov v (disjoint_left.mp hX hv) with h | h
    · nlinarith
    · rw [div_le_iff₀ hkR] at h; linarith
  calc ∑ v ∈ X, R.degree v ≤ ∑ v ∈ X, (k * ∑ c ∈ C, R.w v c + t) := sum_le_sum this
    _ = _ := by rw [sum_add_distrib, sum_const, nsmul_eq_mul]

/-- `eq:general-residual-rounding`. For `R = G - K`, `H = K + H_C^R`, center coverage,
and a shore `Ŝ` agreeing with `S` on `C` with `c_H(Ŝ) ≤ α c_H(S)`,
`vol_R(S ∆ Ŝ) ≤ k (1 + α) c_G(S) + N t`. -/
theorem residual_rounding (G K : WeightedGraph V) (hKG : ∀ u v, K.w u v ≤ G.w u v)
    {C S S' : Finset V} (hagree : S' ∩ C = S ∩ C) {t : ℝ} (ht : 0 ≤ t) {k : ℕ} (hk : 0 < k)
    (hcov : ∀ v ∉ C, (G.subtract K).degree v ≤ t ∨
      (G.subtract K).degree v / k ≤ ∑ c ∈ C, (G.subtract K).w v c)
    {α : ℝ} (hα : 0 ≤ α)
    (hround : (K.add (centerGraph (G.subtract K) C)).cut S' ≤
      α * (K.add (centerGraph (G.subtract K) C)).cut S) :
    vol (G.subtract K) (S ∆ S') ≤ k * (1 + α) * G.cut S + Fintype.card V * t := by
  set R := G.subtract K
  set HC := centerGraph R C
  have hX : Disjoint (S ∆ S') C := by
    rw [disjoint_left]
    intro v hv hvC
    have h1 : v ∈ S ↔ v ∈ S' := by
      have := congrArg (v ∈ ·) hagree
      simp only [mem_inter, hvC, and_true] at this
      exact Iff.of_eq this.symm
    rw [mem_symmDiff] at hv
    tauto
  have h1 := vol_le_center_cut R hX ht hk hcov
  have h2 := cut_symmDiff_le HC S S'
  have hHC : ∀ U, HC.cut U ≤ R.cut U := fun U =>
    sum_le_sum fun _ _ => sum_le_sum fun _ _ => centerGraph_le R C _ _
  have hG : ∀ U, G.cut U = K.cut U + R.cut U := fun U => by
    rw [cut_subtract G K hKG]; ring
  have h3 : (K.add HC).cut S ≤ G.cut S := by
    rw [cut_add, hG]; linarith [hHC S]
  have h4 : HC.cut S' ≤ α * G.cut S := by
    have := K.cut_nonneg S'
    simp only [cut_add] at hround h3
    nlinarith [mul_le_mul_of_nonneg_left h3 hα]
  have h5 : HC.cut S ≤ G.cut S := by
    linarith [hHC S, hG S, K.cut_nonneg S]
  have hcard : ((S ∆ S').card : ℝ) * t ≤ Fintype.card V * t :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_univ _) ht
  have hkR : (0 : ℝ) ≤ k := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h2 hkR]

/-- Upper bound of `eq:general-J-bounds`, given a rounded union of parts `Ŝ = π⁻¹(T)` that
agrees with `S` on `C` and has `c_H(Ŝ) ≤ α c_H(S)`, and center coverage:
`Ψ(S) ≤ (1 + α)(2k + 1) c_G(S) + 2 N t`. -/
theorem psi_upper {ι : Type} [Fintype ι] [DecidableEq ι] (G K : WeightedGraph V)
    (hKG : ∀ u v, K.w u v ≤ G.w u v) (π : V → ι) {C S : Finset V} {T : Finset ι}
    (hagree : pull π T ∩ C = S ∩ C) {t : ℝ} (ht : 0 ≤ t) {k : ℕ} (hk : 0 < k)
    (hcov : ∀ v ∉ C, (G.subtract K).degree v ≤ t ∨
      (G.subtract K).degree v / k ≤ ∑ c ∈ C, (G.subtract K).w v c)
    {α : ℝ} (hα : 0 ≤ α)
    (hround : (K.add (centerGraph (G.subtract K) C)).cut (pull π T) ≤
      α * (K.add (centerGraph (G.subtract K) C)).cut S) :
    psi G K π S ≤ (1 + α) * (2 * k + 1) * G.cut S + 2 * Fintype.card V * t := by
  set R := G.subtract K
  set S' := pull π T
  have hvol := residual_rounding G K hKG hagree ht hk hcov hα hround
  have h0 := psi_le G K π S T
  have hG : ∀ U, G.cut U = K.cut U + R.cut U := fun U => by
    rw [cut_subtract G K hKG]; ring
  -- `c_K(Ŝ) ≤ c_H(Ŝ) ≤ α c_H(S) ≤ α c_G(S)`.
  have hK : K.cut S' ≤ α * G.cut S := by
    have h1 : (centerGraph R C).cut S ≤ R.cut S :=
      sum_le_sum fun _ _ => sum_le_sum fun _ _ => centerGraph_le R C _ _
    have h2 := (centerGraph R C).cut_nonneg S'
    simp only [cut_add] at hround
    have h3 : K.cut S + (centerGraph R C).cut S ≤ G.cut S := by rw [hG]; linarith
    nlinarith [mul_le_mul_of_nonneg_left h3 hα]
  -- `c_R(Ŝ) ≤ c_R(S) + vol_R(S ∆ Ŝ)`.
  have hR : R.cut S' ≤ R.cut S + vol R (S ∆ S') := by
    have := cut_le_cut_add_vol R S' S
    rwa [symmDiff_comm] at this
  have hGS := G.cut_nonneg S
  have hkR : (0 : ℝ) ≤ k := by positivity
  rw [hG S'] at h0
  have := hG S
  nlinarith

end Rounding

end Discovery
end CutQueryComplexity
