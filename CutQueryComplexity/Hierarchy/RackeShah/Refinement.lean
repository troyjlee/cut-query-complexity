import CutQueryComplexity.Hierarchy.RackeShah.Transport
import CutQueryComplexity.Hierarchy.RackeShah.LogBounds

/-! # Weighted refinement and its flow certificate (Räcke–Shah, M4b)

`Ref G n p X Cs` records the binary refinement history of a piece `X` in the parent context
`p`: either `X` is final, or `X = W ⊔ (X ∖ W)` with a split certificate for `W` (M2) and
refinements of both sides, with final parts `Cs`.

`ref_flow` (source Lemma 5, weighted): if `X` is at index `j` (`2^j |X| ≤ p`, `p ≤ 2n`) then
there are a load graph `q` supported in `X`, a flow `F` feasible in `q` and a receiving
function `r` with `div F = d_Cs − r` and `0 ≤ r ≤ B_j b_X` on `X`, where `B_j = Bprod n j`.
Across a split `X = W ⊔ Y` at index `j`, the receiving excess of each side beyond `B` times
its boundary in `X` is the mass on the split edges; the `W` side routes its excess inside
`G[W]` by the split certificate (bounded transportation), and the `Y` side first sends its
excess across the split edges proportionally to their capacities, then routes it inside
`G[W]` the same way. The received amounts in `W` are then at most
`(B_{j+1} + ρ (B_{j+1} + B_j)) b_X ≤ B_j b_X` by `Bprod_step_ineq`.

The load graph is `q_W + q_Y + 4 G[W] + 2 G[W, Y]`, so an edge inside a final part `D` is
loaded at most `4 (log₂ |X| − log₂ |D|)` times its capacity (one unit of `4` per smaller-side
transition), and an edge separated by the refinement at most `4 log₂ |X| + 2` times.
-/

namespace CutQueryComplexity
namespace Hierarchy
namespace RackeShah

open WeightedGraph Finset Certificate

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## Logarithms of sizes -/

/-- `log₂` of a natural number. -/
noncomputable def lg (m : ℕ) : ℝ := Real.logb 2 m

theorem lg_nonneg {m : ℕ} (hm : 1 ≤ m) : 0 ≤ lg m :=
  Real.logb_nonneg one_lt_two (by exact_mod_cast hm)

theorem lg_mono {m k : ℕ} (hm : 1 ≤ m) (hmk : m ≤ k) : lg m ≤ lg k :=
  (Real.logb_le_logb one_lt_two (by exact_mod_cast hm) (by exact_mod_cast (hm.trans hmk))).mpr
    (by exact_mod_cast hmk)

theorem lg_half {m k : ℕ} (hm : 1 ≤ m) (h : 2 * m ≤ k) : lg m + 1 ≤ lg k := by
  have h2 : lg (2 * m) = lg m + 1 := by
    unfold lg
    rw [Nat.cast_mul, Nat.cast_ofNat,
      Real.logb_mul (by norm_num) (by exact_mod_cast (by omega : m ≠ 0)),
      Real.logb_self_eq_one one_lt_two, add_comm]
  rw [← h2]
  exact lg_mono (by omega) h

/-! ## The split-edge graph -/

/-- The edges between `W` and `Y`. -/
def splitGraph (G : WeightedGraph V) (W Y : Finset V) : WeightedGraph V where
  w u v := if (u ∈ W ∧ v ∈ Y) ∨ (u ∈ Y ∧ v ∈ W) then G.w u v else 0
  symm u v := by
    by_cases h : (u ∈ W ∧ v ∈ Y) ∨ (u ∈ Y ∧ v ∈ W)
    · have h' : (v ∈ W ∧ u ∈ Y) ∨ (v ∈ Y ∧ u ∈ W) := by tauto
      simp only [h, h', ite_true, G.symm]
    · have h' : ¬ ((v ∈ W ∧ u ∈ Y) ∨ (v ∈ Y ∧ u ∈ W)) := by tauto
      simp only [h, h', ite_false]
  nonneg u v := by split <;> simp [G.nonneg]
  diag v := by split <;> simp [G.diag]

omit [Fintype V] in
theorem splitGraph_w (G : WeightedGraph V) (W Y : Finset V) (u v : V) :
    (splitGraph G W Y).w u v = if (u ∈ W ∧ v ∈ Y) ∨ (u ∈ Y ∧ v ∈ W) then G.w u v else 0 := rfl

omit [Fintype V] in
theorem splitGraph_supported (G : WeightedGraph V) {W Y X : Finset V} (hW : W ⊆ X) (hY : Y ⊆ X) :
    Supported (splitGraph G W Y) X := by
  intro u v huv
  rw [splitGraph_w, ite_eq_right]
  rintro (⟨hu, hv⟩ | ⟨hu, hv⟩)
  · rcases huv with h | h
    · exact h (hW hu)
    · exact h (hY hv)
  · rcases huv with h | h
    · exact h (hY hu)
    · exact h (hW hv)

/-! ## Refinement trees -/

/-- The refinement history of a piece `X` in parent context `p`, with final parts `Cs`. -/
inductive Ref (G : WeightedGraph V) (n p : ℕ) : Finset V → Finset (Finset V) → Prop
  | final (X : Finset V) (hX : X.Nonempty) : Ref G n p X {X}
  | split (X W : Finset V) (ρ : ℝ) (CsW CsY : Finset (Finset V))
      (hcert : SplitCert G (expFactor n p X.card) X W ρ)
      (hW : Ref G n p W CsW) (hY : Ref G n p (X \ W) CsY) :
      Ref G n p X (CsW ∪ CsY)

theorem Ref.isPart {G : WeightedGraph V} {n p : ℕ} {X : Finset V} {Cs : Finset (Finset V)}
    (h : Ref G n p X Cs) : IsPart X Cs := by
  induction h with
  | final X hX => exact IsPart.single hX
  | split X W ρ CsW CsY hcert hW hY ihW ihY =>
      have hWX := hcert.subset
      have hdisj : Disjoint W (X \ W) := disjoint_sdiff
      refine ⟨?_, ?_, ?_⟩
      · intro C hC
        rcases mem_union.mp hC with hC | hC
        · exact ihW.nonempty C hC
        · exact ihY.nonempty C hC
      · intro C hC D hD hne
        rw [Function.onFun]
        rcases mem_union.mp hC with hC | hC <;> rcases mem_union.mp hD with hD | hD
        · exact ihW.disj hC hD hne
        · exact hdisj.mono (ihW.subset hC) (ihY.subset hD)
        · exact hdisj.symm.mono (ihY.subset hC) (ihW.subset hD)
        · exact ihY.disj hC hD hne
      · rw [union_biUnion, ihW.union, ihY.union, union_sdiff_of_subset hWX]

theorem Ref.nonempty {G : WeightedGraph V} {n p : ℕ} {X : Finset V} {Cs : Finset (Finset V)}
    (h : Ref G n p X Cs) : X.Nonempty := by
  induction h with
  | final X hX => exact hX
  | split X W ρ CsW CsY hcert hW hY ihW ihY => exact hcert.nonempty.mono hcert.subset

/-! ## Routing an excess supply inside the smaller side -/

/-- The receiving bound inside `W`. -/
noncomputable def sinkBound (G : WeightedGraph V) (X W : Finset V) (c : ℝ) (v : V) : ℝ :=
  if v ∈ W then c * bd G X v else 0

/-- A supply on `W` dominated by `B` times the split-edge capacities routes inside `B G[W]`
to receiving amounts at most `B ρ b_X`. -/
theorem exists_route (G : WeightedGraph V) {X W : Finset V} (hWX : W ⊆ X) {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (hcut : ∀ Z ⊆ W, G.cross Z (X \ W) ≤ G.cross Z (W \ Z) + ρ * ∑ v ∈ Z, bd G X v)
    {B : ℝ} (hB : 0 ≤ B) (s : V → ℝ) (hs0 : ∀ v, 0 ≤ s v)
    (hs : ∀ v ∈ W, s v ≤ B * G.cross {v} (X \ W)) (hsW : ∀ v, v ∉ W → s v = 0) :
    ∃ (F : V → V → ℝ) (r : V → ℝ), Feasible ((G.induce W).scale B hB) F ∧
      (∀ v, netOut F v = s v - r v) ∧
      ∀ v, 0 ≤ r v ∧ r v ≤ sinkBound G X W (B * ρ) v := by
  refine exists_transport _ s (sinkBound G X W (B * ρ)) hs0 ?_ ?_
  · intro v; unfold sinkBound; split <;> [exact mul_nonneg (mul_nonneg hB hρ) (bd_nonneg G X v); exact le_rfl]
  · intro U
    have h1 : ∑ v ∈ U, s v = ∑ v ∈ U ∩ W, s v := by
      rw [← sum_filter_add_sum_filter_not U (fun v => v ∈ W), filter_mem_eq_inter,
        sum_eq_zero (s := U.filter fun v => v ∉ W) fun v hv => hsW v (mem_filter.mp hv).2,
        _root_.add_zero]
    have h2 : ∑ v ∈ U ∩ W, s v ≤ B * G.cross (U ∩ W) (X \ W) := by
      rw [cross_eq_sum_singleton, mul_sum]
      exact sum_le_sum fun v hv => hs v (mem_inter.mp hv).2
    have h3 := hcut (U ∩ W) inter_subset_right
    have h4 : W \ (U ∩ W) = W \ U := by
      ext v; simp only [mem_sdiff, mem_inter, not_and]; tauto
    have h5 : ∑ v ∈ U, sinkBound G X W (B * ρ) v = B * ρ * ∑ v ∈ U ∩ W, bd G X v := by
      unfold sinkBound
      rw [← sum_filter, filter_mem_eq_inter, mul_sum]
    rw [h4] at h3
    rw [cut_scale, induce_cut_eq_cross, h1, h5]
    calc ∑ v ∈ U ∩ W, s v ≤ B * G.cross (U ∩ W) (X \ W) := h2
      _ ≤ B * (G.cross (U ∩ W) (W \ U) + ρ * ∑ v ∈ U ∩ W, bd G X v) :=
          mul_le_mul_of_nonneg_left h3 hB
      _ = _ := by ring

/-! ## The flow certificate -/

/-- The refinement flow certificate of `X` with final parts `Cs` and receiving factor `B`. -/
def RefFlow (G : WeightedGraph V) (X : Finset V) (Cs : Finset (Finset V)) (B : ℝ) : Prop :=
  ∃ (q : WeightedGraph V) (F : V → V → ℝ) (r : V → ℝ),
    Supported q X ∧ Feasible q F ∧
    (∀ v ∈ X, netOut F v = pd G Cs v - r v) ∧
    (∀ v ∈ X, 0 ≤ r v ∧ r v ≤ B * bd G X v) ∧
    (∀ u v D, D ∈ Cs → u ∈ D → v ∈ D → q.w u v ≤ 4 * (lg X.card - lg D.card) * G.w u v) ∧
    (∀ u v, u ∈ X → v ∈ X → (∀ D ∈ Cs, ¬ (u ∈ D ∧ v ∈ D)) →
      q.w u v ≤ (4 * lg X.card + 2) * G.w u v)

theorem refFlow_final (G : WeightedGraph V) (X : Finset V) {B : ℝ}
    (hB : 1 ≤ B) : RefFlow G X {X} B := by
  refine ⟨0, fun _ _ => 0, fun v => bd G X v, Supported.zero X, ⟨fun _ _ => by simp,
    fun u v => by simp⟩, ?_, ?_, ?_, ?_⟩
  · intro v _; simp [netOut, pd]
  · intro v _
    exact ⟨bd_nonneg G X v, le_mul_of_one_le_left (bd_nonneg G X v) hB⟩
  · intro u v D hD _ _
    rw [mem_singleton.mp hD]
    simp
  · intro u v hu hv h
    exact absurd ⟨hu, hv⟩ (h X (mem_singleton_self X))

/-- The excess of a receiving function beyond `B` times a boundary. -/
noncomputable def excess (r : V → ℝ) (B : ℝ) (G : WeightedGraph V) (X W : Finset V) (v : V) : ℝ :=
  if v ∈ W then max 0 (r v - B * bd G X v) else 0

theorem excess_nonneg (r : V → ℝ) (B : ℝ) (G : WeightedGraph V) (X W : Finset V) (v : V) :
    0 ≤ excess r B G X W v := by
  unfold excess; split <;> simp

theorem excess_of_notMem (r : V → ℝ) (B : ℝ) (G : WeightedGraph V) (X W : Finset V) {v : V}
    (hv : v ∉ W) : excess r B G X W v = 0 := by
  simp [excess, hv]

theorem sub_excess_nonneg {r : V → ℝ} {B : ℝ} {G : WeightedGraph V} {X W : Finset V} {v : V}
    (hv : v ∈ W) (hr : 0 ≤ r v) (hB : 0 ≤ B) : 0 ≤ r v - excess r B G X W v := by
  simp only [excess, hv, ite_true]
  have := bd_nonneg G X v
  rcases le_total 0 (r v - B * bd G X v) with h | h
  · rw [max_eq_right h]; nlinarith
  · rw [max_eq_left h, sub_zero]; exact hr

theorem sub_excess_le {r : V → ℝ} {B : ℝ} {G : WeightedGraph V} {X W : Finset V} {v : V}
    (hv : v ∈ W) : r v - excess r B G X W v ≤ B * bd G X v := by
  simp only [excess, hv, ite_true]
  rcases le_total 0 (r v - B * bd G X v) with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; linarith

/-- The excess is at most `B` times the split-edge capacity. -/
theorem excess_le {r : V → ℝ} {B : ℝ} (hB : 0 ≤ B) {G : WeightedGraph V} {X W : Finset V}
    (hWX : W ⊆ X) {v : V} (hv : v ∈ W) (hr : r v ≤ B * bd G W v) :
    excess r B G X W v ≤ B * G.cross {v} (X \ W) := by
  simp only [excess, hv, ite_true]
  rw [bd_split G hWX hv, mul_add] at hr
  rcases le_total 0 (r v - B * bd G X v) with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]
    exact mul_nonneg hB (G.cross_nonneg _ _)

omit [Fintype V] [DecidableEq V] in
/-- The weight from `v` into `T`, as a sum over `T`. -/
theorem cross_eq_sum_singleton' (G : WeightedGraph V) (v : V) (T : Finset V) :
    G.cross {v} T = ∑ u ∈ T, G.w v u := by
  simp [cross]

/-! ## The sum of two partition families -/

theorem pd_union_of_disjoint (G : WeightedGraph V) {Ps Qs : Finset (Finset V)}
    (h : Disjoint Ps Qs) (v : V) : pd G (Ps ∪ Qs) v = pd G Ps v + pd G Qs v := by
  unfold pd; rw [sum_union h]

omit [Fintype V] in
theorem disjoint_parts_of_disjoint {W Y : Finset V} (hWY : Disjoint W Y)
    {CsW CsY : Finset (Finset V)} (hW : IsPart W CsW) (hY : IsPart Y CsY) :
    Disjoint CsW CsY := by
  rw [disjoint_left]
  intro D hDW hDY
  obtain ⟨v, hv⟩ := hW.nonempty D hDW
  exact disjoint_left.mp hWY (hW.subset hDW hv) (hY.subset hDY hv)

/-! ## The crossing flow of the larger side -/

/-- One term of the crossing flow: the `Y`-excess of `u` spread over its split edges. -/
noncomputable def crossTerm (G : WeightedGraph V) (W Y : Finset V) (sY : V → ℝ) (u v : V) : ℝ :=
  if u ∈ Y ∧ v ∈ W then sY u * G.w u v / G.cross {u} W else 0

theorem crossTerm_nonneg (G : WeightedGraph V) (W Y : Finset V) {sY : V → ℝ}
    (hs : ∀ v, 0 ≤ sY v) (u v : V) : 0 ≤ crossTerm G W Y sY u v := by
  unfold crossTerm
  split
  · exact div_nonneg (mul_nonneg (hs u) (G.nonneg u v)) (G.cross_nonneg _ _)
  · exact le_rfl

theorem crossTerm_le (G : WeightedGraph V) (W Y : Finset V) {sY : V → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hs : ∀ u ∈ Y, sY u ≤ B * G.cross {u} W) (u v : V) :
    crossTerm G W Y sY u v ≤ B * G.w u v := by
  unfold crossTerm
  split_ifs with h
  · obtain ⟨hu, hv⟩ := h
    rcases (G.cross_nonneg {u} W).lt_or_eq with hc | hc
    · rw [div_le_iff₀ hc]
      have := hs u hu
      have := G.nonneg u v
      nlinarith
    · rw [← hc, div_zero]
      exact mul_nonneg hB (G.nonneg u v)
  · exact mul_nonneg hB (G.nonneg u v)

/-- Row sums of the crossing terms: exactly the excess on `Y`. -/
theorem sum_crossTerm_row (G : WeightedGraph V) (W Y : Finset V) {sY : V → ℝ} {B : ℝ}
    (hs0 : ∀ v, 0 ≤ sY v) (hs : ∀ u ∈ Y, sY u ≤ B * G.cross {u} W) {u : V} (hu : u ∈ Y) :
    ∑ v, crossTerm G W Y sY u v = sY u := by
  unfold crossTerm
  simp only [hu, true_and]
  rw [← sum_filter, filter_mem_eq_inter, univ_inter]
  rcases (G.cross_nonneg {u} W).lt_or_eq with hc | hc
  · rw [← sum_div, ← mul_sum, ← cross_eq_sum_singleton' G u W, mul_div_cancel_right₀ _ hc.ne']
  · have hsu : sY u = 0 := le_antisymm (by have := hs u hu; rw [← hc, mul_zero] at this; exact this)
      (hs0 u)
    simp [hsu]

theorem sum_crossTerm_row_of_notMem (G : WeightedGraph V) (W Y : Finset V) (sY : V → ℝ) {u : V}
    (hu : u ∉ Y) : ∑ v, crossTerm G W Y sY u v = 0 := by
  unfold crossTerm; simp [hu]

theorem sum_crossTerm_col_of_notMem (G : WeightedGraph V) (W Y : Finset V) (sY : V → ℝ) {v : V}
    (hv : v ∉ W) : ∑ u, crossTerm G W Y sY u v = 0 := by
  unfold crossTerm; simp [hv]

/-- Column sums of the crossing terms are at most `B` times the split-edge capacity. -/
theorem sum_crossTerm_col_le (G : WeightedGraph V) {X W Y : Finset V} (hY : Y = X \ W)
    {sY : V → ℝ} {B : ℝ} (hB : 0 ≤ B) (hs0 : ∀ v, 0 ≤ sY v)
    (hs : ∀ u ∈ Y, sY u ≤ B * G.cross {u} W) (v : V) :
    ∑ u, crossTerm G W Y sY u v ≤ B * G.cross {v} (X \ W) := by
  rw [← hY, cross_eq_sum_singleton' G v Y, mul_sum]
  calc ∑ u, crossTerm G W Y sY u v
      = ∑ u ∈ Y, crossTerm G W Y sY u v := by
        rw [← sum_filter_add_sum_filter_not univ (fun u => u ∈ Y), filter_mem_eq_inter, univ_inter,
          sum_eq_zero (s := univ.filter fun u => u ∉ Y) fun u hu => by
            unfold crossTerm; simp [(mem_filter.mp hu).2], _root_.add_zero]
    _ ≤ ∑ u ∈ Y, B * G.w v u := by
        refine sum_le_sum fun u _ => ?_
        rw [G.symm v u]
        exact crossTerm_le G W Y hB hs u v

/-! ## The refinement flow -/

/-- **The refinement flow** (source Lemma 5, weighted). -/
theorem ref_flow (G : WeightedGraph V) (n : ℕ) {p : ℕ} {X : Finset V} {Cs : Finset (Finset V)}
    (h : Ref G n p X Cs) (hp : p ≤ 2 * n) :
    ∀ j, 1 ≤ j → 2 ^ j * X.card ≤ p → RefFlow G X Cs (Bprod n j) := by
  induction h with
  | final X _ =>
      intro j _ _
      exact refFlow_final G X (one_le_Bprod n j)
  | split X W ρ CsW CsY hcert hW hY ihW ihY =>
    intro j hj hjX
    -- sizes, indices and the step inequality
    have hWX := hcert.subset
    have hW0 := hcert.nonempty
    have hhalf := hcert.half
    have hYX : X \ W ⊆ X := sdiff_subset
    have hXY : X \ (X \ W) = W := Finset.sdiff_sdiff_eq_self hWX
    have hdisjWY : Disjoint W (X \ W) := disjoint_sdiff
    have hX1 : 1 ≤ X.card := hW0.card_pos.trans_le (card_le_card hWX)
    have hjW : 2 ^ (j + 1) * W.card ≤ p := by
      calc 2 ^ (j + 1) * W.card = 2 ^ j * (2 * W.card) := by ring
        _ ≤ 2 ^ j * X.card := Nat.mul_le_mul_left _ hhalf
        _ ≤ p := hjX
    have hjY : 2 ^ j * (X \ W).card ≤ p :=
      le_trans (Nat.mul_le_mul_left _ (card_le_card hYX)) hjX
    obtain ⟨qW, FW, rW, hqW, hFW, hdivW, hrW, hsameW, hdiffW⟩ := ihW (j + 1) (by omega) hjW
    obtain ⟨qY, FY, rY, hqY, hFY, hdivY, hrY, hsameY, hdiffY⟩ := ihY j hj hjY
    have hPW := hW.isPart
    have hPY := hY.isPart
    have hCs : Disjoint CsW CsY := disjoint_parts_of_disjoint hdisjWY hPW hPY
    set B' := Bprod n (j + 1) with hB'def
    set B := Bprod n j with hBdef
    have hB'1 := one_le_Bprod n (j + 1)
    have hB1 := one_le_Bprod n j
    have hB'2 : B' ≤ 2 := Bprod_le_two n (j := j + 1) (by omega)
    have hB2 : B ≤ 2 := Bprod_le_two n hj
    have hB'0 : 0 ≤ B' := by linarith
    have hB0 : 0 ≤ B := by linarith
    have hjL : j ≤ DetMinCut.logL n := by
      have h1 : 2 ^ j ≤ 2 ^ DetMinCut.logL n :=
        calc 2 ^ j ≤ 2 ^ j * X.card := Nat.le_mul_of_pos_right _ hX1
          _ ≤ p := hjX
          _ ≤ 2 * n := hp
          _ ≤ 2 ^ DetMinCut.logL n := DetMinCut.le_two_pow_logL n
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
    have hρ : ρ * (kappa * KK n * j) ≤ 2 :=
      le_trans (mul_le_mul_of_nonneg_left (expFactor_ge hX1 hjX) hcert.rho_nonneg) hcert.rho_small
    have hstep := Bprod_step_ineq hj hjL hcert.rho_nonneg hρ
    -- the excesses
    set sW := excess rW B' G X W with hsWdef
    set sY := excess rY B G X (X \ W) with hsYdef
    have hsW0 : ∀ v, 0 ≤ sW v := excess_nonneg _ _ _ _ _
    have hsY0 : ∀ v, 0 ≤ sY v := excess_nonneg _ _ _ _ _
    have hsWle : ∀ v ∈ W, sW v ≤ B' * G.cross {v} (X \ W) :=
      fun v hv => excess_le hB'0 hWX hv (hrW v hv).2
    have hsYle : ∀ u ∈ X \ W, sY u ≤ B * G.cross {u} W := by
      intro u hu
      have := excess_le hB0 hYX hu (hrY u hu).2
      rwa [hXY] at this
    have hsWout : ∀ v, v ∉ W → sW v = 0 := fun v hv => excess_of_notMem _ _ _ _ _ hv
    have hsYout : ∀ v, v ∉ X \ W → sY v = 0 := fun v hv => excess_of_notMem _ _ _ _ _ hv
    -- routing the `W` excess inside `W`
    obtain ⟨F₁, r₁, hF₁, hdiv₁, hr₁⟩ :=
      exists_route G hWX hcert.rho_nonneg hcert.cutIneq hB'0 sW hsW0 hsWle hsWout
    -- the crossing flow and the received supply in `W`
    set φ := crossTerm G W (X \ W) sY with hφdef
    set F₂ : V → V → ℝ := fun u v => φ u v - φ v u with hF₂def
    set g : V → ℝ := fun v => ∑ u, φ u v with hgdef
    have hg0 : ∀ v, 0 ≤ g v := fun v => sum_nonneg fun u _ => crossTerm_nonneg G _ _ hsY0 u v
    have hgle : ∀ v ∈ W, g v ≤ B * G.cross {v} (X \ W) :=
      fun v _ => sum_crossTerm_col_le G rfl hB0 hsY0 hsYle v
    have hgout : ∀ v, v ∉ W → g v = 0 := fun v hv => sum_crossTerm_col_of_notMem G _ _ _ hv
    obtain ⟨F₃, r₃, hF₃, hdiv₃, hr₃⟩ :=
      exists_route G hWX hcert.rho_nonneg hcert.cutIneq hB0 g hg0 hgle hgout
    -- facts about the crossing flow
    have hF₂flow : IsFlow F₂ := fun u v => by simp only [hF₂def]; ring
    have hφle : ∀ u v, φ u v ≤ B * G.w u v := crossTerm_le G W (X \ W) hB0 hsYle
    have hφ0 : ∀ u v, 0 ≤ φ u v := crossTerm_nonneg G W (X \ W) hsY0
    have hF₂le : ∀ u v, |F₂ u v| ≤ 2 * (splitGraph G W (X \ W)).w u v := by
      intro u v
      rw [splitGraph_w, abs_le]
      have h1 := hφle u v
      have h2 := hφle v u
      have h3 := hφ0 u v
      have h4 := hφ0 v u
      have hw := G.nonneg u v
      rw [G.symm v u] at h2
      by_cases hc : (u ∈ W ∧ v ∈ X \ W) ∨ (u ∈ X \ W ∧ v ∈ W)
      · rw [ite_eq_left hc]
        simp only [hF₂def]
        constructor <;> nlinarith
      · rw [ite_eq_right hc]
        have hφuv : φ u v = 0 := by
          simp only [hφdef, crossTerm]
          rw [ite_eq_right]
          rintro ⟨hu, hv⟩; exact hc (Or.inr ⟨hu, hv⟩)
        have hφvu : φ v u = 0 := by
          simp only [hφdef, crossTerm]
          rw [ite_eq_right]
          rintro ⟨hv, hu⟩; exact hc (Or.inl ⟨hu, hv⟩)
        simp only [hF₂def, hφuv, hφvu, sub_self, mul_zero]
        norm_num
    have hnet₂ : ∀ u, netOut F₂ u = ∑ v, φ u v - ∑ v, φ v u := by
      intro u; unfold netOut; simp only [hF₂def]; rw [sum_sub_distrib]
    have hnet₂Y : ∀ u ∈ X \ W, netOut F₂ u = sY u := by
      intro u hu
      rw [hnet₂, sum_crossTerm_row G W (X \ W) hsY0 hsYle hu,
        sum_crossTerm_col_of_notMem G W (X \ W) sY (disjoint_right.mp hdisjWY hu), sub_zero]
    have hnet₂W : ∀ v ∈ W, netOut F₂ v = - g v := by
      intro v hv
      rw [hnet₂, sum_crossTerm_row_of_notMem G W (X \ W) sY (disjoint_left.mp hdisjWY hv),
        zero_sub]
    -- divergences of the routed flows outside their support vanish
    have hr₁out : ∀ v, v ∉ W → r₁ v = 0 := by
      intro v hv
      have h1 := hdiv₁ v
      rw [hsWout v hv, ((Supported.induce G W).scale _ _).netOut_eq_zero hF₁ hv] at h1
      linarith
    have hr₃out : ∀ v, v ∉ W → r₃ v = 0 := by
      intro v hv
      have h1 := hdiv₃ v
      rw [hgout v hv, ((Supported.induce G W).scale _ _).netOut_eq_zero hF₃ hv] at h1
      linarith
    -- the assembled certificate
    refine ⟨qW.add (qY.add (((G.induce W).scale 4 (by norm_num)).add
        ((splitGraph G W (X \ W)).scale 2 (by norm_num)))),
      fun u v => FW u v + FY u v + F₁ u v + F₂ u v + F₃ u v,
      fun v => if v ∈ W then (rW v - sW v) + r₁ v + r₃ v else rY v - sY v,
      ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · -- supported in `X`
      exact (hqW.mono hWX).add ((hqY.mono hYX).add
        ((((Supported.induce G W).scale _ _).mono hWX).add
          ((splitGraph_supported G hWX hYX).scale _ _)))
    · -- antisymmetry
      intro u v
      have := hFW.1 u v; have := hFY.1 u v; have := hF₁.1 u v; have := hF₂flow u v
      have := hF₃.1 u v
      linarith
    · -- feasibility
      intro u v
      have h1 := hFW.2 u v
      have h2 := hFY.2 u v
      have h3 := hF₁.2 u v
      have h4 := hF₂le u v
      have h5 := hF₃.2 u v
      rw [scale_w, induce_w] at h3 h5
      have hind : 0 ≤ (if u ∈ W ∧ v ∈ W then G.w u v else 0) := by split <;> simp [G.nonneg]
      have hsplit : 0 ≤ (splitGraph G W (X \ W)).w u v := (splitGraph G W (X \ W)).nonneg u v
      simp only [add_w, scale_w, induce_w]
      have ha := abs_add_le (FW u v + FY u v + F₁ u v + F₂ u v) (F₃ u v)
      have hb := abs_add_le (FW u v + FY u v + F₁ u v) (F₂ u v)
      have hc := abs_add_le (FW u v + FY u v) (F₁ u v)
      have hd := abs_add_le (FW u v) (FY u v)
      nlinarith
    · -- divergence
      intro v hv
      dsimp only
      have hnet : netOut (fun u w => FW u w + FY u w + F₁ u w + F₂ u w + F₃ u w) v =
          netOut FW v + netOut FY v + netOut F₁ v + netOut F₂ v + netOut F₃ v := by
        unfold netOut; simp only [sum_add_distrib]
      rw [hnet, pd_union_of_disjoint G hCs]
      by_cases hvW : v ∈ W
      · rw [ite_eq_left hvW, hdivW v hvW, hdiv₁ v, hnet₂W v hvW, hdiv₃ v,
          hqY.netOut_eq_zero hFY (disjoint_left.mp hdisjWY hvW),
          pd_of_notMem G hPY (disjoint_left.mp hdisjWY hvW)]
        ring
      · have hvY : v ∈ X \ W := mem_sdiff.mpr ⟨hv, hvW⟩
        rw [ite_eq_right hvW, hdivY v hvY, hdiv₁ v, hnet₂Y v hvY, hdiv₃ v,
          hqW.netOut_eq_zero hFW hvW, pd_of_notMem G hPW hvW, hsWout v hvW, hr₁out v hvW,
          hgout v hvW, hr₃out v hvW]
        ring
    · -- receiving bounds
      intro v hv
      dsimp only
      have hbd := bd_nonneg G X v
      by_cases hvW : v ∈ W
      · rw [ite_eq_left hvW]
        have h0 := sub_excess_nonneg (r := rW) (B := B') (G := G) (X := X) hvW (hrW v hvW).1 hB'0
        have h1 := sub_excess_le (r := rW) (B := B') (G := G) (X := X) (W := W) hvW
        have h2 := hr₁ v
        have h3 := hr₃ v
        simp only [sinkBound, hvW, ite_true] at h2 h3
        refine ⟨by linarith [h2.1, h3.1], ?_⟩
        have : (rW v - sW v) + r₁ v + r₃ v ≤ (B' + ρ * (B' + B)) * bd G X v := by
          have := h2.2; have := h3.2
          nlinarith
        refine this.trans ?_
        exact mul_le_mul_of_nonneg_right hstep hbd
      · rw [ite_eq_right hvW]
        have hvY : v ∈ X \ W := mem_sdiff.mpr ⟨hv, hvW⟩
        exact ⟨sub_excess_nonneg (r := rY) (B := B) (G := G) (X := X) hvY (hrY v hvY).1 hB0,
          sub_excess_le (r := rY) (B := B) (G := G) (X := X) (W := X \ W) hvY⟩
    · -- loads inside a final part
      intro u v D hD hu hv
      simp only [add_w, scale_w, induce_w, splitGraph_w]
      have hw := G.nonneg u v
      rcases mem_union.mp hD with hDW | hDY
      · have huW := hPW.subset hDW hu
        have hvW := hPW.subset hDW hv
        have hqY0 : qY.w u v = 0 := hqY.w_eq_zero fun h => disjoint_left.mp hdisjWY huW h.1
        have hsp : ¬ ((u ∈ W ∧ v ∈ X \ W) ∨ (u ∈ X \ W ∧ v ∈ W)) := by
          rintro (⟨-, h⟩ | ⟨h, -⟩)
          · exact disjoint_left.mp hdisjWY hvW h
          · exact disjoint_left.mp hdisjWY huW h
        rw [hqY0, ite_eq_left ⟨huW, hvW⟩, ite_eq_right hsp]
        have h1 := hsameW u v D hDW hu hv
        have hD1 : 1 ≤ D.card := (hPW.nonempty D hDW).card_pos
        have hlg := lg_half (hD1.trans (card_le_card (hPW.subset hDW))) hhalf
        nlinarith
      · have huY := hPY.subset hDY hu
        have hvY := hPY.subset hDY hv
        have huW : u ∉ W := disjoint_right.mp hdisjWY huY
        have hqW0 : qW.w u v = 0 := hqW.w_eq_zero fun h => huW h.1
        have hsp : ¬ ((u ∈ W ∧ v ∈ X \ W) ∨ (u ∈ X \ W ∧ v ∈ W)) := by
          rintro (⟨h, -⟩ | ⟨-, h⟩)
          · exact huW h
          · exact disjoint_right.mp hdisjWY hvY h
        rw [hqW0, ite_eq_right (fun h => huW h.1), ite_eq_right hsp]
        have h1 := hsameY u v D hDY hu hv
        have hD1 : 1 ≤ D.card := (hPY.nonempty D hDY).card_pos
        have hlg := lg_mono (hD1.trans (card_le_card (hPY.subset hDY))) (card_le_card hYX)
        nlinarith
    · -- loads across final parts
      intro u v hu hv hsep
      simp only [add_w, scale_w, induce_w, splitGraph_w]
      have hw := G.nonneg u v
      have hlgX := lg_nonneg hX1
      by_cases huW : u ∈ W <;> by_cases hvW : v ∈ W
      · have hqY0 : qY.w u v = 0 := hqY.w_eq_zero fun h => disjoint_left.mp hdisjWY huW h.1
        have hsp : ¬ ((u ∈ W ∧ v ∈ X \ W) ∨ (u ∈ X \ W ∧ v ∈ W)) := by
          rintro (⟨-, h⟩ | ⟨h, -⟩)
          · exact disjoint_left.mp hdisjWY hvW h
          · exact disjoint_left.mp hdisjWY huW h
        rw [hqY0, ite_eq_left ⟨huW, hvW⟩, ite_eq_right hsp]
        have h1 := hdiffW u v huW hvW fun D hD => hsep D (mem_union_left _ hD)
        have hlg := lg_half (hW0.card_pos) hhalf
        nlinarith
      · have hvY : v ∈ X \ W := mem_sdiff.mpr ⟨hv, hvW⟩
        have hqW0 : qW.w u v = 0 := hqW.w_eq_zero fun h => hvW h.2
        have hqY0 : qY.w u v = 0 := hqY.w_eq_zero fun h => disjoint_left.mp hdisjWY huW h.1
        rw [hqW0, hqY0, ite_eq_right (fun h => hvW h.2), ite_eq_left (Or.inl ⟨huW, hvY⟩)]
        nlinarith
      · have huY : u ∈ X \ W := mem_sdiff.mpr ⟨hu, huW⟩
        have hqW0 : qW.w u v = 0 := hqW.w_eq_zero fun h => huW h.1
        have hqY0 : qY.w u v = 0 := hqY.w_eq_zero fun h => disjoint_left.mp hdisjWY hvW h.2
        rw [hqW0, hqY0, ite_eq_right (fun h => huW h.1), ite_eq_left (Or.inr ⟨huY, hvW⟩)]
        nlinarith
      · have huY : u ∈ X \ W := mem_sdiff.mpr ⟨hu, huW⟩
        have hvY : v ∈ X \ W := mem_sdiff.mpr ⟨hv, hvW⟩
        have hqW0 : qW.w u v = 0 := hqW.w_eq_zero fun h => huW h.1
        have hsp : ¬ ((u ∈ W ∧ v ∈ X \ W) ∨ (u ∈ X \ W ∧ v ∈ W)) := by
          rintro (⟨h, -⟩ | ⟨-, h⟩)
          · exact huW h
          · exact hvW h
        rw [hqW0, ite_eq_right (fun h => huW h.1), ite_eq_right hsp]
        have h1 := hdiffY u v huY hvY fun D hD => hsep D (mem_union_right _ hD)
        have hY1 : 1 ≤ (X \ W).card := hY.nonempty.card_pos
        have hlg := lg_mono hY1 (card_le_card hYX)
        nlinarith

end RackeShah
end Hierarchy
end CutQueryComplexity
