import CutQueryComplexity.DirectedCertificate.FlowMeasure
import CutQueryComplexity.DirectedCertificate.SourceSet

set_option autoImplicit false

/-! # The fixed comparison graph for small shores

Equation (5) of paper P3 (`papers/P3/directed-cut-certificates.pdf`).
Heavy capacities `K` and the residual degree vector of `L` define one graph
before the competitor is quantified. Every violating small shore of every
competitor lies in the same finite near-minimum family of this graph.
-/

namespace CutQueryComplexity.DirectedCertificate.Completion

open Finset WeightedDiGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Redirect the residual out-degree to a fixed root, aggregating parallel arcs. -/
noncomputable def comparisonGraph (K L : WeightedDiGraph V) (r : V) : WeightedDiGraph V where
  c u v := K.c u v + if u ≠ r ∧ v = r then L.outdeg u else 0
  nonneg u v := add_nonneg (K.nonneg u v) (by
    split_ifs
    · exact sum_nonneg fun w _ => L.nonneg u w
    · exact le_rfl)
  diag u := by simp [K.diag, and_comm]

theorem comparisonGraph_out (K L : WeightedDiGraph V) {r : V} {S : Finset V} (hr : r ∉ S) :
    (comparisonGraph K L r).out S = K.out S + ∑ u ∈ S, L.outdeg u := by
  simp only [WeightedDiGraph.out, comparisonGraph, sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro u hu
  have hur : u ≠ r := fun h => hr (h ▸ hu)
  simp [hur, hr]

omit [Fintype V] [DecidableEq V] in
theorem internal_nonneg (L : WeightedDiGraph V) (S : Finset V) : 0 ≤ L.internal S :=
  sum_nonneg fun u _ => sum_nonneg fun v _ => L.nonneg u v

theorem out_split {H K L : WeightedDiGraph V}
    (hsplit : ∀ u v, H.c u v = K.c u v + L.c u v) (S : Finset V) :
    H.out S = K.out S + L.out S := by
  simp only [WeightedDiGraph.out, hsplit, sum_add_distrib]

/-- **The comparison-majorant identity.** `A` uses the actual residual `L`,
and is independent of `H'` and `L'`. Only residual out-degrees must be fixed. -/
theorem comparisonGraph_majorant (K L : WeightedDiGraph V) {H' L' : WeightedDiGraph V}
    (hsplit : ∀ u v, H'.c u v = K.c u v + L'.c u v)
    (hdeg : ∀ u, L'.outdeg u = L.outdeg u) {r : V} {S : Finset V} (hr : r ∉ S) :
    (comparisonGraph K L r).out S = H'.out S + L'.internal S := by
  rw [comparisonGraph_out K L hr, out_split hsplit, L'.out_eq_sum_outdeg_sub_internal]
  simp only [hdeg]
  ring

/-- Every input cut avoiding the root is dominated by the comparison graph. -/
theorem out_le_comparisonGraph {H K L : WeightedDiGraph V}
    (hsplit : ∀ u v, H.c u v = K.c u v + L.c u v) {r : V} {S : Finset V} (hr : r ∉ S) :
    H.out S ≤ (comparisonGraph K L r).out S := by
  rw [comparisonGraph_majorant K L hsplit (fun _ => rfl) hr]
  exact le_add_of_nonneg_right (internal_nonneg L S)

omit [Fintype V] [DecidableEq V] in
/-- Uniform arc caps bound all residual internal mass. The weaker `|S|²`
bound already gives the paper's `9λ/8` threshold. -/
theorem internal_le_cap (L : WeightedDiGraph V) {B : ℝ}
    (hcap : ∀ u v, L.c u v ≤ B) (S : Finset V) :
    L.internal S ≤ B * (S.card : ℝ) ^ 2 := by
  calc L.internal S ≤ ∑ _u ∈ S, ∑ _v ∈ S, B :=
      sum_le_sum fun u _ => sum_le_sum fun v _ => hcap u v
    _ = B * (S.card : ℝ) ^ 2 := by simp; ring

omit [Fintype V] in
/-- The diagonal is zero, so the exact cap bound counts only distinct ordered
pairs. This is the degree-cap estimate in the bounded-spread refinement. -/
theorem internal_le_cap_offDiagonal (H : WeightedDiGraph V) {B : ℝ}
    (hcap : ∀ u v, H.c u v ≤ B) {S : Finset V} (hS : S.Nonempty) :
    H.internal S ≤ B * (S.card : ℝ) * ((S.card : ℝ) - 1) := by
  have hs1 : 1 ≤ S.card := hS.card_pos
  have hrow : ∀ u ∈ S, (∑ v ∈ S, H.c u v) ≤ ((S.card : ℝ) - 1) * B := by
    intro u hu
    calc
      (∑ v ∈ S, H.c u v) = ∑ v ∈ S.erase u, H.c u v := by
        rw [← sum_erase_add _ _ hu, H.diag, add_zero]
      _ ≤ ∑ _v ∈ S.erase u, B := sum_le_sum fun v _ => hcap u v
      _ = ((S.card : ℝ) - 1) * B := by
        simp only [sum_const, nsmul_eq_mul, card_erase_of_mem hu, Nat.cast_sub hs1, Nat.cast_one]
  calc H.internal S ≤ ∑ _u ∈ S, ((S.card : ℝ) - 1) * B := sum_le_sum hrow
    _ = B * (S.card : ℝ) * ((S.card : ℝ) - 1) := by simp; ring

/-- Fixed minimum out-degree and a query-enforced arc cap certify every shore
whose size is at most `λ/B`. No promise on the original competitor is used. -/
theorem degree_cap_cut_lower_bound (H : WeightedDiGraph V) {lam B : ℝ}
    (hdegree : ∀ v, lam ≤ H.outdeg v) (hcap : ∀ u v, H.c u v ≤ B)
    {S : Finset V} (hS : S.Nonempty) (hsize : B * S.card ≤ lam) : lam ≤ H.out S := by
  have hs1 : (1 : ℝ) ≤ S.card := by exact_mod_cast hS.card_pos
  have hdeg : (S.card : ℝ) * lam ≤ ∑ u ∈ S, H.outdeg u := by
    calc (S.card : ℝ) * lam = ∑ _u ∈ S, lam := by simp
      _ ≤ ∑ u ∈ S, H.outdeg u := sum_le_sum fun u _ => hdegree u
  have hint := internal_le_cap_offDiagonal H hcap hS
  have hproduct := mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr hsize)
  rw [H.out_eq_sum_outdeg_sub_internal]
  nlinarith

omit [Fintype V] [DecidableEq V] in
/-- A capped residual contributes at most `λ/8` inside a shore of size at most `k`. -/
theorem small_internal_le (L : WeightedDiGraph V) {lam : ℝ} (hlam : 0 ≤ lam)
    {k : ℕ} (hk : 1 ≤ k) (hcap : ∀ u v, L.c u v ≤ lam / (8 * (k : ℝ) ^ 2))
    {S : Finset V} (hS : S.card ≤ k) : L.internal S ≤ lam / 8 := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hcard : (S.card : ℝ) ≤ k := by exact_mod_cast hS
  have hsq : (S.card : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2
  calc L.internal S ≤ lam / (8 * (k : ℝ) ^ 2) * (S.card : ℝ) ^ 2 := internal_le_cap L hcap S
    _ ≤ lam / (8 * (k : ℝ) ^ 2) * (k : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (div_nonneg hlam (by positivity))
    _ = lam / 8 := by field_simp [hk0]

/-- The family to be covered is selected in the explicit comparison graph,
before considering any competitor or any violating shore. -/
noncomputable def comparisonFamily (A : WeightedDiGraph V) (r : V) (lam : ℝ) (k : ℕ) :
    Finset (Finset V) := by
  classical
  exact univ.filter fun S => S.Nonempty ∧ r ∉ S ∧ S.card ≤ k ∧ A.out S < 9 * lam / 8

theorem mem_comparisonFamily {A : WeightedDiGraph V} {r : V} {lam : ℝ} {k : ℕ}
    {S : Finset V} : S ∈ comparisonFamily A r lam k ↔
      S.Nonempty ∧ r ∉ S ∧ S.card ≤ k ∧ A.out S < 9 * lam / 8 := by
  classical
  simp [comparisonFamily]

/-- **The quantifier-order step of W6.** Every small root-avoiding violation in
any nonnegative competitor belongs to one fixed finite family. -/
theorem violating_small_mem_comparisonFamily (K L : WeightedDiGraph V)
    {H' L' : WeightedDiGraph V} {lam : ℝ} (hlam : 0 ≤ lam) {k : ℕ} (hk : 1 ≤ k)
    (hsplit : ∀ u v, H'.c u v = K.c u v + L'.c u v)
    (hdeg : ∀ u, L'.outdeg u = L.outdeg u)
    (hcap : ∀ u v, L'.c u v ≤ lam / (8 * (k : ℝ) ^ 2))
    {r : V} {S : Finset V} (hS : S.Nonempty) (hr : r ∉ S) (hsize : S.card ≤ k)
    (hviol : H'.out S < lam) : S ∈ comparisonFamily (comparisonGraph K L r) r lam k := by
  refine mem_comparisonFamily.mpr ⟨hS, hr, hsize, ?_⟩
  rw [comparisonGraph_majorant K L hsplit hdeg hr]
  have hmass := small_internal_le L' hlam hk hcap hsize
  linarith

/-- Number of arcs of an in-arborescence leaving a shore. -/
noncomputable def leavingCount {r : V} (T : InArb r) (S : Finset V) : ℕ :=
  outN (arcInd T.val) S

theorem leavingCount_cast {r : V} (T : InArb r) (S : Finset V) :
    (leavingCount T S : ℝ) =
      ∑ u ∈ S, ∑ v ∈ Sᶜ, (if T.val u = some v then (1 : ℝ) else 0) := by
  classical
  simp [leavingCount, outN, arcInd]

/-- Every nonempty root-avoiding shore has an outgoing arborescence arc. -/
theorem one_le_leavingCount {r : V} (T : InArb r) {S : Finset V}
    (hS : S.Nonempty) (hr : r ∉ S) : 1 ≤ leavingCount T S := by
  classical
  obtain ⟨u, hu, v, hv, huv⟩ := (mem_inArbs.mp T.property).exists_leaving hS hr
  have hinner : 1 ≤ ∑ w ∈ Sᶜ, arcInd T.val u w := by
    calc 1 = arcInd T.val u v := by simp [arcInd, huv]
      _ ≤ ∑ w ∈ Sᶜ, arcInd T.val u w := single_le_sum (fun _ _ => Nat.zero_le _) (mem_compl.mpr hv)
  change 1 ≤ ∑ u ∈ S, ∑ w ∈ Sᶜ, arcInd T.val u w
  exact hinner.trans (single_le_sum (f := fun u => ∑ w ∈ Sᶜ, arcInd T.val u w)
    (fun _ _ => Nat.zero_le _) hu)

/-- The expected outgoing-arc count is at most the comparison cut capacity. -/
theorem weighted_leavingCount_le {r : V} (A : WeightedDiGraph V)
    (a : InArb r → ℝ) (hload : ∀ u v, load a u v ≤ A.c u v) (S : Finset V) :
    ∑ T, a T * (leavingCount T S : ℝ) ≤ A.out S := by
  simp_rw [leavingCount_cast]
  rw [← sum_load_eq a S Sᶜ]
  exact sum_le_sum fun u _ => sum_le_sum fun v _ => hload u v

/-- A packing contains a tree one-respecting at least half of any fixed family
of root-avoiding cuts with capacity at most `3λ/2`. The W6 family uses `9λ/8`. -/
theorem exists_half_oneRespecting {r : V} (A : WeightedDiGraph V) {lam : ℝ}
    (hlam : 0 < lam) (a : InArb r → ℝ) (ha : ∀ T, 0 ≤ a T)
    (hasum : ∑ T, a T = lam) (hload : ∀ u v, load a u v ≤ A.c u v)
    (F : Finset (Finset V))
    (hF : ∀ S ∈ F, S.Nonempty ∧ r ∉ S ∧ A.out S ≤ 3 * lam / 2) :
    ∃ T : InArb r, 2 * (F.filter fun S => leavingCount T S ≠ 1).card ≤ F.card := by
  classical
  have hmean : (∑ T, a T * ∑ S ∈ F, (leavingCount T S : ℝ)) ≤
      (3 * lam / 2) * F.card := by
    calc (∑ T, a T * ∑ S ∈ F, (leavingCount T S : ℝ))
        = ∑ S ∈ F, ∑ T, a T * (leavingCount T S : ℝ) := by
          simp_rw [mul_sum]
          exact sum_comm
      _ ≤ ∑ S ∈ F, A.out S := sum_le_sum fun S _ => weighted_leavingCount_le A a hload S
      _ ≤ ∑ _S ∈ F, 3 * lam / 2 := sum_le_sum fun S hS => (hF S hS).2.2
      _ = (3 * lam / 2) * F.card := by simp [mul_comm]
  have hpositive : ∃ T : InArb r, 0 < a T := by
    by_contra hn
    push Not at hn
    have hzero : ∑ T, a T ≤ 0 := sum_nonpos fun T _ => hn T
    rw [hasum] at hzero
    linarith
  have hlight : ∃ T : InArb r, 2 * (∑ S ∈ F, leavingCount T S) ≤ 3 * F.card := by
    by_contra hn
    push Not at hn
    obtain ⟨T₀, hT₀⟩ := hpositive
    have hlt : ∀ T : InArb r,
        3 * (F.card : ℝ) < 2 * (∑ S ∈ F, (leavingCount T S : ℝ)) := by
      intro T
      exact_mod_cast hn T
    have hstrict : (∑ T, a T * (3 * (F.card : ℝ))) <
        ∑ T, a T * (2 * ∑ S ∈ F, (leavingCount T S : ℝ)) :=
      sum_lt_sum (fun T _ => mul_le_mul_of_nonneg_left (hlt T).le (ha T))
        ⟨T₀, mem_univ T₀, mul_lt_mul_of_pos_left (hlt T₀) hT₀⟩
    have hleft : (∑ T, a T * (3 * (F.card : ℝ))) = lam * (3 * F.card) := by
      rw [← sum_mul, hasum]
    have hright : (∑ T, a T * (2 * ∑ S ∈ F, (leavingCount T S : ℝ))) =
        2 * ∑ T, a T * ∑ S ∈ F, (leavingCount T S : ℝ) := by
      rw [mul_sum]
      exact sum_congr rfl fun _ _ => by ring
    rw [hleft, hright] at hstrict
    nlinarith
  obtain ⟨T, hT⟩ := hlight
  have hdefect : F.card + (F.filter fun S => leavingCount T S ≠ 1).card ≤
      ∑ S ∈ F, leavingCount T S := by
    calc F.card + (F.filter fun S => leavingCount T S ≠ 1).card
        = ∑ S ∈ F, (1 + if leavingCount T S ≠ 1 then 1 else 0) := by
          simp [sum_add_distrib, card_filter]
      _ ≤ ∑ S ∈ F, leavingCount T S := by
        apply sum_le_sum
        intro S hS
        have hp := one_le_leavingCount T (hF S hS).1 (hF S hS).2.1
        split_ifs with heq <;> omega
  exact ⟨T, by omega⟩

/-- Vertices of a shore whose parent arc leaves that shore. -/
noncomputable def exitVertices {r : V} (T : InArb r) (S : Finset V) : Finset V := by
  classical
  exact S.filter fun u => ∃ v, v ∉ S ∧ T.val u = some v

/-- Each vertex has at most one parent, so arc count equals exit-vertex count. -/
theorem exitVertices_card {r : V} (T : InArb r) (S : Finset V) :
    (exitVertices T S).card = leavingCount T S := by
  classical
  unfold exitVertices leavingCount outN
  rw [card_filter]
  apply sum_congr rfl
  intro u _
  cases hp : T.val u with
  | none => simp [arcInd, hp]
  | some v => simp [arcInd, hp]

/-- Paths that follow parent edges without leaving a shore. -/
def ParentPathIn {r : V} (T : InArb r) (S : Finset V) (u v : V) : Prop :=
  Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ T.val a = some b) u v

/-- A one-respected root-avoiding shore is connected: every vertex has an
internal parent path to its unique exit vertex. This gives explicit path
witnesses, without assuming connectedness of the shore. -/
theorem oneRespecting_internal_paths {r : V} (T : InArb r) {S : Finset V}
    (hr : r ∉ S) (hone : leavingCount T S = 1) :
    ∃ x ∈ S, ∀ v ∈ S, ParentPathIn T S v x := by
  classical
  obtain ⟨x, hx⟩ := card_eq_one.mp ((exitVertices_card T S).trans hone)
  have hxS : x ∈ S := (mem_filter.mp (show x ∈ exitVertices T S from by rw [hx]; simp)).1
  have hunique : ∀ v ∈ S, ∀ w, w ∉ S → T.val v = some w → v = x := by
    intro v hv w hw hp
    have hmem : v ∈ exitVertices T S := mem_filter.mpr ⟨hv, w, hw, hp⟩
    simpa only [hx, mem_singleton] using hmem
  have hT := mem_inArbs.mp T.property
  have hpaths : ∀ (n : ℕ) (v : V), v ∈ S →
      (parentStep T.val)^[n] (some v) = none → ParentPathIn T S v x := by
    intro n
    induction n with
    | zero => intro v _ hn; simp at hn
    | succ n ih =>
      intro v hv hn
      have hvr : v ≠ r := fun h => hr (h ▸ hv)
      cases hp : T.val v with
      | none => exact (hT.nonroot v hvr hp).elim
      | some w =>
        by_cases hw : w ∈ S
        · have hstep : parentStep T.val (some v) = some w := by simp [parentStep, hp]
          rw [Function.iterate_succ_apply, hstep] at hn
          exact (Relation.ReflTransGen.single ⟨hv, hw, hp⟩).trans (ih w hw hn)
        · have hvx := hunique v hv w hw hp
          subst v
          exact Relation.ReflTransGen.refl
  refine ⟨x, hxS, fun v hv => ?_⟩
  obtain ⟨n, hn⟩ := hT.acyclic v
  exact hpaths n v hv hn

end CutQueryComplexity.DirectedCertificate.Completion

#print axioms CutQueryComplexity.DirectedCertificate.Completion.violating_small_mem_comparisonFamily

#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_half_oneRespecting

#print axioms CutQueryComplexity.DirectedCertificate.Completion.oneRespecting_internal_paths

#print axioms CutQueryComplexity.DirectedCertificate.Completion.degree_cap_cut_lower_bound
