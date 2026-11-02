import CutQueryComplexity.Certificate.FlowCert
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Bitwise

/-! # Isolating-cut certificates (Lemma 7)

For terminals `R` and `v ∈ R`, `isoValue G R v = min {c_G(S) : S ∩ R = {v}}`.

* `subset_of_isoMinimal`: an inclusion-minimal minimum isolating shore lies in every
  optimal bit-cut shore containing its terminal (submodular uncrossing). It is stated
  for an arbitrary graph, so it applies inside every consistent graph.
* `exists_isoCert`: all values `isoValue G R v`, `v ∈ R`, are certified by at most
  `9 n (⌈log₂ |R|⌉ + 1)` shores.

Terminals receive distinct binary labels of length `k = ⌈log₂ |R|⌉`. Each bit cut is
certified optimal by `exists_cutCert`. The cell `P v` of `v` is the intersection of
the bit-cut shores containing `v`. A flow in `G` from `v` to the outside of `P v`
is certified on `P v` by the local form of `exists_flowCert`; the cells are disjoint,
so these local certificates cost `O(n)` together.
-/

namespace CutQueryComplexity
namespace Certificate

open WeightedGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Shores whose terminal set is exactly `{v}`. -/
def isoShores (R : Finset V) (v : V) : Finset (Finset V) :=
  Finset.univ.filter fun S => S ∩ R = {v}

/-- Minimum isolating-cut value of `v` among the terminals `R` (zero if `v ∉ R`). -/
noncomputable def isoValue (G : WeightedGraph V) (R : Finset V) (v : V) : ℝ :=
  if h : (isoShores R v).Nonempty then (isoShores R v).inf' h G.cut else 0

theorem mem_isoShores {R : Finset V} {v : V} {S : Finset V} :
    S ∈ isoShores R v ↔ S ∩ R = {v} := by simp [isoShores]

theorem isoShores_nonempty {R : Finset V} {v : V} (hv : v ∈ R) : (isoShores R v).Nonempty :=
  ⟨{v}, mem_isoShores.mpr (by simp [hv])⟩

theorem isoValue_le (G : WeightedGraph V) {R : Finset V} {v : V} {S : Finset V}
    (hS : S ∩ R = {v}) : isoValue G R v ≤ G.cut S := by
  have hm := mem_isoShores.mpr hS
  rw [isoValue, dite_eq_left ⟨S, hm⟩]
  exact Finset.inf'_le _ hm

/-- A minimum isolating shore of minimum cardinality. -/
theorem exists_isoMinimal (G : WeightedGraph V) {R : Finset V} {v : V} (hv : v ∈ R) :
    ∃ S, S ∩ R = {v} ∧ G.cut S = isoValue G R v ∧
      ∀ S', S' ∩ R = {v} → G.cut S' ≤ G.cut S → S.card ≤ S'.card := by
  have hne := isoShores_nonempty hv
  obtain ⟨S₀, hS₀, hmin₀⟩ := Finset.exists_mem_eq_inf' hne G.cut
  set M := (isoShores R v).filter fun S => G.cut S = G.cut S₀
  have hMne : M.Nonempty := ⟨S₀, Finset.mem_filter.mpr ⟨hS₀, rfl⟩⟩
  obtain ⟨S, hSM, hSmin⟩ := Finset.exists_min_image M Finset.card hMne
  obtain ⟨hS, hScut⟩ := Finset.mem_filter.mp hSM
  have hval : isoValue G R v = G.cut S₀ := by rw [isoValue, dite_eq_left hne, hmin₀]
  refine ⟨S, mem_isoShores.mp hS, by rw [hScut, hval], fun S' hS' hle => hSmin S' ?_⟩
  refine Finset.mem_filter.mpr ⟨mem_isoShores.mpr hS', le_antisymm (hScut ▸ hle) ?_⟩
  rw [← hval]; exact isoValue_le G hS'

/-- Uncrossing: a cardinality-minimal minimum isolating shore lies in every optimal
shore containing the terminal class `C ∋ v` and avoiding the class `D ∌ v`. -/
theorem subset_of_isoMinimal (H : WeightedGraph V) {R C D T S : Finset V} {v : V}
    (hvC : v ∈ C) (hvD : v ∉ D) (hCT : C ⊆ T) (hTD : Disjoint T D) (hDR : D ⊆ R)
    (hT : ∀ X, C ⊆ X → Disjoint X D → H.cut T ≤ H.cut X)
    (hS : S ∩ R = {v})
    (hScard : ∀ S', S' ∩ R = {v} → H.cut S' ≤ H.cut S → S.card ≤ S'.card) : S ⊆ T := by
  have hvT : v ∈ T := hCT hvC
  have hiso : (S ∩ T) ∩ R = {v} := by
    rw [Finset.inter_right_comm, hS]
    exact Finset.singleton_inter_of_mem hvT
  have hdisj : Disjoint (S ∪ T) D := by
    refine Finset.disjoint_union_left.mpr ⟨Finset.disjoint_left.mpr fun x hxS hxD => ?_, hTD⟩
    have : x ∈ S ∩ R := Finset.mem_inter.mpr ⟨hxS, hDR hxD⟩
    rw [hS, Finset.mem_singleton] at this
    exact hvD (this ▸ hxD)
  have h1 := hT (S ∪ T) (hCT.trans Finset.subset_union_right) hdisj
  have h2 := H.cut_submodular S T
  have h3 : H.cut (S ∩ T) ≤ H.cut S := by linarith
  have hcard := hScard _ hiso h3
  have : S ∩ T = S := Finset.eq_of_subset_of_card_le Finset.inter_subset_left hcard
  rw [← this]; exact Finset.inter_subset_right

/-! ### Binary labels -/

/-- Position of a terminal in `R`. -/
noncomputable def termIdx (R : Finset V) (v : V) : ℕ :=
  if h : v ∈ R then (R.equivFin ⟨v, h⟩ : ℕ) else 0

omit [Fintype V] in
theorem termIdx_lt {R : Finset V} {v : V} (hv : v ∈ R) : termIdx R v < R.card := by
  simp [termIdx, hv]

omit [Fintype V] in
theorem termIdx_inj {R : Finset V} {v w : V} (hv : v ∈ R) (hw : w ∈ R)
    (h : termIdx R v = termIdx R w) : v = w := by
  simp only [termIdx, hv, hw, dite_true] at h
  have := R.equivFin.injective (Fin.val_injective h)
  exact congrArg Subtype.val this

omit [Fintype V] in
/-- Distinct terminals differ in one of the first `⌈log₂ |R|⌉` bits. -/
theorem exists_bit_ne {R : Finset V} {v w : V} (hv : v ∈ R) (hw : w ∈ R) (hvw : v ≠ w) :
    ∃ j < Nat.clog 2 R.card, (termIdx R v).testBit j ≠ (termIdx R w).testBit j := by
  by_contra hall
  push Not at hall
  apply hvw
  apply termIdx_inj hv hw
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < Nat.clog 2 R.card
  · exact hall j hj
  · have hpow : R.card ≤ 2 ^ j := (Nat.le_pow_clog (by norm_num) _).trans
      (Nat.pow_le_pow_right (by norm_num) (not_lt.mp hj))
    rw [Nat.testBit_eq_false_of_lt ((termIdx_lt hv).trans_le hpow),
      Nat.testBit_eq_false_of_lt ((termIdx_lt hw).trans_le hpow)]

/-- Terminals whose bit `j` equals `b`. -/
noncomputable def bitClass (R : Finset V) (j : ℕ) (b : Bool) : Finset V :=
  R.filter fun v => (termIdx R v).testBit j = b

omit [Fintype V] in
theorem mem_bitClass {R : Finset V} {j : ℕ} {b : Bool} {v : V} :
    v ∈ bitClass R j b ↔ v ∈ R ∧ (termIdx R v).testBit j = b := by
  simp [bitClass]

omit [Fintype V] in
theorem disjoint_bitClass (R : Finset V) (j : ℕ) :
    Disjoint (bitClass R j true) (bitClass R j false) := by
  rw [Finset.disjoint_left]
  intro v h1 h2
  rw [mem_bitClass] at h1 h2
  rw [h1.2] at h2; exact Bool.noConfusion h2.2

/-! ### The certificate -/

/-- Lemma 7: isolating-cut values are certified with `O(n log |R|)` shores. -/
theorem exists_isoCert (G : WeightedGraph V) (R : Finset V) :
    ∃ Q : Finset (Finset V),
      Q.card ≤ 9 * Fintype.card V * (Nat.clog 2 R.card + 1) ∧
      ∀ G' : WeightedGraph V, Consistent G G' Q → ∀ v ∈ R, isoValue G' R v = isoValue G R v := by
  set n := Fintype.card V
  set k := Nat.clog 2 R.card
  -- Bit cuts and their certificates.
  choose T hTA hTB Qb hTQ hQb hbit using fun j : ℕ =>
    exists_cutCert G (bitClass R j true) (bitClass R j false) (disjoint_bitClass R j)
  -- The bit-cut shore on the side of `v`.
  set Tv : V → ℕ → Finset V := fun v j =>
    if (termIdx R v).testBit j = true then T j else (T j)ᶜ
  have hTv : ∀ H : WeightedGraph V, ∀ j, Consistent G H (Qb j) → ∀ v ∈ R,
      bitClass R j ((termIdx R v).testBit j) ⊆ Tv v j ∧
      Disjoint (Tv v j) (bitClass R j (!(termIdx R v).testBit j)) ∧
      ∀ X, bitClass R j ((termIdx R v).testBit j) ⊆ X →
        Disjoint X (bitClass R j (!(termIdx R v).testBit j)) → H.cut (Tv v j) ≤ H.cut X := by
    intro H j hH v _
    by_cases hb : (termIdx R v).testBit j = true
    · simp only [Tv, hb, ite_true, Bool.not_true]
      exact ⟨hTA j, hTB j, hbit j H hH⟩
    · simp only [Bool.not_eq_true] at hb
      simp only [Tv, hb, Bool.false_eq_true, ite_false, Bool.not_false]
      refine ⟨?_, ?_, fun X hX hXd => ?_⟩
      · intro x hx
        rw [Finset.mem_compl]
        exact Finset.disjoint_left.mp (hTB j).symm hx
      · exact Finset.disjoint_left.mpr fun x hx hA => (Finset.mem_compl.mp hx) (hTA j hA)
      · have h1 : bitClass R j true ⊆ Xᶜ := fun x hx =>
          Finset.mem_compl.mpr fun hX' => Finset.disjoint_left.mp hXd hX' hx
        have h2 : Disjoint Xᶜ (bitClass R j false) :=
          Finset.disjoint_left.mpr fun x hx hB => (Finset.mem_compl.mp hx) (hX hB)
        have := hbit j H hH Xᶜ h1 h2
        rwa [cut_compl, ← cut_compl H (T j)] at this
  -- Cells.
  set P : V → Finset V := fun v => Finset.univ.filter fun x => ∀ j < k, x ∈ Tv v j
  have hvP : ∀ v ∈ R, v ∈ P v := by
    intro v hv
    simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
    intro j _
    exact (hTv G j (fun _ _ => rfl) v hv).1 (mem_bitClass.mpr ⟨hv, rfl⟩)
  have hsep : ∀ v ∈ R, ∀ w ∈ R, v ≠ w → ∃ j < k,
      Disjoint (Tv v j) (Tv w j) ∧ w ∉ Tv v j := by
    intro v hv w hw hvw
    obtain ⟨j, hj, hne⟩ := exists_bit_ne hv hw hvw
    refine ⟨j, hj, ?_, ?_⟩
    · simp only [Tv]
      cases h1 : (termIdx R v).testBit j <;> cases h2 : (termIdx R w).testBit j <;>
        simp_all [disjoint_compl_left, disjoint_compl_right]
    · have hw' : w ∈ bitClass R j (!(termIdx R v).testBit j) := by
        refine mem_bitClass.mpr ⟨hw, ?_⟩
        cases h1 : (termIdx R v).testBit j <;> cases h2 : (termIdx R w).testBit j <;> simp_all
      exact fun h => Finset.disjoint_left.mp (hTv G j (fun _ _ => rfl) v hv).2.1 h hw'
  have hPR : ∀ v ∈ R, P v ∩ R = {v} := by
    intro v hv
    ext w
    simp only [Finset.mem_inter, Finset.mem_singleton]
    constructor
    · rintro ⟨hwP, hwR⟩
      by_contra hvw
      obtain ⟨j, hj, -, hwT⟩ := hsep v hv w hwR (Ne.symm hvw)
      simp only [P, Finset.mem_filter, Finset.mem_univ, true_and] at hwP
      exact hwT (hwP j hj)
    · rintro rfl; exact ⟨hvP w hv, hv⟩
  have hPdisj : (R : Set V).PairwiseDisjoint P := by
    intro v hv w hw hvw
    obtain ⟨j, hj, hd, -⟩ := hsep v hv w hw hvw
    refine Finset.disjoint_left.mpr fun x hxv hxw => ?_
    simp only [P, Finset.mem_filter, Finset.mem_univ, true_and] at hxv hxw
    exact Finset.disjoint_left.mp hd (hxv j hj) (hxw j hj)
  have hPsum : ∑ v ∈ R, (P v).card ≤ n := by
    rw [← Finset.card_biUnion hPdisj]; exact Finset.card_le_univ _
  -- Local flow certificates on the cells.
  have hloc : ∀ v ∈ R, ∃ Qv : Finset (Finset V), Qv.card ≤ 8 * (P v).card ∧
      ∀ G' : WeightedGraph V, Consistent G G' Qv →
        ∀ S ⊆ P v, v ∈ S → isoValue G R v ≤ G'.cut S := by
    intro v hv
    have hdisj : Disjoint ({v} : Finset V) (P v)ᶜ := by simpa using hvP v hv
    obtain ⟨f, S₀, hf, hcons, -, -, hS₀B, hval⟩ :=
      exists_maxFlow G {v} (P v)ᶜ hdisj G.degree
        (fun x => Finset.sum_nonneg fun u _ => G.nonneg x u)
    have hS₀P : S₀ ⊆ P v := fun x hx => by
      by_contra h; exact Finset.disjoint_left.mp hS₀B hx (Finset.mem_compl.mpr h)
    have hiso : (S₀ ∪ {v}) ∩ R = {v} := by
      refine Finset.Subset.antisymm ?_ ?_
      · have h := Finset.inter_subset_inter (Finset.union_subset hS₀P
          (Finset.singleton_subset_iff.mpr (hvP v hv))) (le_refl R)
        rwa [hPR v hv] at h
      · simp [hv]
    have hge : isoValue G R v ≤ netOut f v := by
      have h1 := isoValue_le G hiso
      have h2 := cut_union_le G S₀ {v}
      rw [Finset.sum_singleton] at hval
      linarith
    obtain ⟨Qv, hQv, hcert⟩ := exists_flowCert G (P v) hf
    refine ⟨Qv, hQv, fun G' hG' S hSP hvS => ?_⟩
    obtain ⟨f', hf', hnet'⟩ := hcert G' hG'
    have hsum : ∑ x ∈ S, netOut f' x = netOut f v := by
      rw [Finset.sum_congr rfl fun x hx => hnet' x (hSP hx)]
      rw [Finset.sum_eq_single_of_mem v hvS]
      intro x hxS hxv
      exact hcons x (by simpa using hxv) (by simpa using hSP hxS)
    have := sum_netOut_le_cut hf' S
    linarith
  choose! Qv hQv hQvcert using hloc
  -- Optimal isolating shores of `G` for the upper bounds.
  have hup : ∀ v ∈ R, ∃ S, S ∩ R = {v} ∧ G.cut S = isoValue G R v := fun v hv => by
    obtain ⟨S, hS, hc, -⟩ := exists_isoMinimal G hv; exact ⟨S, hS, hc⟩
  choose! Sopt hSopt hSoptc using hup
  set Q := (Finset.range k).biUnion Qb ∪ R.biUnion Qv ∪ R.image Sopt
  refine ⟨Q, ?_, fun G' hG' v hv => ?_⟩
  · -- counting
    have c1 : ((Finset.range k).biUnion Qb).card ≤ k * (8 * n + 1) := by
      refine Finset.card_biUnion_le.trans ?_
      refine (Finset.sum_le_sum fun j _ => hQb j).trans ?_
      rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    have c2 : (R.biUnion Qv).card ≤ 8 * n := by
      refine Finset.card_biUnion_le.trans ?_
      refine (Finset.sum_le_sum fun v hv => hQv v hv).trans ?_
      rw [← Finset.mul_sum]; omega
    have c3 : (R.image Sopt).card ≤ n := Finset.card_image_le.trans (Finset.card_le_univ _)
    have c4 : Q.card ≤ ((Finset.range k).biUnion Qb ∪ R.biUnion Qv).card + (R.image Sopt).card :=
      Finset.card_union_le _ _
    have c5 := Finset.card_union_le ((Finset.range k).biUnion Qb) (R.biUnion Qv)
    have hn : 1 ≤ n ∨ k = 0 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · right
        have : R.card = 0 := by
          have := Finset.card_le_univ R; omega
        simp [k, this]
      · left; exact h
    have : k * (8 * n + 1) + 8 * n + n ≤ 9 * n * (k + 1) := by
      rcases hn with h | h
      · nlinarith
      · rw [h]; omega
    omega
  · have hG'b : ∀ j < k, Consistent G G' (Qb j) := fun j hj =>
      hG'.mono (fun S hS => Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj, hS⟩)))
    have hG'v : Consistent G G' (Qv v) := hG'.mono (fun S hS => Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨v, hv, hS⟩)))
    have hSopt' : G'.cut (Sopt v) = G.cut (Sopt v) :=
      hG' _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hv))
    obtain ⟨S, hS, hScut, hScard⟩ := exists_isoMinimal G' hv
    have hSP : S ⊆ P v := by
      intro x hx
      simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
      intro j hj
      obtain ⟨hC, hD, hopt⟩ := hTv G' j (hG'b j hj) v hv
      have hsub := subset_of_isoMinimal G' (mem_bitClass.mpr ⟨hv, rfl⟩)
        (fun h => by simp [mem_bitClass] at h) hC hD (Finset.filter_subset _ _) hopt hS hScard
      exact hsub hx
    have hvS : v ∈ S := by
      have : v ∈ S ∩ R := by rw [hS]; exact Finset.mem_singleton_self v
      exact (Finset.mem_inter.mp this).1
    refine le_antisymm ?_ ?_
    · have := isoValue_le G' (hSopt v hv)
      rw [hSopt', hSoptc v hv] at this; exact this
    · rw [← hScut]; exact hQvcert v hv G' hG'v S hSP hvS

end Certificate
end CutQueryComplexity
