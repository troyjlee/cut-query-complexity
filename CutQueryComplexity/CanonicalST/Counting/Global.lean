import CutQueryComplexity.CanonicalST.Counting.Partition
import CutQueryComplexity.CanonicalST.Counting.Local
import Mathlib.Data.Fintype.BigOperators

/-!
# Joint integer budgets and the global labeling count

Each labeling is encoded by its restrictions to the actual partition blocks.
Its natural internal cut values form one vector with sum at most the global
cut value. The union below ranges over those jointly bounded vectors, rather
than assigning the full global budget separately to each block.
-/

set_option autoImplicit false

namespace CutQueryComplexity.CanonicalST.Counting

noncomputable section
open Finset WeightedGraph AllPairsAudit
open scoped Classical

section Vectors
variable {I A : Type*} [Fintype I] [DecidableEq A]

/-- Actual natural budget vectors satisfying one shared sum constraint. -/
def budgetVectors (I : Type*) [Fintype I] (b : ℕ) : Finset (I → ℕ) :=
  (Fintype.piFinset (fun _ : I => range (b + 1))).filter (fun a => ∑ i, a i ≤ b)

@[simp] theorem mem_budgetVectors (b : ℕ) (a : I → ℕ) :
    a ∈ budgetVectors I b ↔ ∑ i, a i ≤ b := by
  constructor
  · intro h
    exact (mem_filter.mp h).2
  · intro h
    refine mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_, h⟩
    intro i
    have hi : a i ≤ ∑ j, a j := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)
    exact mem_range.mpr (by omega)

theorem budgetVectors_card_le (b : ℕ) :
    (budgetVectors I b).card ≤ (b + 1) ^ Fintype.card I := by
  calc
    _ ≤ (Fintype.piFinset (fun _ : I => range (b + 1))).card := card_filter_le _ _
    _ = _ := by simp

/-- Count products over only the jointly bounded budgets. The exponent premise
is arithmetic about the supplied local exponents, not a counting assumption. -/
theorem jointFamilies_card_le (F : I → ℕ → Finset A) (e : I → ℕ → ℕ)
    (b B E : ℕ) (hB : 1 ≤ B) (hb : b + 1 ≤ B)
    (hlocal : ∀ i a, (F i a).card ≤ B ^ e i a)
    (hE : ∀ a ∈ budgetVectors I b, (∑ i, e i (a i)) + Fintype.card I ≤ E) :
    ((budgetVectors I b).biUnion (fun a => Fintype.piFinset (fun i => F i (a i)))).card ≤
      B ^ E := by
  have hzero : (fun _ : I => 0) ∈ budgetVectors I b := by simp
  have hq : Fintype.card I ≤ E := by
    have := hE _ hzero
    omega
  have hbranch (a : I → ℕ) (ha : a ∈ budgetVectors I b) :
      (Fintype.piFinset (fun i => F i (a i))).card ≤ B ^ (E - Fintype.card I) := by
    calc
      _ = ∏ i, (F i (a i)).card := Fintype.card_piFinset _
      _ ≤ ∏ i, B ^ e i (a i) := prod_le_prod (fun i _ => hlocal i _)
      _ = B ^ (∑ i, e i (a i)) := prod_pow_eq_pow_sum _ _ _
      _ ≤ B ^ (E - Fintype.card I) := pow_le_pow_right' hB (by have := hE a ha; omega)
  calc
    _ ≤ ∑ a ∈ budgetVectors I b, (Fintype.piFinset (fun i => F i (a i))).card := card_biUnion_le
    _ ≤ ∑ _a ∈ budgetVectors I b, B ^ (E - Fintype.card I) := sum_le_sum hbranch
    _ = (budgetVectors I b).card * B ^ (E - Fintype.card I) := by simp
    _ ≤ (b + 1) ^ Fintype.card I * B ^ (E - Fintype.card I) :=
      Nat.mul_le_mul_right _ (budgetVectors_card_le b)
    _ ≤ B ^ Fintype.card I * B ^ (E - Fintype.card I) :=
      Nat.mul_le_mul_right _ (pow_le_pow_left' hb _)
    _ = B ^ E := by rw [← pow_add, Nat.add_sub_of_le hq]

end Vectors

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The actual core labelings at the requested global cut budget. -/
def coreLabelings (J : WeightedGraph V) (C : Finset V) (b : ℕ) : Finset (Finset V) :=
  C.powerset.filter (fun S => J.cut S ≤ (b : ℝ))

@[simp] theorem mem_coreLabelings (J : WeightedGraph V) (C S : Finset V) (b : ℕ) :
    S ∈ coreLabelings J C b ↔ S ⊆ C ∧ J.cut S ≤ (b : ℝ) := by
  simp [coreLabelings]

omit [Fintype V] in
theorem cross_integral (J : WeightedGraph V) (hJ : Unweighted J) (S T : Finset V) :
    ∃ a : ℕ, J.cross S T = a := by
  choose a ha using (fun u : V => incident_integral hJ u T)
  refine ⟨∑ u ∈ S, a u, ?_⟩
  change (∑ u ∈ S, incident J u T) = _
  simp only [ha, Nat.cast_sum]

/-- This is the internal cut value itself; integrality proves no rounding loss. -/
def internalBudget (J : WeightedGraph V) (U S : Finset V) : ℕ :=
  ⌊J.localCut U S⌋₊

theorem internalBudget_cast (J : WeightedGraph V) (hJ : Unweighted J) (U S : Finset V) :
    (internalBudget J U S : ℝ) = J.localCut U S := by
  obtain ⟨a, ha⟩ := cross_integral J hJ (S ∩ U) (U \ S)
  change (⌊J.cross (S ∩ U) (U \ S)⌋₊ : ℝ) = J.cross (S ∩ U) (U \ S)
  rw [ha, Nat.floor_natCast]

/-- Disjoint blocks cannot count the same internal crossing edge twice. -/
theorem sum_localCut_le (J : WeightedGraph V) {C : Finset V}
    (P : Finpartition C) (S : Finset V) :
    (∑ U ∈ P.parts, J.localCut U S) ≤ J.cut S := by
  have hd : (P.parts : Set (Finset V)).PairwiseDisjoint (fun U => S ∩ U) := by
    intro U hU W hW hne
    exact (P.disjoint hU hW hne).mono inter_subset_right inter_subset_right
  have hunion : P.parts.biUnion (fun U => S ∩ U) ⊆ S := by
    intro v hv
    obtain ⟨U, _, hv⟩ := mem_biUnion.mp hv
    exact (mem_inter.mp hv).1
  calc
    _ ≤ ∑ U ∈ P.parts, J.cross (S ∩ U) Sᶜ := by
      apply sum_le_sum
      intro U _
      exact J.cross_mono (Subset.refl _) (by
        intro v hv
        exact mem_compl.mpr (mem_sdiff.mp hv).2)
    _ = J.cross (P.parts.biUnion (fun U => S ∩ U)) Sᶜ := by
      unfold cross
      rw [sum_biUnion hd]
    _ ≤ J.cross S Sᶜ := J.cross_mono hunion (Subset.refl _)
    _ = J.cut S := rfl

theorem sum_internalBudget_le (J : WeightedGraph V) (hJ : Unweighted J)
    {C : Finset V} (P : Finpartition C) (S : Finset V) {b : ℕ}
    (hcut : J.cut S ≤ (b : ℝ)) :
    (∑ U : P.parts, internalBudget J U.val S) ≤ b := by
  have hreal : ((∑ U : P.parts, internalBudget J U.val S : ℕ) : ℝ) ≤ (b : ℝ) := by
    rw [Nat.cast_sum]
    simp only [internalBudget_cast J hJ]
    rw [sum_coe_sort P.parts (fun U : Finset V => J.localCut U S)]
    exact (sum_localCut_le J P S).trans hcut
  exact_mod_cast hreal

omit [Fintype V] in
/-- Restrictions to all actual blocks determine a core labeling. -/
theorem blockTrace_injective {C : Finset V} (P : Finpartition C)
    {S T : Finset V} (hS : S ⊆ C) (hT : T ⊆ C)
    (he : (fun U : P.parts => S ∩ U.val) = (fun U : P.parts => T ∩ U.val)) : S = T := by
  have hsub {A B : Finset V} (hA : A ⊆ C)
      (he : (fun U : P.parts => A ∩ U.val) = (fun U : P.parts => B ∩ U.val)) : A ⊆ B := by
    intro v hv
    obtain ⟨U, hU, hvU⟩ := P.exists_mem (hA hv)
    have hi : v ∈ A ∩ U := mem_inter.mpr ⟨hv, hvU⟩
    have heU := congrFun he ⟨U, hU⟩
    change A ∩ U = B ∩ U at heU
    rw [heU] at hi
    exact (mem_inter.mp hi).1
  exact Subset.antisymm (hsub hS he) (hsub hT he.symm)

/-- Explicit natural exponent; the factor 32 absorbs the local integer ceilings. -/
def countExponent (N b D : ℕ) : ℕ := ⌈32 * ((N : ℝ) + (b : ℝ)) / (D : ℝ)⌉₊

omit [Fintype V] in
theorem jointExponent_le {C : Finset V} (P : Finpartition C)
    {D b : ℕ} (hD : 0 < D)
    (hparts : (P.parts.card : ℝ) ≤ 4 * (C.card : ℝ) / (D : ℝ))
    (a : P.parts → ℕ) (ha : a ∈ budgetVectors P.parts b) :
    (∑ U : P.parts, localExponent ((D : ℝ) / 8) (a U)) + Fintype.card P.parts ≤
      countExponent C.card b D := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hτ : (0 : ℝ) < (D : ℝ) / 8 := by positivity
  have hterm (U : P.parts) :
      (localExponent ((D : ℝ) / 8) (a U) : ℝ) * D ≤ 5 * D + 16 * (a U : ℝ) := by
    have he := localExponent_le hτ (a U)
    have hm := mul_le_mul_of_nonneg_right he hτ.le
    rw [add_mul, div_mul_cancel₀ _ hτ.ne'] at hm
    nlinarith
  have hs := sum_le_sum (s := (univ : Finset P.parts)) (fun U _ => hterm U)
  have hab : ((∑ U : P.parts, a U : ℕ) : ℝ) ≤ (b : ℝ) := by
    exact_mod_cast (mem_budgetVectors b a).mp ha
  have hpr : (P.parts.card : ℝ) * D ≤ 4 * (C.card : ℝ) :=
    (le_div_iff₀ hDr).mp hparts
  have hsum : ((∑ U : P.parts, localExponent ((D : ℝ) / 8) (a U) : ℕ) : ℝ) * D ≤
      5 * D * (P.parts.card : ℝ) + 16 * (b : ℝ) := by
    simp only [sum_add_distrib, sum_const, nsmul_eq_mul, ← sum_mul, ← mul_sum,
      ← Nat.cast_sum, card_univ, Fintype.card_coe] at hs
    nlinarith
  have hreal :
      (((∑ U : P.parts, localExponent ((D : ℝ) / 8) (a U)) +
        Fintype.card P.parts : ℕ) : ℝ) ≤
      32 * ((C.card : ℝ) + (b : ℝ)) / (D : ℝ) := by
    apply (le_div_iff₀ hDr).mpr
    simp only [Nat.cast_add, Fintype.card_coe]
    nlinarith [(Nat.cast_nonneg C.card : (0 : ℝ) ≤ (C.card : ℝ)),
      (Nat.cast_nonneg b : (0 : ℝ) ≤ (b : ℝ))]
  have hceil : 32 * ((C.card : ℝ) + (b : ℝ)) / (D : ℝ) ≤
      (countExponent C.card b D : ℝ) :=
    Nat.le_ceil (32 * ((C.card : ℝ) + (b : ℝ)) / (D : ℝ))
  exact_mod_cast hreal.trans hceil

set_option maxHeartbeats 1000000 in

/-- The actual restriction encoding and its jointly bounded internal budgets
give the count for any partition constructed with the stated connectivity. -/
theorem partitionLabelings_card_le (J : WeightedGraph V) (hJ : Unweighted J)
    {C : Finset V} (P : Finpartition C) {D n b : ℕ}
    (hD : 0 < D) (hn : 1 ≤ n) (hCn : C.card ≤ n) (hbn : b ≤ n)
    (hconn : ∀ U ∈ P.parts, InternallyConnected J ((D : ℝ) / 8) U)
    (hparts : (P.parts.card : ℝ) ≤ 4 * (C.card : ℝ) / (D : ℝ)) :
    (coreLabelings J C b).card ≤ (2 * n) ^ countExponent C.card b D := by
  letI : DecidableEq P.parts := fun U W => Classical.propDecidable (U = W)
  have hbase : 1 ≤ 2 * n := by omega
  have hbudget : b + 1 ≤ 2 * n := by omega
  have hτ : (0 : ℝ) < (D : ℝ) / 8 := by positivity
  let F : P.parts → ℕ → Finset (Finset V) := fun U a => localLabelings J U.val a
  let T : Finset (P.parts → Finset V) :=
    (budgetVectors P.parts b).biUnion (fun a => Fintype.piFinset (fun U => F U (a U)))
  have hencode : (coreLabelings J C b).card ≤ T.card := by
    apply card_le_card_of_injOn (fun (S : Finset V) (U : P.parts) => S ∩ U.val)
    · intro S hS
      have hs := (mem_coreLabelings J C S b).mp hS
      let a : P.parts → ℕ := fun U => internalBudget J U.val S
      have ha : a ∈ budgetVectors P.parts b :=
        (mem_budgetVectors b a).mpr (sum_internalBudget_le J hJ P S hs.2)
      apply mem_biUnion.mpr
      refine ⟨a, ha, Fintype.mem_piFinset.mpr ?_⟩
      intro U
      apply (mem_localLabelings J U.val (S ∩ U.val) (a U)).mpr
      refine ⟨inter_subset_right, ?_⟩
      change J.localCut U.val (S ∩ U.val) ≤ (internalBudget J U.val S : ℝ)
      rw [J.localCut_inter, internalBudget_cast J hJ]
    · intro S hS T hT he
      exact blockTrace_injective P ((mem_coreLabelings J C S b).mp hS).1
        ((mem_coreLabelings J C T b).mp hT).1 he
  apply hencode.trans
  dsimp only [T]
  apply jointFamilies_card_le F (fun _ a => localExponent ((D : ℝ) / 8) a)
    b (2 * n) (countExponent C.card b D) hbase hbudget
  · intro U a
    apply localLabelings_card_le J U.val hτ (hconn U.val U.property)
      (P.nonempty_of_mem_parts U.property)
      ((card_le_card (P.subset U.property)).trans hCn) a
  · exact jointExponent_le P hD hparts

end
end CutQueryComplexity.CanonicalST.Counting

#print axioms CutQueryComplexity.CanonicalST.Counting.jointFamilies_card_le
#print axioms CutQueryComplexity.CanonicalST.Counting.internalBudget_cast
#print axioms CutQueryComplexity.CanonicalST.Counting.sum_internalBudget_le
#print axioms CutQueryComplexity.CanonicalST.Counting.blockTrace_injective
#print axioms CutQueryComplexity.CanonicalST.Counting.jointExponent_le
#print axioms CutQueryComplexity.CanonicalST.Counting.partitionLabelings_card_le
