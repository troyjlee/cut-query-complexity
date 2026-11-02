import CutQueryComplexity.Problem.Basic
import CutQueryComplexity.Certificate.SplittingOff

/-! # Canonical source shores and source-switching algebra

All minimization on `G` below occurs in semantic definitions and existence
proofs, never inside an oracle program. Program implementations must use the
supplied public s-t family.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical
open WeightedGraph

variable {V : Type} [Fintype V] [DecidableEq V]

def stShores (s t : V) : Finset (Finset V) :=
  Finset.univ.filter (fun S => s ∈ S ∧ t ∉ S)

@[simp] theorem mem_stShores (s t : V) (S : Finset V) :
    S ∈ stShores s t ↔ s ∈ S ∧ t ∉ S := by simp [stShores]

theorem stShores_nonempty {s t : V} (hst : s ≠ t) : (stShores s t).Nonempty :=
  ⟨{s}, by simp [Ne.symm hst]⟩

def stValue (G : WeightedGraph V) (s t : V) : ℝ :=
  if h : (stShores s t).Nonempty then (stShores s t).inf' h G.cut else 0

theorem stValue_nonneg (G : WeightedGraph V) (s t : V) : 0 ≤ stValue G s t := by
  unfold stValue
  split
  · exact Finset.le_inf' _ _ (fun S _ => G.cut_nonneg S)
  · exact le_rfl

theorem stValue_le (G : WeightedGraph V) {s t : V} {S : Finset V}
    (hs : s ∈ S) (ht : t ∉ S) : stValue G s t ≤ G.cut S := by
  have hm := (mem_stShores s t S).mpr ⟨hs, ht⟩
  rw [stValue, dite_eq_left ⟨S, hm⟩]
  exact Finset.inf'_le _ hm

theorem exists_stMinCut (G : WeightedGraph V) {s t : V} (hst : s ≠ t) :
    ∃ S, IsSTMinCut G s t S ∧ G.cut S = stValue G s t := by
  have hne := stShores_nonempty hst
  obtain ⟨S, hS, hval⟩ := Finset.exists_mem_eq_inf' hne G.cut
  obtain ⟨hs, ht⟩ := (mem_stShores s t S).mp hS
  refine ⟨S, ⟨hs, ht, fun T hsT htT => ?_⟩, ?_⟩
  · rw [← hval]
    exact Finset.inf'_le _ ((mem_stShores s t T).mpr ⟨hsT, htT⟩)
  · rw [stValue, dite_eq_left hne, hval]

theorem stValue_eq_of_minCut (G : WeightedGraph V) {s t : V} {S : Finset V}
    (hS : IsSTMinCut G s t S) : G.cut S = stValue G s t := by
  have hst : s ≠ t := fun h => hS.2.1 (h ▸ hS.1)
  obtain ⟨T, hT, hval⟩ := exists_stMinCut G hst
  exact le_antisymm (hval ▸ hS.2.2 T hT.1 hT.2.1) (stValue_le G hS.1 hS.2.1)

theorem stMinCut_compl (G : WeightedGraph V) {s t : V} {S : Finset V}
    (hS : IsSTMinCut G s t S) : IsSTMinCut G t s Sᶜ := by
  refine ⟨by simpa using hS.2.1, by simpa using hS.1, fun T htT hsT => ?_⟩
  have h := hS.2.2 Tᶜ (by simpa using hsT) (by simpa using htT)
  simpa only [cut_compl] using h

theorem stMinCut_inter (G : WeightedGraph V) {s t : V} {S T : Finset V}
    (hS : IsSTMinCut G s t S) (hT : IsSTMinCut G s t T) :
    IsSTMinCut G s t (S ∩ T) := by
  have hs : s ∈ S ∩ T := Finset.mem_inter.mpr ⟨hS.1, hT.1⟩
  have ht : t ∉ S ∩ T := fun h => hS.2.1 (Finset.mem_inter.mp h).1
  have hsub := G.cut_submodular S T
  have hUnion := hT.2.2 (S ∪ T) (Finset.mem_union_left _ hS.1)
    (by simpa using And.intro hS.2.1 hT.2.1)
  have hle : G.cut (S ∩ T) ≤ G.cut S := by linarith
  exact ⟨hs, ht, fun A hsA htA => hle.trans (hS.2.2 A hsA htA)⟩

/-- The first terminal always lies inside the canonical shore. -/
def IsCanonicalSTCut (G : WeightedGraph V) (s t : V) (S : Finset V) : Prop :=
  IsSTMinCut G s t S ∧ ∀ T, IsSTMinCut G s t T → S ⊆ T

theorem exists_canonicalSTCut (G : WeightedGraph V) {s t : V} (hst : s ≠ t) :
    ∃ S, IsCanonicalSTCut G s t S := by
  obtain ⟨S0, hS0, _⟩ := exists_stMinCut G hst
  let M := Finset.univ.filter (fun S => IsSTMinCut G s t S)
  have hM : M.Nonempty := ⟨S0, by simp [M, hS0]⟩
  obtain ⟨S, hS, hcard⟩ := Finset.exists_min_image M Finset.card hM
  have hmin : IsSTMinCut G s t S := (Finset.mem_filter.mp hS).2
  refine ⟨S, hmin, fun T hT => ?_⟩
  have hInt := stMinCut_inter G hmin hT
  have hc := hcard (S ∩ T) (by simp [M, hInt])
  have he : S ∩ T = S := Finset.eq_of_subset_of_card_le Finset.inter_subset_left hc
  rw [← he]
  exact Finset.inter_subset_right

theorem canonicalSTCut_unique (G : WeightedGraph V) {s t : V} {S T : Finset V}
    (hS : IsCanonicalSTCut G s t S) (hT : IsCanonicalSTCut G s t T) : S = T :=
  Finset.Subset.antisymm (hS.2 T hT.1) (hT.2 S hS.1)

/-- Minimum shore with a specified terminal trace, oriented to that trace. -/
def IsMinTraceCut (G : WeightedGraph V) (R A S : Finset V) : Prop :=
  S ∩ R = A ∧ ∀ T, T ∩ R = A → G.cut S ≤ G.cut T

def IsCanonicalTraceCut (G : WeightedGraph V) (R A S : Finset V) : Prop :=
  IsMinTraceCut G R A S ∧ ∀ T, IsMinTraceCut G R A T → S ⊆ T

/-- Nested terminal traces admit nested optimum shores by actual submodularity. -/
theorem trace_uncross (G : WeightedGraph V) {R A B S T : Finset V}
    (hAB : A ⊆ B) (hS : IsMinTraceCut G R A S) (hT : IsMinTraceCut G R B T) :
    IsMinTraceCut G R A (S ∩ T) := by
  have hInt : (S ∩ T) ∩ R = A := by
    calc
      _ = (S ∩ R) ∩ (T ∩ R) := by ext; simp [and_assoc, and_left_comm, and_comm]
      _ = A := by rw [hS.1, hT.1, Finset.inter_eq_left.mpr hAB]
  have hUnion : (S ∪ T) ∩ R = B := by
    rw [Finset.union_inter_distrib_right, hS.1, hT.1, Finset.union_eq_right.mpr hAB]
  have hsub := G.cut_submodular S T
  have hlow := hT.2 (S ∪ T) hUnion
  have hle : G.cut (S ∩ T) ≤ G.cut S := by linarith
  exact ⟨hInt, fun X hX => hle.trans (hS.2 X hX)⟩

theorem exists_canonicalTraceCut (G : WeightedGraph V) {R A : Finset V}
    (hAR : A ⊆ R) : ∃ S, IsCanonicalTraceCut G R A S := by
  let F := Finset.univ.filter (fun S : Finset V => S ∩ R = A)
  have hF : F.Nonempty := ⟨A, by simp [F, Finset.inter_eq_left.mpr hAR]⟩
  obtain ⟨S0, hS0, hopt⟩ := Finset.exists_min_image F G.cut hF
  have hmin0 : IsMinTraceCut G R A S0 :=
    ⟨(Finset.mem_filter.mp hS0).2, fun T hT => hopt T (by simp [F, hT])⟩
  let K := Finset.univ.filter (fun S => IsMinTraceCut G R A S)
  have hK : K.Nonempty := ⟨S0, by simp [K, hmin0]⟩
  obtain ⟨S, hS, hcard⟩ := Finset.exists_min_image K Finset.card hK
  have hmin : IsMinTraceCut G R A S := (Finset.mem_filter.mp hS).2
  refine ⟨S, hmin, fun T hT => ?_⟩
  have hInt := trace_uncross G (Finset.Subset.refl A) hmin hT
  have hc := hcard (S ∩ T) (by simp [K, hInt])
  have he : S ∩ T = S := Finset.eq_of_subset_of_card_le Finset.inter_subset_left hc
  rw [← he]
  exact Finset.inter_subset_right

theorem canonical_trace_subset (G : WeightedGraph V) {R A B S T : Finset V}
    (hAB : A ⊆ B) (hS : IsCanonicalTraceCut G R A S)
    (hT : IsMinTraceCut G R B T) : S ⊆ T :=
  (hS.2 (S ∩ T) (trace_uncross G hAB hS.1 hT)).trans Finset.inter_subset_right

theorem canonical_trace_unique (G : WeightedGraph V) {R A S T : Finset V}
    (hS : IsCanonicalTraceCut G R A S) (hT : IsCanonicalTraceCut G R A T) : S = T :=
  Finset.Subset.antisymm (hS.2 _ hT.1) (hT.2 _ hS.1)

theorem minTrace_compl (G : WeightedGraph V) {R A S : Finset V}
    (hS : IsMinTraceCut G R A S) : IsMinTraceCut G R (R \ A) Sᶜ := by
  have hcomp : Sᶜ ∩ R = R \ A := by
    rw [← hS.1]
    ext v
    simp only [Finset.mem_inter, Finset.mem_compl, Finset.mem_sdiff]
    tauto
  refine ⟨hcomp, fun T hT => ?_⟩
  have hAR : A ⊆ R := hS.1 ▸ Finset.inter_subset_right
  have hback : Tᶜ ∩ R = A := by
    ext v
    have ht : v ∈ T ∩ R ↔ v ∈ R \ A := by rw [hT]
    have har : v ∈ A → v ∈ R := fun hv => hAR hv
    simp only [Finset.mem_inter, Finset.mem_compl, Finset.mem_sdiff] at ht ⊢
    tauto
  have h := hS.2 Tᶜ hback
  simpa only [cut_compl] using h

/-- Canonical isolating shores of disjoint terminal groups are disjoint. -/
theorem canonical_trace_disjoint (G : WeightedGraph V) {R A B S T : Finset V}
    (hAB : Disjoint A B) (hS : IsCanonicalTraceCut G R A S)
    (hT : IsCanonicalTraceCut G R B T) : Disjoint S T := by
  have hdiffS : (S \ T) ∩ R = A := by
    calc
      _ = (S ∩ R) \ (T ∩ R) := by ext; simp; tauto
      _ = A := by rw [hS.1.1, hT.1.1, Finset.sdiff_eq_self_of_disjoint hAB]
  have hdiffT : (T \ S) ∩ R = B := by
    calc
      _ = (T ∩ R) \ (S ∩ R) := by ext; simp; tauto
      _ = B := by rw [hT.1.1, hS.1.1, Finset.sdiff_eq_self_of_disjoint hAB.symm]
  have hposi := Certificate.cut_posimodular_eq G S T
  have hnonneg := G.cross_nonneg (S ∩ T) (S ∪ T)ᶜ
  have hlow := hT.1.2 (T \ S) hdiffT
  have hle : G.cut (S \ T) ≤ G.cut S := by linarith
  have hmin : IsMinTraceCut G R A (S \ T) :=
    ⟨hdiffS, fun X hX => hle.trans (hS.1.2 X hX)⟩
  have hsub := hS.2 (S \ T) hmin
  exact Finset.disjoint_left.mpr (fun v hvS hvT => (Finset.mem_sdiff.mp (hsub hvS)).2 hvT)

/-- The ultrametric inequality behind the source-switching branch. -/
theorem stValue_triangle (G : WeightedGraph V) (s a t : V) (hat : a ≠ t) :
    min (stValue G s a) (stValue G s t) ≤ stValue G a t := by
  obtain ⟨S, hS, hval⟩ := exists_stMinCut G hat
  by_cases hs : s ∈ S
  · exact (min_le_right _ _).trans ((stValue_le G hs hS.2.1).trans_eq hval)
  · have hle := stValue_le G (S := Sᶜ) (by simpa using hs) (by simpa using hS.1)
    rw [cut_compl] at hle
    exact (min_le_left _ _).trans (hle.trans_eq hval)

/-- A source with strictly larger old-source connectivity has the same
connectivity to the target. This justifies the actual source switch. -/
theorem stValue_source_switch (G : WeightedGraph V) {s a t : V} (hst : s ≠ t)
    (hat : a ≠ t) (hlt : stValue G s t < stValue G s a) :
    stValue G a t = stValue G s t := by
  obtain ⟨S, hS, hval⟩ := exists_stMinCut G hst
  have ha : a ∈ S := by
    by_contra h
    have hle := stValue_le G hS.1 h
    rw [hval] at hle
    exact (not_lt_of_ge hle) hlt
  have hupper := (stValue_le G ha hS.2.1).trans_eq hval
  have hlower := stValue_triangle G s a t hat
  rw [min_eq_right hlt.le] at hlower
  exact le_antisymm hupper hlower

end
end CutQueryComplexity.GHReduction
