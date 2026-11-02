import CutQueryComplexity.GHReduction.Isolating

/-! # Canonical-shore facts used by sampled threshold classification

These are graph-theoretic implications for the actual canonical outputs. In
particular, a sampled isolating call recovers an original source cut whenever
its target is the only sampled terminal on that source cut's canonical side.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical
open WeightedGraph

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A canonical shore is contained in every other source shore which is itself
minimum for a terminal it contains. -/
theorem canonicalST_subset_of_mem (G : WeightedGraph V) {s u v : V} {S T : Finset V}
    (hS : IsCanonicalSTCut G u s S) (hT : IsSTMinCut G v s T) (huT : u ∈ T) : S ⊆ T := by
  have huInt : u ∈ S ∩ T := Finset.mem_inter.mpr ⟨hS.1.1, huT⟩
  have hsInt : s ∉ S ∩ T := fun h => hS.1.2.1 (Finset.mem_inter.mp h).1
  have hUnion := hT.2.2 (S ∪ T) (Finset.mem_union_right _ hT.1)
    (by simpa using And.intro hS.1.2.1 hT.2.1)
  have hsub := G.cut_submodular S T
  have hle : G.cut (S ∩ T) ≤ G.cut S := by linarith
  have hmin : IsSTMinCut G u s (S ∩ T) :=
    ⟨huInt, hsInt, fun A huA hsA => hle.trans (hS.1.2.2 A huA hsA)⟩
  exact (hS.2 _ hmin).trans Finset.inter_subset_right

theorem canonicalST_disjoint_of_targets_outside (G : WeightedGraph V)
    {s u v : V} {S T : Finset V}
    (hS : IsCanonicalSTCut G u s S) (hT : IsCanonicalSTCut G v s T)
    (huT : u ∉ T) (hvS : v ∉ S) : Disjoint S T := by
  have huDiff : u ∈ S \ T := Finset.mem_sdiff.mpr ⟨hS.1.1, huT⟩
  have hvDiff : v ∈ T \ S := Finset.mem_sdiff.mpr ⟨hT.1.1, hvS⟩
  have hsDiff : s ∉ S \ T := fun h => hS.1.2.1 (Finset.mem_sdiff.mp h).1
  have hsDiff' : s ∉ T \ S := fun h => hT.1.2.1 (Finset.mem_sdiff.mp h).1
  have hlow := hT.1.2.2 (T \ S) hvDiff hsDiff'
  have hposi := Certificate.cut_posimodular_eq G S T
  have hnonneg := G.cross_nonneg (S ∩ T) (S ∪ T)ᶜ
  have hle : G.cut (S \ T) ≤ G.cut S := by linarith
  have hmin : IsSTMinCut G u s (S \ T) :=
    ⟨huDiff, hsDiff, fun A huA hsA => hle.trans (hS.1.2.2 A huA hsA)⟩
  have hsub := hS.2 _ hmin
  exact Finset.disjoint_left.mpr (fun x hxS hxT => (Finset.mem_sdiff.mp (hsub hxS)).2 hxT)

theorem canonicalST_laminar (G : WeightedGraph V) {s u v : V} {S T : Finset V}
    (hS : IsCanonicalSTCut G u s S) (hT : IsCanonicalSTCut G v s T) :
    S ⊆ T ∨ T ⊆ S ∨ Disjoint S T := by
  by_cases huT : u ∈ T
  · exact Or.inl (canonicalST_subset_of_mem G hS hT.1 huT)
  · by_cases hvS : v ∈ S
    · exact Or.inr (Or.inl (canonicalST_subset_of_mem G hT hS.1 hvS))
    · exact Or.inr (Or.inr (canonicalST_disjoint_of_targets_outside G hS hT huT hvS))

/-- This equality, rather than just a value inequality, is the useful event in
the sampled isolating-cut argument. -/
theorem canonicalIso_eq_pair (G : WeightedGraph V) {R C S : Finset V} {s v : V}
    (hsR : s ∈ R) (hvs : v ≠ s) (hC : IsCanonicalSTCut G v s C)
    (htrace : C ∩ R = {v}) (hS : IsCanonicalTraceCut G R {v} S) : S = C := by
  have hvS : v ∈ S := by
    have : v ∈ S ∩ R := by rw [hS.1.1]; simp
    exact (Finset.mem_inter.mp this).1
  have hsS : s ∉ S := by
    intro hs
    have : s ∈ S ∩ R := Finset.mem_inter.mpr ⟨hs, hsR⟩
    rw [hS.1.1, Finset.mem_singleton] at this
    exact hvs this.symm
  have hle := hS.1.2 C htrace
  have hminS : IsSTMinCut G v s S :=
    ⟨hvS, hsS, fun A hvA hsA => hle.trans (hC.1.2.2 A hvA hsA)⟩
  have hminC : IsMinTraceCut G R {v} C := by
    refine ⟨htrace, fun A hA => ?_⟩
    have hvA : v ∈ A := by
      have : v ∈ A ∩ R := by rw [hA]; simp
      exact (Finset.mem_inter.mp this).1
    have hsA : s ∉ A := by
      intro hs
      have : s ∈ A ∩ R := Finset.mem_inter.mpr ⟨hs, hsR⟩
      rw [hA, Finset.mem_singleton] at this
      exact hvs this.symm
    exact hC.1.2.2 A hvA hsA
  exact Finset.Subset.antisymm (hS.2 C hminC) (hC.2 S hminS)

/-- Every vertex covered by an accepted isolating shore is below the threshold.
This is unconditional on the success of the random sampling scheme. -/
theorem accepted_shore_sound (G : WeightedGraph V) {S : Finset V} {s v : V} {W : ℝ}
    (hs : s ∉ S) (hv : v ∈ S) (hvalue : G.cut S ≤ W) : stValue G v s ≤ W :=
  (stValue_le G hv hs).trans hvalue

theorem canonical_hit_covers (G : WeightedGraph V) {R C S U : Finset V} {s v : V} {W : ℝ}
    (hsR : s ∈ R) (hvs : v ≠ s) (hC : IsCanonicalSTCut G v s C)
    (htrace : C ∩ R = {v}) (hS : IsCanonicalTraceCut G R {v} S)
    (hvalue : stValue G v s ≤ W) :
    G.cut S ≤ W ∧ C ∩ U ⊆ S ∩ U := by
  rw [canonicalIso_eq_pair G hsR hvs hC htrace hS]
  exact ⟨(stValue_eq_of_minCut G hC.1).trans_le hvalue, Finset.Subset.refl _⟩

end
end CutQueryComplexity.GHReduction
