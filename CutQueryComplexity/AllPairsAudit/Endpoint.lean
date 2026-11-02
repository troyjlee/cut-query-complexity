import CutQueryComplexity.AllPairsAudit.MinimalShore
import CutQueryComplexity.AllPairsAudit.Star

/-!
# Deterministic all-pairs structural endpoint

`PreservesFriendly` is the explicit input contract for an externally constructed
friendly-cut partition. It asserts only that small friendly cuts do not split
blocks. It does not assume preservation of terminal minima or the star theorem.
This file proves those consequences. No randomized construction, query bound,
low-degree preprocessing, Gomory-Hu reduction, or Appendix A result is assumed
or proved here.
-/

set_option autoImplicit false

namespace CutQueryComplexity.AllPairsAudit

open WeightedGraph
noncomputable section
open scoped Classical
variable {V B : Type*} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]

/-- The only external sparsifier property used by the structural endpoint. -/
def PreservesFriendly (G : WeightedGraph V) (p : V → B) : Prop :=
  ∀ S, Friendly G S → G.cut S ≤ 2 * Fintype.card V → Respects p S

@[simp] theorem originalShore_compl (A : Finset (V ⊕ B)) :
    originalShore Aᶜ = (originalShore A)ᶜ := by ext; simp

/-- Every original terminal pair has an optimal shore admitting an exact star lift. -/
theorem exists_exact_minimum_lift {G : WeightedGraph V} (hG : Unweighted G)
    (hdeg : ∀ v, 2 ≤ G.degree v) (p : V → B) (hp : PreservesFriendly G p)
    {s t : V} (hst : s ≠ t) :
    ∃ S A, IsSTMinCut G s t S ∧ originalShore A = S ∧ (star G p).cut A = G.cut S := by
  obtain ⟨r, q, S, horient, hS, hshape⟩ := exists_structured_minimum hG hdeg hst
  have hexact : ∃ A, originalShore A = S ∧ (star G p).cut A = G.cut S := by
    rcases hshape with ⟨hf, hb⟩ | ⟨hf, hb⟩
    · exact ⟨lift p S, originalShore_lift p S, star_cut_lift G p (hp S hf hb)⟩
    · refine ⟨insert (Sum.inl r) (lift p (S.erase r)), ?_, ?_⟩
      · simp [hS.1]
      · simpa [Finset.insert_erase hS.1] using
          star_cut_lift_insert G p (hp _ hf hb) (Finset.notMem_erase r S)
  obtain ⟨A, hAS, hcut⟩ := hexact
  rcases horient with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨S, A, hS, hAS, hcut⟩
  · exact ⟨Sᶜ, Aᶜ, st_compl G hS, by simp [hAS], by simpa using hcut⟩

/-- The star graph has a minimum cut with exactly the original optimum value. -/
theorem exists_star_minimum {G : WeightedGraph V} (hG : Unweighted G)
    (hdeg : ∀ v, 2 ≤ G.degree v) (p : V → B) (hp : PreservesFriendly G p)
    {s t : V} (hst : s ≠ t) :
    ∃ A, IsSTMinCut (star G p) (Sum.inl s) (Sum.inl t) A ∧
      IsSTMinCut G s t (originalShore A) ∧ (star G p).cut A = G.cut (originalShore A) := by
  obtain ⟨S, A, hS, hAS, hc⟩ := exists_exact_minimum_lift hG hdeg p hp hst
  have hsA : Sum.inl s ∈ A := (mem_originalShore A s).mp (hAS.symm ▸ hS.1)
  have htA : Sum.inl t ∉ A := by
    intro ht
    exact hS.2.1 (hAS ▸ (mem_originalShore A t).mpr ht)
  refine ⟨A, ⟨hsA, htA, ?_⟩, hAS.symm ▸ hS, by simpa [hAS] using hc⟩
  intro T hsT htT
  rw [hc]
  exact (hS.2.2 (originalShore T) (by simpa using hsT) (by simpa using htT)).trans
    (star_cut_dominates G p T)

/-- Any minimum found offline in the explicit star graph restricts to a genuine
minimum in the original graph, with equality of values. -/
theorem star_minimum_extract {G : WeightedGraph V} (hG : Unweighted G)
    (hdeg : ∀ v, 2 ≤ G.degree v) (p : V → B) (hp : PreservesFriendly G p)
    {s t : V} (hst : s ≠ t) {A : Finset (V ⊕ B)}
    (hA : IsSTMinCut (star G p) (Sum.inl s) (Sum.inl t) A) :
    IsSTMinCut G s t (originalShore A) ∧ (star G p).cut A = G.cut (originalShore A) := by
  obtain ⟨S, X, hS, hXS, hX⟩ := exists_exact_minimum_lift hG hdeg p hp hst
  have hsA : s ∈ originalShore A := by simpa using hA.1
  have htA : t ∉ originalShore A := by simpa using hA.2.1
  have hsX : Sum.inl s ∈ X := by
    apply (mem_originalShore X s).mp
    simpa [hXS] using hS.1
  have htX : Sum.inl t ∉ X := by
    intro h
    have := (mem_originalShore X t).mpr h
    exact hS.2.1 (hXS ▸ this)
  have hAX := hA.2.2 X hsX htX
  rw [hX] at hAX
  have hdom := star_cut_dominates G p A
  have hmin := hS.2.2 (originalShore A) hsA htA
  refine ⟨⟨hsA, htA, ?_⟩, by linarith⟩
  intro T hsT htT
  exact hdom.trans (hAX.trans (hS.2.2 T hsT htT))

/-- Terminal-cut values coincide: for any two minimum shores, one in each graph,
their cut values are equal. This is simultaneous for every pair of originals. -/
theorem all_pairs_minimum_values {G : WeightedGraph V} (hG : Unweighted G)
    (hdeg : ∀ v, 2 ≤ G.degree v) (p : V → B) (hp : PreservesFriendly G p)
    {s t : V} (hst : s ≠ t) {S : Finset V} {A : Finset (V ⊕ B)}
    (hS : IsSTMinCut G s t S)
    (hA : IsSTMinCut (star G p) (Sum.inl s) (Sum.inl t) A) :
    (star G p).cut A = G.cut S := by
  obtain ⟨hr, he⟩ := star_minimum_extract hG hdeg p hp hst hA
  rw [he]
  exact le_antisymm (hr.2.2 S hS.1 hS.2.1) (hS.2.2 _ hr.1 hr.2.1)

omit [Fintype B] [DecidableEq B] [Fintype V] [DecidableEq V] in
theorem simpleGraph_unweighted (F : _root_.SimpleGraph V) :
    Unweighted (SimpleGraph.toWeighted F) := by
  intro u v
  rw [SimpleGraph.toWeighted_w]
  by_cases h : F.Adj u v <;> simp [h]

omit [Fintype B] [DecidableEq B] [DecidableEq V] in
theorem simpleGraph_degree (F : _root_.SimpleGraph V) (v : V) :
    (SimpleGraph.toWeighted F).degree v = (F.degree v : ℝ) := by
  simp only [WeightedGraph.degree, SimpleGraph.toWeighted_w]
  rw [← F.card_neighborFinset_eq_degree]
  have he : F.neighborFinset v = Finset.univ.filter (F.Adj v) := by ext; simp
  rw [he, Finset.card_filter]
  push_cast
  rfl

/-- The endpoint specialized to an actual finite simple graph with natural degrees. -/
theorem star_minimum_extract_simple (F : _root_.SimpleGraph V)
    (hdeg : ∀ v, 2 ≤ F.degree v) (p : V → B)
    (hp : PreservesFriendly (SimpleGraph.toWeighted F) p)
    {s t : V} (hst : s ≠ t) {A : Finset (V ⊕ B)}
    (hA : IsSTMinCut (star (SimpleGraph.toWeighted F) p) (Sum.inl s) (Sum.inl t) A) :
    IsSTMinCut (SimpleGraph.toWeighted F) s t (originalShore A) ∧
      (star (SimpleGraph.toWeighted F) p).cut A =
        (SimpleGraph.toWeighted F).cut (originalShore A) := by
  apply star_minimum_extract (simpleGraph_unweighted F) _ p hp hst hA
  intro v
  rw [simpleGraph_degree]
  exact_mod_cast hdeg v

end
end CutQueryComplexity.AllPairsAudit
