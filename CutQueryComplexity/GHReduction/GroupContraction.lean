import CutQueryComplexity.GHReduction.Isolating

/-! # Isolating disjoint terminal groups by an actual compact contraction

Each nonempty terminal group becomes one vertex, and every vertex outside all
groups retains its own label. The ordinary isolating program runs on that exact
quotient; returned shores are pulled back to the original graph. Group selection
and all label maps depend only on public sets.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical BigOperators
open WeightedGraph

variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

def groupUnion (U : I → Finset V) : Finset V := Finset.univ.biUnion U

abbrev GroupVertex (U : I → Finset V) := I ⊕ {v : V // v ∉ groupUnion U}

def groupChoice (U : I → Finset V) (v : V) (hv : v ∈ groupUnion U) : I :=
  Classical.choose (show ∃ i, v ∈ U i from by
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hv
    exact ⟨i, hi⟩)

theorem groupChoice_mem (U : I → Finset V) (v : V) (hv : v ∈ groupUnion U) :
    v ∈ U (groupChoice U v hv) :=
  Classical.choose_spec (show ∃ i, v ∈ U i from by
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hv
    exact ⟨i, hi⟩)

def groupMap (U : I → Finset V) (v : V) : GroupVertex U :=
  if hv : v ∈ groupUnion U then Sum.inl (groupChoice U v hv) else Sum.inr ⟨v, hv⟩

theorem mem_groupUnion (U : I → Finset V) (i : I) {v : V} (hv : v ∈ U i) :
    v ∈ groupUnion U := Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hv⟩

theorem groupMap_inl (U : I → Finset V) (hU : Pairwise (fun i j => Disjoint (U i) (U j)))
    (i : I) {v : V} (hv : v ∈ U i) : groupMap U v = Sum.inl i := by
  have hu := mem_groupUnion U i hv
  have hi : groupChoice U v hu = i := by
    by_contra hne
    exact Finset.disjoint_left.mp (hU hne) (groupChoice_mem U v hu) hv
  simp [groupMap, hu, hi]

theorem groupMap_surjective (U : I → Finset V)
    (hU : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hne : ∀ i, (U i).Nonempty) : Function.Surjective (groupMap U) := by
  rintro (i | ⟨v, hv⟩)
  · obtain ⟨v, hv⟩ := hne i
    exact ⟨v, groupMap_inl U hU i hv⟩
  · exact ⟨v, by simp [groupMap, hv]⟩

theorem groupVertex_card_le (U : I → Finset V)
    (hU : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hne : ∀ i, (U i).Nonempty) : Fintype.card (GroupVertex U) ≤ Fintype.card V :=
  Fintype.card_le_of_surjective _ (groupMap_surjective U hU hne)

def groupTerminals (U : I → Finset V) : Finset (GroupVertex U) :=
  Finset.univ.image Sum.inl

@[simp] theorem inl_mem_groupTerminals (U : I → Finset V) (i : I) :
    Sum.inl i ∈ groupTerminals U := by simp [groupTerminals]

@[simp] theorem inr_not_mem_groupTerminals (U : I → Finset V)
    (v : {v : V // v ∉ groupUnion U}) : Sum.inr v ∉ groupTerminals U := by
  simp [groupTerminals]

@[simp] theorem groupTerminals_card (U : I → Finset V) :
    (groupTerminals U).card = Fintype.card I := by
  rw [groupTerminals, Finset.card_image_of_injective _ Sum.inl_injective]
  exact Finset.card_univ

def groupPush (U : I → Finset V) (i : I) (S : Finset V) : Finset (GroupVertex U) :=
  Finset.univ.filter (fun w => match w with | Sum.inl j => j = i | Sum.inr v => v.val ∈ S)

theorem groupPush_trace (U : I → Finset V) (i : I) (S : Finset V) :
    groupPush U i S ∩ groupTerminals U = {Sum.inl i} := by
  ext w
  cases w <;> simp [groupPush]

theorem groupPull_trace (U : I → Finset V)
    (hU : Pairwise (fun i j => Disjoint (U i) (U j)))
    (i : I) {X : Finset (GroupVertex U)}
    (hX : X ∩ groupTerminals U = {Sum.inl i}) :
    pull (groupMap U) X ∩ groupUnion U = U i := by
  have hmem : ∀ j, Sum.inl j ∈ X ↔ j = i := by
    intro j
    have h : Sum.inl j ∈ X ∩ groupTerminals U ↔ Sum.inl j ∈ ({Sum.inl i} : Finset (GroupVertex U)) := by
      rw [hX]
    simpa using h
  ext v
  constructor
  · intro hv
    obtain ⟨hvX, hvU⟩ := Finset.mem_inter.mp hv
    obtain ⟨j, _, hvj⟩ := Finset.mem_biUnion.mp hvU
    have hmap : groupMap U v ∈ X := (mem_pull _ _ _).mp hvX
    rw [groupMap_inl U hU j hvj] at hmap
    simpa only [(hmem j).mp hmap] using hvj
  · intro hv
    refine Finset.mem_inter.mpr ⟨?_, mem_groupUnion U i hv⟩
    apply (mem_pull _ _ _).mpr
    rw [groupMap_inl U hU i hv]
    exact (hmem i).mpr rfl

theorem pull_groupPush (U : I → Finset V)
    (hU : Pairwise (fun i j => Disjoint (U i) (U j)))
    (i : I) {S : Finset V} (hS : S ∩ groupUnion U = U i) :
    pull (groupMap U) (groupPush U i S) = S := by
  ext v
  by_cases hvU : v ∈ groupUnion U
  · obtain ⟨j, _, hvj⟩ := Finset.mem_biUnion.mp hvU
    have hji : v ∈ S ↔ j = i := by
      constructor
      · intro hvS
        have hvi : v ∈ U i := by rw [← hS]; exact Finset.mem_inter.mpr ⟨hvS, hvU⟩
        by_contra hne
        exact Finset.disjoint_left.mp (hU hne) hvj hvi
      · rintro rfl
        have : v ∈ S ∩ groupUnion U := by rw [hS]; exact hvj
        exact (Finset.mem_inter.mp this).1
    simp only [mem_pull, groupMap_inl U hU j hvj, groupPush, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact hji.symm
  · simp [groupMap, groupPush, hvU]

theorem canonical_groupPull (G : WeightedGraph V) (U : I → Finset V)
    (hU : Pairwise (fun i j => Disjoint (U i) (U j))) (i : I)
    {X : Finset (GroupVertex U)}
    (hX : IsCanonicalTraceCut (G.contract (groupMap U)) (groupTerminals U) {Sum.inl i} X) :
    IsCanonicalTraceCut G (groupUnion U) (U i) (pull (groupMap U) X) := by
  have htrace := groupPull_trace U hU i hX.1.1
  have hmin : IsMinTraceCut G (groupUnion U) (U i) (pull (groupMap U) X) := by
    refine ⟨htrace, fun S hS => ?_⟩
    have h := hX.1.2 (groupPush U i S) (groupPush_trace U i S)
    simpa only [cut_contract, pull_groupPush U hU i hS] using h
  refine ⟨hmin, fun S hS => ?_⟩
  have hpush : IsMinTraceCut (G.contract (groupMap U)) (groupTerminals U) {Sum.inl i}
      (groupPush U i S) := by
    refine ⟨groupPush_trace U i S, fun Y hY => ?_⟩
    have h := hS.2 (pull (groupMap U) Y) (groupPull_trace U hU i hY)
    simpa only [cut_contract, pull_groupPush U hU i hS.1] using h
  have hs := hX.2 (groupPush U i S) hpush
  have hpull : pull (groupMap U) X ⊆ pull (groupMap U) (groupPush U i S) := by
    intro v hv
    exact (mem_pull _ _ _).mpr (hs ((mem_pull _ _ _).mp hv))
  rwa [pull_groupPush U hU i hS.1] at hpull

def groupIsolatingProgram {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (U : I → Finset V) : Prog (Finset V) ℝ (I → Finset V) :=
  (queryMap (pull (groupMap U)) (isolatingProgram family (groupTerminals U))).map
    (fun output i => pull (groupMap U) (output ⟨Sum.inl i, inl_mem_groupTerminals U i⟩))

theorem groupIsolatingProgram_correct {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (hG : InputPromise M G) (U : I → Finset V)
    (hU : Pairwise (fun i j => Disjoint (U i) (U j))) (hI : 2 ≤ Fintype.card I)
    (i : I) :
    IsCanonicalTraceCut G (groupUnion U) (U i)
      (Prog.eval G.cut (groupIsolatingProgram family U) i) := by
  have hread : G.cut ∘ pull (groupMap U) = (G.contract (groupMap U)).cut := by
    funext S
    exact (cut_contract G _ S).symm
  simp only [groupIsolatingProgram, Prog.eval_map, queryMap_eval, hread]
  apply canonical_groupPull G U hU i
  exact isolatingProgram_correct family _
    ⟨integral_contract G hG.1 _, (edgeMass_contract_le G _).trans hG.2⟩ _
    (by simpa only [groupTerminals_card] using hI) _

/-- Costs are measured against the original public size and original capacity
parameter even when the group quotient is strictly smaller. -/
theorem groupIsolatingProgram_cost_scaled {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (U : I → Finset V)
    (hU : Pairwise (fun i j => Disjoint (U i) (U j))) (hne : ∀ i, (U i).Nonempty)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) (read : Finset V → ℝ) :
    n * Prog.cost read (groupIsolatingProgram family U) ≤
      ((Nat.clog 2 (Fintype.card I) + 2) * Fintype.card V) * Q n := by
  have hsize := groupVertex_card_le U hU hne
  rw [groupIsolatingProgram, Prog.cost_map, queryMap_cost]
  have h := isolatingProgram_cost_scaled family (groupTerminals U) (hsize.trans hvn) hQ
    (read ∘ pull (groupMap U))
  rw [groupTerminals_card] at h
  exact h.trans (Nat.mul_le_mul_right (Q n) (Nat.mul_le_mul_left _ hsize))

end
end CutQueryComplexity.GHReduction
