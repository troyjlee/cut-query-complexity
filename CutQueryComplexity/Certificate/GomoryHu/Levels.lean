import CutQueryComplexity.Certificate.GomoryHu.Decomposition
import CutQueryComplexity.Certificate.GomoryHu.TerminalLower

set_option autoImplicit false

/-! # Simultaneous certificates organized by actual positive tree-weight levels

The level components are explicitly the equivalence classes of all fundamental
shores of smaller weight. Their boundary edges are proved smaller, and their
terminal lower bounds follow from the tree-path theorem. Quotient certificates
are chosen before every unrestricted competitor. Zero-weight edges are handled
only by their queried values and nonnegativity.
-/

namespace CutQueryComplexity.Certificate.GomoryHu

open Finset WeightedGraph
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

def LevelRel (T : TwoRespecting.RootedTree V) (tau : V → ℝ) (a : ℝ) (s t : V) : Prop :=
  ∀ e, e ≠ T.root → tau e < a → (s ∈ T.subtree e ↔ t ∈ T.subtree e)

theorem LevelRel.refl (T : TwoRespecting.RootedTree V) (tau : V → ℝ) (a : ℝ) (s : V) :
    LevelRel T tau a s s := fun _ _ _ => Iff.rfl

theorem LevelRel.symm {T : TwoRespecting.RootedTree V} {tau : V → ℝ} {a : ℝ} {s t : V}
    (h : LevelRel T tau a s t) : LevelRel T tau a t s := fun e he ha => (h e he ha).symm

theorem LevelRel.trans {T : TwoRespecting.RootedTree V} {tau : V → ℝ} {a : ℝ} {s t u : V}
    (h₁ : LevelRel T tau a s t) (h₂ : LevelRel T tau a t u) : LevelRel T tau a s u :=
  fun e he ha => (h₁ e he ha).trans (h₂ e he ha)

def levelClass (T : TwoRespecting.RootedTree V) (tau : V → ℝ) (a : ℝ) (s : V) : Finset V :=
  univ.filter (LevelRel T tau a s)

@[simp] theorem mem_levelClass (T : TwoRespecting.RootedTree V) (tau : V → ℝ)
    (a : ℝ) (s t : V) : t ∈ levelClass T tau a s ↔ LevelRel T tau a s t := by
  simp [levelClass]

theorem self_mem_levelClass (T : TwoRespecting.RootedTree V) (tau : V → ℝ) (a : ℝ) (s : V) :
    s ∈ levelClass T tau a s := (mem_levelClass T tau a s s).mpr (LevelRel.refl T tau a s)

theorem levelClass_eq_of_mem {T : TwoRespecting.RootedTree V} {tau : V → ℝ}
    {a : ℝ} {s x : V} (hx : x ∈ levelClass T tau a s) :
    levelClass T tau a x = levelClass T tau a s := by
  have h := (mem_levelClass T tau a s x).mp hx
  ext y
  simp only [mem_levelClass]
  exact ⟨fun hxy => h.trans hxy, fun hsy => h.symm.trans hsy⟩

def levelParts (T : TwoRespecting.RootedTree V) (tau : V → ℝ) (a : ℝ) : Finset (Finset V) :=
  univ.image (levelClass T tau a)

theorem levelParts_nonempty (T : TwoRespecting.RootedTree V) (tau : V → ℝ) (a : ℝ)
    {U : Finset V} (hU : U ∈ levelParts T tau a) : U.Nonempty := by
  obtain ⟨s, _, rfl⟩ := mem_image.mp hU
  exact ⟨s, self_mem_levelClass T tau a s⟩

theorem levelParts_disjoint (T : TwoRespecting.RootedTree V) (tau : V → ℝ) (a : ℝ) :
    (levelParts T tau a : Set (Finset V)).PairwiseDisjoint id := by
  intro U hU W hW hne
  obtain ⟨s, _, rfl⟩ := mem_image.mp hU
  obtain ⟨t, _, rfl⟩ := mem_image.mp hW
  apply disjoint_left.mpr
  intro x hxs hxt
  exact hne ((levelClass_eq_of_mem hxs).symm.trans (levelClass_eq_of_mem hxt))

theorem levelClass_pathClosed (T : TwoRespecting.RootedTree V) (tau : V → ℝ)
    (a : ℝ) (r : V) : PathClosed T (levelClass T tau a r) := by
  intro s hs t ht e he
  have hrs := (mem_levelClass T tau a r s).mp hs
  have hrt := (mem_levelClass T tau a r t).mp ht
  have hboth : ∀ z, z ≠ T.root → tau z < a →
      (r ∈ T.subtree z ↔ e ∈ T.subtree z) ∧
      (r ∈ T.subtree z ↔ T.parent e ∈ T.subtree z) := by
    intro z hz hza
    by_cases hrz : r ∈ T.subtree z
    · have hs' := (hrs z hz hza).mp hrz
      have ht' := (hrt z hz hza).mp hrz
      have h := subtree_pathClosed T z s hs' t ht' e he
      exact ⟨⟨fun _ => h.1, fun _ => hrz⟩, ⟨fun _ => h.2, fun _ => hrz⟩⟩
    · have hs' : s ∈ (T.subtree z)ᶜ := mem_compl.mpr fun h => hrz ((hrs z hz hza).mpr h)
      have ht' : t ∈ (T.subtree z)ᶜ := mem_compl.mpr fun h => hrz ((hrt z hz hza).mpr h)
      have h := compl_subtree_pathClosed T z s hs' t ht' e he
      exact ⟨⟨fun h => (hrz h).elim, fun h' => (mem_compl.mp h.1 h').elim⟩,
        ⟨fun h => (hrz h).elim, fun h' => (mem_compl.mp h.2 h').elim⟩⟩
  exact ⟨(mem_levelClass T tau a r e).mpr (fun z hz hza => (hboth z hz hza).1),
    (mem_levelClass T tau a r (T.parent e)).mpr (fun z hz hza => (hboth z hz hza).2)⟩

theorem levelRel_parent_of_le (T : TwoRespecting.RootedTree V) (tau : V → ℝ)
    {a : ℝ} {e : V} (ha : a ≤ tau e) : LevelRel T tau a e (T.parent e) := by
  intro f hf hfa
  by_contra hcross
  have hef := (crosses_subtree_iff T hf).mp hcross
  rw [hef] at ha
  exact not_lt_of_ge ha hfa

theorem levelParts_boundary_lt (T : TwoRespecting.RootedTree V) (tau : V → ℝ)
    (a : ℝ) {U : Finset V} (hU : U ∈ levelParts T tau a) {e : V}
    (he : e ∈ boundary T U) : tau e < a := by
  obtain ⟨r, _, rfl⟩ := mem_image.mp hU
  by_contra hle
  have hrel := levelRel_parent_of_le T tau (le_of_not_gt hle)
  have hiff : e ∈ levelClass T tau a r ↔ T.parent e ∈ levelClass T tau a r := by
    simp only [mem_levelClass]
    exact ⟨fun h => h.trans hrel, fun h => h.trans hrel.symm⟩
  exact (mem_filter.mp he).2 hiff

theorem levelClass_path_lower (T : TwoRespecting.RootedTree V) (tau : V → ℝ)
    (a : ℝ) {r s t e : V} (hs : s ∈ levelClass T tau a r)
    (ht : t ∈ levelClass T tau a r) (he : e ∈ pathEdges T s t) : a ≤ tau e := by
  have hrel := ((mem_levelClass T tau a r s).mp hs).symm.trans
    ((mem_levelClass T tau a r t).mp ht)
  have hp := (mem_pathEdges T s t e).mp he
  exact le_of_not_gt fun hlt => hp.2 (hrel e hp.1 hlt)

/-- The terminal threshold follows from actual tree paths, without a global
minimum-cut lower bound or a terminal-connectivity oracle. -/
theorem FundamentalCorrect.level_terminal_lower {G : WeightedGraph V}
    {T : TwoRespecting.RootedTree V} {tau : V → ℝ} (hT : FundamentalCorrect G T tau)
    (a : ℝ) {U : Finset V} (hU : U ∈ levelParts T tau a) :
    ∀ S, Separates U S → a ≤ G.cut S := by
  obtain ⟨r, _, rfl⟩ := mem_image.mp hU
  intro S hS
  obtain ⟨s, hs⟩ := hS.1
  obtain ⟨t, ht, htS⟩ := not_subset.mp hS.2
  obtain ⟨e, hep, heS⟩ := exists_path_crossing T (mem_inter.mp hs).1 htS
  exact (levelClass_path_lower T tau a (mem_inter.mp hs).2 ht hep).trans
    (hT.crossing_lower ((mem_pathEdges T s t e).mp hep).1 heS)

def frontierTerminals (T : TwoRespecting.RootedTree V) (U : Finset V) :
    Finset (FrontierVertex T U) := univ.image Sum.inl

@[simp] theorem card_frontierTerminals (T : TwoRespecting.RootedTree V) (U : Finset V) :
    (frontierTerminals T U).card = U.card := by
  rw [frontierTerminals, card_image_of_injective _ Sum.inl_injective]
  simp

theorem separates_frontierTerminals_iff (T : TwoRespecting.RootedTree V) (U : Finset V)
    (hU : PathClosed T U) (hne : U.Nonempty) (S : Finset (FrontierVertex T U)) :
    Separates (frontierTerminals T U) S ↔
      Separates U (pull (frontierPartition T U hU hne).projection S) := by
  let P := frontierPartition T U hU hne
  have hp (v : {x : V // x ∈ U}) : P.projection v.val = Sum.inl v :=
    P.projection_root (Sum.inl v)
  constructor
  · rintro ⟨⟨b, hb⟩, hn⟩
    obtain ⟨v, _, rfl⟩ := mem_image.mp (mem_inter.mp hb).2
    refine ⟨⟨v.val, mem_inter.mpr ⟨?_, v.property⟩⟩, ?_⟩
    · apply (mem_pull P.projection S v.val).mpr
      exact (hp v).symm ▸ (mem_inter.mp hb).1
    · intro hsub
      apply hn
      intro b hb
      obtain ⟨w, _, rfl⟩ := mem_image.mp hb
      have hw' : P.projection w.val ∈ S :=
        (mem_pull P.projection S w.val).mp (hsub w.property)
      exact hp w ▸ hw'
  · rintro ⟨⟨v, hv⟩, hn⟩
    let b : {x : V // x ∈ U} := ⟨v, (mem_inter.mp hv).2⟩
    refine ⟨⟨Sum.inl b, mem_inter.mpr ⟨?_, mem_image_of_mem _ (mem_univ b)⟩⟩, ?_⟩
    · have hv' : P.projection b.val ∈ S :=
        (mem_pull P.projection S b.val).mp (mem_inter.mp hv).1
      exact hp b ▸ hv'
    · intro hsub
      apply hn
      intro w hw
      apply (mem_pull P.projection S w).mpr
      have hw' : Sum.inl (⟨w, hw⟩ : {x : V // x ∈ U}) ∈ S :=
        hsub (mem_image_of_mem Sum.inl (mem_univ (⟨w, hw⟩ : {x : V // x ∈ U})))
      exact (hp ⟨w, hw⟩).symm ▸ hw'

/-- Construct a real terminal lower-bound certificate on the actual frontier
quotient; only its correctness lifting uses previously certified boundary edges. -/
theorem exists_frontier_terminal_certificate (G : WeightedGraph V)
    (T : TwoRespecting.RootedTree V) (U : Finset V)
    (hU : PathClosed T U) (hne : U.Nonempty) {a : ℝ} (ha : 0 < a)
    (hconn : ∀ S, Separates U S → a ≤ G.cut S) :
    ∃ Q : Finset (Finset V),
      Q.card ≤ 17 * frontierVolume T U * (Nat.clog 2 (2 * U.card)) ^ 2 ∧
      ∀ H : WeightedGraph V, Consistent G H Q →
        (∀ e ∈ boundary T U, IsSTMinCut H e (T.parent e) (T.subtree e)) →
        ∀ S, Separates U S → a ≤ H.cut S := by
  let P := frontierPartition T U hU hne
  have hc : ∀ S, Separates (frontierTerminals T U) S → a ≤ (G.contract P.projection).cut S := by
    intro S hS
    rw [cut_contract]
    exact hconn _ ((separates_frontierTerminals_iff T U hU hne S).mp hS)
  obtain ⟨Q₀, hQ₀, hcert⟩ := exists_terminal_lower_certificate
    (G.contract P.projection) (frontierTerminals T U) ha hc
  refine ⟨pullQueries P.projection Q₀, ?_, fun H hH hmin S hS => ?_⟩
  · exact (pullQueries_card _ _).trans (by
      simpa only [card_frontierVertex, card_frontierTerminals] using hQ₀)
  · have hp : ∀ b, RootProtected H (fiber P.projection b) (P.root b) := by
      intro b
      rw [P.fiber_projection]
      exact frontier_protected H T U hmin b
    obtain ⟨R, hR, hside⟩ := exists_quotient_round H P.projection P.root P.projection_root hp S
    have hRS : Separates (frontierTerminals T U) R := by
      obtain ⟨s, hs⟩ := hS.1
      obtain ⟨t, ht, htS⟩ := not_subset.mp hS.2
      let bs : {x : V // x ∈ U} := ⟨s, (mem_inter.mp hs).2⟩
      let bt : {x : V // x ∈ U} := ⟨t, ht⟩
      refine ⟨⟨Sum.inl bs, mem_inter.mpr
        ⟨(hside (Sum.inl bs)).mpr (mem_inter.mp hs).1, mem_image_of_mem _ (mem_univ bs)⟩⟩, ?_⟩
      intro hsub
      exact htS ((hside (Sum.inl bt)).mp (hsub (mem_image_of_mem _ (mem_univ bt))))
    exact (hcert (H.contract P.projection) (consistent_contract _ hH) R hRS).trans hR

/-- One shared query family advances every edge at this exact positive level. -/
theorem exists_level_step_certificate (G : WeightedGraph V) (T : TwoRespecting.RootedTree V)
    (tau : V → ℝ) (hT : FundamentalCorrect G T tau) {a : ℝ} (ha : 0 < a) :
    ∃ Q : Finset (Finset V),
      Q.card ≤ 51 * Fintype.card V * (Nat.clog 2 (2 * Fintype.card V)) ^ 2 ∧
      ∀ H : WeightedGraph V, Consistent G H Q →
        (∀ f, f ≠ T.root → tau f < a → IsSTMinCut H f (T.parent f) (T.subtree f)) →
        ∀ e, e ≠ T.root → tau e = a → ∀ S, e ∈ S → T.parent e ∉ S → a ≤ H.cut S := by
  let parts := levelParts T tau a
  have hex : ∀ U : Finset V, ∃ Q : Finset (Finset V),
      Q.card ≤ 17 * frontierVolume T U * (Nat.clog 2 (2 * U.card)) ^ 2 ∧
      (U ∈ parts → ∀ H : WeightedGraph V, Consistent G H Q →
        (∀ f ∈ boundary T U, IsSTMinCut H f (T.parent f) (T.subtree f)) →
        ∀ S, Separates U S → a ≤ H.cut S) := by
    intro U
    by_cases hU : U ∈ parts
    · have hp : PathClosed T U := by
        obtain ⟨r, _, rfl⟩ := mem_image.mp hU
        exact levelClass_pathClosed T tau a r
      obtain ⟨Q, hQ, hcert⟩ := exists_frontier_terminal_certificate G T U hp
        (levelParts_nonempty T tau a hU) ha (hT.level_terminal_lower a hU)
      exact ⟨Q, hQ, fun _ => hcert⟩
    · exact ⟨∅, by simp, fun h => (hU h).elim⟩
  choose Q hcard hcert using hex
  refine ⟨parts.biUnion Q, ?_, fun H hH hprev e he hea S hs ht => ?_⟩
  · let L := Nat.clog 2 (2 * Fintype.card V)
    have hb := disjoint_frontier_volume T parts (levelParts_disjoint T tau a)
    calc
      (parts.biUnion Q).card ≤ ∑ U ∈ parts, (Q U).card := card_biUnion_le
      _ ≤ ∑ U ∈ parts, 17 * frontierVolume T U * L ^ 2 := by
        apply sum_le_sum
        intro U hU
        exact (hcard U).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
          (Nat.clog_mono_right 2 (Nat.mul_le_mul_left 2 (card_le_univ U))) 2))
      _ = 17 * (∑ U ∈ parts, frontierVolume T U) * L ^ 2 := by rw [← sum_mul, ← mul_sum]
      _ ≤ 51 * Fintype.card V * L ^ 2 := by
        exact Nat.mul_le_mul_right (L ^ 2) (by omega)
  · let U := levelClass T tau a e
    have hU : U ∈ parts := mem_image_of_mem _ (mem_univ e)
    have heU : e ∈ U := self_mem_levelClass T tau a e
    have hpU : T.parent e ∈ U := (mem_levelClass T tau a e _).mpr
      (levelRel_parent_of_le T tau (le_of_eq hea.symm))
    have hlocal : Consistent G H (Q U) := hH.mono (fun A hA => mem_biUnion.mpr ⟨U, hU, hA⟩)
    apply hcert U hU H hlocal
    · intro f hf
      exact hprev f (boundary_endpoints T hf).1 (levelParts_boundary_lt T tau a hU hf)
    · exact ⟨⟨e, mem_inter.mpr ⟨hs, heU⟩⟩, fun h => ht (h hpU)⟩

/-- The finite induction carries only already handled smaller levels. The final
endpoint instantiates the lower-set invariant with all actual positive weights. -/
private theorem level_prefix_certificate (G : WeightedGraph V) (T : TwoRespecting.RootedTree V)
    (tau : V → ℝ) (hT : FundamentalCorrect G T tau) (A : Finset ℝ) :
    A ⊆ positiveWeights T tau →
    (∀ a ∈ A, ∀ e, e ≠ T.root → 0 < tau e → tau e < a → tau e ∈ A) →
    ∃ Q : Finset (Finset V),
      Q.card ≤ 51 * A.card * Fintype.card V * (Nat.clog 2 (2 * Fintype.card V)) ^ 2 ∧
      ∀ H : WeightedGraph V, Consistent G H (Q ∪ fundamentalQueries T) →
        ∀ e, e ≠ T.root → tau e = 0 ∨ tau e ∈ A →
          IsSTMinCut H e (T.parent e) (T.subtree e) := by
  induction A using Finset.induction_on_max with
  | empty =>
    intro _ _
    refine ⟨∅, by simp, fun H hH e he hzero => ?_⟩
    have hz : tau e = 0 := by simpa using hzero
    have hval : H.cut (T.subtree e) = 0 :=
      (hH _ (mem_union_right _ (fundamental_mem T he))).trans ((hT e he).1.trans hz)
    refine ⟨(subtree_separates T he).1, (subtree_separates T he).2, fun S _ _ => ?_⟩
    rw [hval]
    exact H.cut_nonneg S
  | @insert a A hless ih =>
    intro hA hdown
    have haA : a ∉ A := fun h => lt_irrefl a (hless a h)
    have ha : 0 < a := by
      obtain ⟨e, he, hval⟩ := mem_image.mp (hA (mem_insert_self _ _))
      exact hval ▸ (mem_filter.mp he).2
    have hsub : A ⊆ positiveWeights T tau := (subset_insert a A).trans hA
    have hdownA : ∀ b ∈ A, ∀ e, e ≠ T.root → 0 < tau e → tau e < b → tau e ∈ A := by
      intro b hb e he hpos hlt
      have hm := hdown b (mem_insert_of_mem hb) e he hpos hlt
      rcases mem_insert.mp hm with hm | hm
      · have := hless b hb
        rw [hm] at hlt
        linarith
      · exact hm
    obtain ⟨Q₀, hQ₀, hcert₀⟩ := ih hsub hdownA
    obtain ⟨Qa, hQa, hcerta⟩ := exists_level_step_certificate G T tau hT ha
    refine ⟨Q₀ ∪ Qa, ?_, fun H hH e he hcase => ?_⟩
    · have hc := card_union_le Q₀ Qa
      rw [card_insert_of_notMem haA]
      nlinarith [hc, hQ₀, hQa]
    · have hH₀ : Consistent G H (Q₀ ∪ fundamentalQueries T) :=
        hH.mono (by intro S hS; simp only [mem_union] at hS ⊢; tauto)
      have hHa : Consistent G H Qa :=
        hH.mono (by intro S hS; exact mem_union_left _ (mem_union_right _ hS))
      have hprev : ∀ f, f ≠ T.root → tau f < a → IsSTMinCut H f (T.parent f) (T.subtree f) := by
        intro f hf hlt
        apply hcert₀ H hH₀ f hf
        by_cases hz : tau f = 0
        · exact Or.inl hz
        · have hpos : 0 < tau f := lt_of_le_of_ne (hT.nonneg hf) (Ne.symm hz)
          have hm := hdown a (mem_insert_self _ _) f hf hpos hlt
          exact Or.inr ((mem_insert.mp hm).resolve_left (ne_of_lt hlt))
      rcases hcase with hz | hm
      · exact hcert₀ H hH₀ e he (Or.inl hz)
      · rcases mem_insert.mp hm with hea | hm
        · have hval : H.cut (T.subtree e) = a :=
            (hH _ (mem_union_right _ (fundamental_mem T he))).trans ((hT e he).1.trans hea)
          refine ⟨(subtree_separates T he).1, (subtree_separates T he).2, fun S hs ht => ?_⟩
          rw [hval]
          exact hcerta H hHa hprev e he hea S hs ht
        · exact hcert₀ H hH₀ e he (Or.inr hm)

/-- One certificate, selected before every unrestricted real-weighted competitor,
retains all fundamental minimum shores and weights simultaneously. -/
theorem exists_level_certificate (G : WeightedGraph V) (T : TwoRespecting.RootedTree V)
    (tau : V → ℝ) (hn : 1 ≤ Fintype.card V) (hT : FundamentalCorrect G T tau) :
    ∃ Q : Finset (Finset V),
      Q.card ≤ (Fintype.card V - 1) +
        51 * (positiveWeights T tau).card * Fintype.card V *
          (Nat.clog 2 (2 * Fintype.card V)) ^ 2 ∧ TreeCertificate G T tau Q := by
  have hmem : ∀ e, e ≠ T.root → 0 < tau e → tau e ∈ positiveWeights T tau := by
    intro e he hp
    exact mem_image_of_mem _ (mem_filter.mpr ⟨(mem_edges T e).mpr he, hp⟩)
  obtain ⟨Q₀, hQ₀, hcert⟩ := level_prefix_certificate G T tau hT (positiveWeights T tau)
    (subset_refl _) (fun _ _ e he hp _ => hmem e he hp)
  refine ⟨Q₀ ∪ fundamentalQueries T, ?_, subset_union_right, fun H hH e he => ?_⟩
  · have hc := card_union_le Q₀ (fundamentalQueries T)
    have hf := fundamentalQueries_card T
    omega
  · refine ⟨(hH _ (mem_union_right _ (fundamental_mem T he))).trans (hT e he).1,
      hcert H hH e he ?_⟩
    by_cases hz : tau e = 0
    · exact Or.inl hz
    · exact Or.inr (hmem e he (lt_of_le_of_ne (hT.nonneg he) (Ne.symm hz)))

end
end CutQueryComplexity.Certificate.GomoryHu

#print axioms CutQueryComplexity.Certificate.GomoryHu.levelClass_pathClosed
#print axioms CutQueryComplexity.Certificate.GomoryHu.levelParts_boundary_lt
#print axioms CutQueryComplexity.Certificate.GomoryHu.FundamentalCorrect.level_terminal_lower
#print axioms CutQueryComplexity.Certificate.GomoryHu.exists_frontier_terminal_certificate
#print axioms CutQueryComplexity.Certificate.GomoryHu.exists_level_step_certificate
#print axioms CutQueryComplexity.Certificate.GomoryHu.exists_level_certificate
