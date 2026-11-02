import CutQueryComplexity.Certificate.GomoryHu.Decomposition

set_option autoImplicit false

/-! # Degree-sensitive whole-tree certificates

The local quotient is constructed from actual frontier blocks and is refined
to the actual branches at a centroid. Every coarse capacity is learned by pair
queries. The recursion charges component size and original tree incidences;
halving bounds depth, while disjoint children charge each centroid only once.
-/

namespace CutQueryComplexity.Certificate.GomoryHu

open Finset WeightedGraph
open scoped Classical
noncomputable section

variable {V B C : Type} [Fintype V] [DecidableEq V]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

def Refines (P : BlockPartition V B) (R : BlockPartition V C) : Prop :=
  ∀ b x, x ∈ P.block b → R.projection x = R.projection (P.root b)

def refinementPartition (P : BlockPartition V B) (R : BlockPartition V C)
    (hr : Refines P R) : BlockPartition B C where
  block c := fiber (fun b => R.projection (P.root b)) c
  root c := P.projection (R.root c)
  root_mem c := by
    rw [mem_fiber, ← hr _ _ (P.projection_mem (R.root c)), R.projection_root]
  disjoint b c hbc := by
    apply disjoint_left.mpr
    intro x hx hy
    have hx' := (mem_fiber (fun y => R.projection (P.root y)) b x).mp hx
    have hy' := (mem_fiber (fun y => R.projection (P.root y)) c x).mp hy
    exact hbc (hx'.symm.trans hy')
  cover b := ⟨R.projection (P.root b), by simp⟩

theorem refinement_comp (P : BlockPartition V B) (R : BlockPartition V C)
    (hr : Refines P R) (x : V) :
    (refinementPartition P R hr).projection (P.projection x) = R.projection x := by
  apply ((refinementPartition P R hr).projection_eq_iff _ _).mpr
  change P.projection x ∈ fiber (fun b => R.projection (P.root b)) (R.projection x)
  rw [mem_fiber]
  exact (hr _ x (P.projection_mem x)).symm

theorem pull_refinement_block (P : BlockPartition V B) (R : BlockPartition V C)
    (hr : Refines P R) (c : C) :
    pull P.projection ((refinementPartition P R hr).block c) = R.block c := by
  ext x
  rw [mem_pull]
  change P.projection x ∈ fiber (fun b => R.projection (P.root b)) c ↔ x ∈ R.block c
  rw [mem_fiber, ← hr _ x (P.projection_mem x), R.projection_eq_iff]

theorem refinement_protected (G : WeightedGraph V)
    (P : BlockPartition V B) (R : BlockPartition V C) (hr : Refines P R)
    (hp : ∀ c, RootProtected G (R.block c) (R.root c)) :
    ∀ c, RootProtected (G.contract P.projection)
      ((refinementPartition P R hr).block c) ((refinementPartition P R hr).root c) := by
  intro c
  refine ⟨(refinementPartition P R hr).root_mem c, fun A hA hx => ?_⟩
  rw [cut_contract, cut_contract, pull_refinement_block]
  apply (hp c).2
  · intro x hx
    have := hA ((mem_pull _ _ _).mp hx)
    exact (show pull P.projection ((refinementPartition P R hr).block c) = R.block c
      from pull_refinement_block P R hr c) ▸ (mem_pull _ _ _).mpr this
  · exact (mem_pull _ _ _).mpr hx

/-- A refinement has an actual query certificate. Any true coarse-block mincut
between retained representatives then lifts in every consistent graph whose
fine blocks were protected by earlier stages. -/
theorem exists_refinement_certificate (G : WeightedGraph V)
    (P : BlockPartition V B) (R : BlockPartition V C) (hr : Refines P R)
    (hp : ∀ c, RootProtected G (R.block c) (R.root c)) :
    ∃ Q : Finset (Finset V), Q.card ≤ 18 * Fintype.card B + (Fintype.card C) ^ 2 ∧
      ∀ H : WeightedGraph V, Consistent G H Q →
        (∀ b, RootProtected H (P.block b) (P.root b)) →
        ∀ s t : C, P.root (P.projection (R.root s)) = R.root s →
          P.root (P.projection (R.root t)) = R.root t →
          IsSTMinCut G (R.root s) (R.root t) (R.block s) →
          IsSTMinCut H (R.root s) (R.root t) (R.block s) := by
  let D := refinementPartition P R hr
  obtain ⟨Q₀, hQ₀, hcert⟩ := D.exists_learned_quotient_certificate (G.contract P.projection)
    (refinement_protected G P R hr hp)
  refine ⟨pullQueries P.projection Q₀, (pullQueries_card _ _).trans hQ₀,
    fun H hH hPH s t hsroot htroot hmin => ?_⟩
  obtain ⟨heq, hDH⟩ := hcert (H.contract P.projection) (consistent_contract _ hH)
  have hproj (c : C) : D.projection (P.projection (R.root c)) = c := D.projection_root c
  have hpull : pull P.projection (pull D.projection {s}) = R.block s := by
    change pull P.projection (fiber D.projection s) = R.block s
    rw [D.fiber_projection]
    exact pull_refinement_block P R hr s
  have hminG : IsSTMinCut ((G.contract P.projection).contract D.projection) s t {s} := by
    have hts : t ≠ s := by
      intro h
      subst t
      exact hmin.2.1 (R.root_mem s)
    refine ⟨mem_singleton_self _, by simpa using hts, fun A hs ht => ?_⟩
    rw [cut_contract, cut_contract, cut_contract, cut_contract, hpull]
    apply hmin.2.2
    · simpa only [mem_pull, hproj] using hs
    · simpa only [mem_pull, hproj] using ht
  have hminH : IsSTMinCut ((H.contract P.projection).contract D.projection) s t {s} := by
    rw [heq]
    exact hminG
  have hmid := D.lift_minCut hDH hminH
  have hfinal := P.lift_minCut hPH hmid
  change IsSTMinCut H (P.root (P.projection (R.root s)))
    (P.root (P.projection (R.root t))) (pull P.projection (pull D.projection {s})) at hfinal
  simpa only [hsroot, htroot, hpull] using hfinal

theorem pathClosed_singleton (T : TwoRespecting.RootedTree V) (c : V) : PathClosed T {c} := by
  intro s hs t ht e he
  have hs' := mem_singleton.mp hs
  have ht' := mem_singleton.mp ht
  subst s
  subst t
  exact (((mem_pathEdges T c c e).mp he).2 Iff.rfl).elim

theorem boundary_singleton_card (T : TwoRespecting.RootedTree V) (c : V) :
    (boundary T {c}).card = degree T c := by
  unfold degree
  congr 1
  ext e
  simp only [boundary, degree, mem_filter, mem_singleton, mem_edges]
  by_cases he : e ≠ T.root
  · have hne := TwoRespecting.RootedTree.parent_ne_self (T := T) he
    constructor
    · rintro ⟨_, h⟩
      exact ⟨he, by tauto⟩
    · rintro ⟨_, h⟩
      refine ⟨he, ?_⟩
      rcases h with h | h <;> intro hiff
      · exact hne ((hiff.mp h).trans h.symm)
      · exact hne (h.trans (hiff.mpr h).symm)
  · simp [he]

def starPartition (T : TwoRespecting.RootedTree V) (c : V) :
    BlockPartition V (FrontierVertex T {c}) :=
  frontierPartition T {c} (pathClosed_singleton T c) (singleton_nonempty c)

theorem card_starVertex (T : TwoRespecting.RootedTree V) (c : V) :
    Fintype.card (FrontierVertex T {c}) = degree T c + 1 := by
  rw [card_frontierVertex, frontierVolume, card_singleton, boundary_singleton_card, add_comm]

/-- A connected outside branch avoiding the centroid lies in a single actual
star block. This proves the refinement geometrically, not as an oracle premise. -/
theorem PathClosed.star_projection_constant {T : TwoRespecting.RootedTree V} {K : Finset V}
    (hK : PathClosed T K) {c x y : V} (hc : c ∉ K) (hx : x ∈ K) (hy : y ∈ K) :
    (starPartition T c).projection x = (starPartition T c).projection y := by
  let R := starPartition T c
  have hymem := R.projection_mem y
  generalize hb : R.projection y = b at hymem ⊢
  cases b with
  | inl v =>
    have hyc : y = c := (mem_singleton.mp hymem).trans (mem_singleton.mp v.property)
    exact (hc (hyc ▸ hy)).elim
  | inr e =>
    apply (R.projection_eq_iff x (Sum.inr e)).mpr
    change x ∈ outerShore T {c} e.val
    by_contra hxE
    have he := boundary_endpoints T e.property
    have hpath : e.val ∈ pathEdges T y x := by
      apply (mem_pathEdges T y x e.val).mpr
      refine ⟨he.1, ?_⟩
      change y ∈ outerShore T {c} e.val at hymem
      by_cases hec : e.val ∈ ({c} : Finset V) <;> simp_all [outerShore]
    have hend := hK y hy x hx e.val hpath
    have hin : innerRoot T {c} e.val ∈ K := by
      by_cases hec : e.val ∈ ({c} : Finset V)
      · simpa [innerRoot, hec] using hend.1
      · simpa [innerRoot, hec] using hend.2
    exact hc ((mem_singleton.mp he.2.1) ▸ hin)

theorem frontier_refines_star (T : TwoRespecting.RootedTree V) (U : Finset V)
    (hU : PathClosed T U) (hne : U.Nonempty) {c : V} (hc : c ∈ U) :
    Refines (frontierPartition T U hU hne) (starPartition T c) := by
  intro b x hx
  cases b with
  | inl v =>
    have he : x = v.val := mem_singleton.mp hx
    subst x
    rfl
  | inr e =>
    apply (outerShore_pathClosed T U e.val).star_projection_constant
    · exact fun h => disjoint_left.mp (hU.disjoint_outerShore e.property) hc h
    · exact hx
    · exact (outerShore_endpoints T e.property).1

theorem FundamentalCorrect.outer_minCut {G : WeightedGraph V}
    {T : TwoRespecting.RootedTree V} {tau : V → ℝ} (hT : FundamentalCorrect G T tau)
    (U : Finset V) {e : V} (he : e ∈ boundary T U) :
    IsSTMinCut G (outerRoot T U e) (innerRoot T U e) (outerShore T U e) := by
  have hm := (hT e (boundary_endpoints T he).1).2
  by_cases heU : e ∈ U
  · simp only [outerRoot, innerRoot, outerShore, heU, ite_true]
    refine ⟨mem_compl.mpr hm.2.1, by simpa using hm.1, fun S hs ht => ?_⟩
    have h := hm.2.2 Sᶜ (mem_compl.mpr ht) (fun h => mem_compl.mp h hs)
    simpa only [cut_compl] using h
  · simpa only [outerRoot, innerRoot, outerShore, heU, ite_false] using hm

/-- One centroid step certifies all newly exposed internal edges, using the
actual frontier graph and its completely learned contracted star. -/
theorem exists_centroid_step_certificate (G : WeightedGraph V)
    (T : TwoRespecting.RootedTree V) (tau : V → ℝ) (hT : FundamentalCorrect G T tau)
    (U : Finset V) (hU : PathClosed T U) (hne : U.Nonempty) {c : V} (hc : c ∈ U) :
    ∃ Q : Finset (Finset V),
      Q.card ≤ 18 * frontierVolume T U + (degree T c + 1) ^ 2 ∧
      ∀ H : WeightedGraph V, Consistent G H Q →
        (∀ f ∈ boundary T U, IsSTMinCut H f (T.parent f) (T.subtree f)) →
        ∀ e, e ≠ T.root → e ∈ U → T.parent e ∈ U → (e = c ∨ T.parent e = c) →
          IsSTMinCut H e (T.parent e) (T.subtree e) := by
  let P := frontierPartition T U hU hne
  let R := starPartition T c
  have hr : Refines P R := frontier_refines_star T U hU hne hc
  have hp : ∀ b, RootProtected G (R.block b) (R.root b) :=
    frontier_protected G T {c} (fun e he => (hT e (boundary_endpoints T he).1).2)
  obtain ⟨Q, hQ, hcert⟩ := exists_refinement_certificate G P R hr hp
  refine ⟨Q, by rw [card_frontierVertex T U, card_starVertex T c] at hQ; exact hQ,
    fun H hH hboundary e he heU hpU hinc => ?_⟩
  have hestar : e ∈ boundary T {c} := by
    apply mem_filter.mpr
    refine ⟨(mem_edges T e).mpr he, ?_⟩
    have hne := TwoRespecting.RootedTree.parent_ne_self (T := T) he
    simp only [mem_singleton]
    rcases hinc with h | h <;> intro hiff
    · exact hne ((hiff.mp h).trans h.symm)
    · exact hne (h.trans (hiff.mpr h).symm)
  let s : FrontierVertex T {c} := .inr ⟨e, hestar⟩
  let t : FrontierVertex T {c} := .inl ⟨c, mem_singleton_self _⟩
  have hinner : innerRoot T {c} e = c := mem_singleton.mp (boundary_endpoints T hestar).2.1
  have hsU : R.root s ∈ U := by
    change outerRoot T {c} e ∈ U
    by_cases hec : e ∈ ({c} : Finset V)
    · simpa [outerRoot, hec] using hpU
    · simpa [outerRoot, hec] using heU
  have hfix (x : V) (hx : x ∈ U) : P.root (P.projection x) = x := by
    have hpx := P.projection_root (Sum.inl (⟨x, hx⟩ : {v : V // v ∈ U}))
    change P.projection x = Sum.inl ⟨x, hx⟩ at hpx
    rw [hpx]
    rfl
  have htrue : IsSTMinCut G (R.root s) (R.root t) (R.block s) := by
    change IsSTMinCut G (outerRoot T {c} e) c (outerShore T {c} e)
    simpa only [hinner] using hT.outer_minCut {c} hestar
  have hnew := hcert H hH (frontier_protected H T U hboundary) s t
    (hfix _ hsU) (hfix _ hc) htrue
  change IsSTMinCut H (outerRoot T {c} e) c (outerShore T {c} e) at hnew
  by_cases hec : e ∈ ({c} : Finset V)
  · have heq : e = c := mem_singleton.mp hec
    simp only [outerRoot, outerShore, hec, ite_true] at hnew
    refine ⟨(subtree_separates T he).1, (subtree_separates T he).2, fun S hs ht => ?_⟩
    have hb := hnew.2.2 Sᶜ (mem_compl.mpr ht) (fun h => mem_compl.mp h (heq ▸ hs))
    simpa only [cut_compl] using hb
  · have hp : T.parent e = c := hinc.resolve_left (by simpa using hec)
    simpa only [outerRoot, outerShore, hec, ite_false, hp] using hnew

def treeMass (T : TwoRespecting.RootedTree V) (U : Finset V) : ℕ :=
  ∑ u ∈ U, (1 + degree T u)

def starCharge (T : TwoRespecting.RootedTree V) (U : Finset V) : ℕ :=
  ∑ u ∈ U, (degree T u + 1) ^ 2

theorem frontierVolume_le_treeMass (T : TwoRespecting.RootedTree V) (U : Finset V) :
    frontierVolume T U ≤ treeMass T U := by
  have h := boundary_card_le_degree_sum T U
  simp only [frontierVolume, treeMass, sum_add_distrib, sum_const, smul_eq_mul, mul_one]
  omega

theorem centroid_not_mem_part (T : TwoRespecting.RootedTree V) (U : Finset V) (c : V)
    {P : Finset V} (hP : P ∈ DirectedCertificate.Completion.separatorParts T U c) : c ∉ P := by
  rcases DirectedCertificate.Completion.separatorParts_cases T U c hP with
    rfl | ⟨v, hv, hvc, rfl⟩
  · exact fun h => (mem_sdiff.mp h).2 (TwoRespecting.RootedTree.self_mem_subtree (T := T) c)
  · exact fun h => parent_not_mem_subtree T hv (by simpa only [hvc] using (mem_inter.mp h).2)

/-- A child has only old boundary edges and the newly exposed centroid edges. -/
theorem separatorPart_boundary (T : TwoRespecting.RootedTree V) (U : Finset V) (c : V)
    {P : Finset V} (hP : P ∈ DirectedCertificate.Completion.separatorParts T U c)
    {e : V} (he : e ∈ boundary T P) :
    e ∈ boundary T U ∨ (e ∈ U ∧ T.parent e ∈ U ∧ (e = c ∨ T.parent e = c)) := by
  have hsub := DirectedCertificate.Completion.separatorParts_subset T U c hP
  have hcross := (mem_filter.mp he).2
  have her := (mem_edges T e).mp (mem_filter.mp he).1
  by_cases heU : e ∈ boundary T U
  · exact Or.inl heU
  · have hiffU : e ∈ U ↔ T.parent e ∈ U := by
      by_contra h
      exact heU (mem_filter.mpr ⟨(mem_edges T e).mpr her, h⟩)
    have heIn : e ∈ U := by
      by_cases heP : e ∈ P
      · exact hsub heP
      · have hpP : T.parent e ∈ P := by tauto
        exact hiffU.mpr (hsub hpP)
    have hpIn := hiffU.mp heIn
    refine Or.inr ⟨heIn, hpIn, ?_⟩
    by_cases hec : e = c
    · exact Or.inl hec
    · by_cases hpc : T.parent e = c
      · exact Or.inr hpc
      · exact (hcross (DirectedCertificate.Completion.separatorParts_parent_iff
          T U c hP heIn hpIn hec hpc rfl)).elim

theorem separatorParts_mass (T : TwoRespecting.RootedTree V) (U : Finset V) (c : V) :
    (∑ P ∈ DirectedCertificate.Completion.separatorParts T U c, treeMass T P) ≤ treeMass T U := by
  unfold treeMass
  have hsum := sum_biUnion (f := fun u => 1 + degree T u)
    (DirectedCertificate.Completion.separatorParts_disjoint T U c)
  simp only [id_eq] at hsum
  rw [← hsum]
  apply sum_le_sum_of_subset
  intro x hx
  obtain ⟨P, hP, hxP⟩ := mem_biUnion.mp hx
  exact DirectedCertificate.Completion.separatorParts_subset T U c hP hxP

theorem separatorParts_starCharge (T : TwoRespecting.RootedTree V) (U : Finset V)
    {c : V} (hc : c ∈ U) :
    (degree T c + 1) ^ 2 +
      (∑ P ∈ DirectedCertificate.Completion.separatorParts T U c, starCharge T P) ≤
        starCharge T U := by
  have hsum : (∑ P ∈ DirectedCertificate.Completion.separatorParts T U c, starCharge T P) ≤
      starCharge T (U.erase c) := by
    unfold starCharge
    have hsum := sum_biUnion (f := fun u => (degree T u + 1) ^ 2)
      (DirectedCertificate.Completion.separatorParts_disjoint T U c)
    simp only [id_eq] at hsum
    rw [← hsum]
    apply sum_le_sum_of_subset
    intro x hx
    obtain ⟨P, hP, hxP⟩ := mem_biUnion.mp hx
    exact mem_erase.mpr ⟨fun h => centroid_not_mem_part T U c hP (h ▸ hxP),
      DirectedCertificate.Completion.separatorParts_subset T U c hP hxP⟩
  exact (Nat.add_le_add_left hsum _).trans_eq
    (add_sum_erase U (fun u => (degree T u + 1) ^ 2) hc)

/-- Actual finite centroid recursion. Its correctness assumption is precisely
the already certified outside boundary; it is empty at the final root call. -/
private theorem centroid_certificate_rec (G : WeightedGraph V)
    (T : TwoRespecting.RootedTree V) (tau : V → ℝ) (hT : FundamentalCorrect G T tau) :
    ∀ d : ℕ, ∀ U : Finset V, PathClosed T U → U.card < 2 ^ d →
      ∃ Q : Finset (Finset V),
        Q.card ≤ 18 * treeMass T U * d + starCharge T U ∧
        ∀ H : WeightedGraph V, Consistent G H Q →
          (∀ f ∈ boundary T U, IsSTMinCut H f (T.parent f) (T.subtree f)) →
          ∀ e, e ≠ T.root → e ∈ U → T.parent e ∈ U →
            IsSTMinCut H e (T.parent e) (T.subtree e) := by
  intro d
  induction d with
  | zero =>
    intro U _ hsize
    have he : U = ∅ := card_eq_zero.mp (by simpa using hsize)
    subst U
    exact ⟨∅, by simp [treeMass, starCharge], fun _ _ _ _ _ he => (notMem_empty _ he).elim⟩
  | succ d ih =>
    intro U hU hsize
    by_cases hne : U.Nonempty
    · obtain ⟨c, hc, hhalf⟩ := exists_pathClosed_centroid T U hne hU
      obtain ⟨Qc, hQc, hcent⟩ := exists_centroid_step_certificate G T tau hT U hU hne hc
      let parts := DirectedCertificate.Completion.separatorParts T U c
      have hsmall : ∀ P ∈ parts, P.card < 2 ^ d := by
        intro P hP
        have hh := hhalf P hP
        rw [pow_succ] at hsize
        omega
      have hex : ∀ P : Finset V, ∃ Q : Finset (Finset V),
          Q.card ≤ 18 * treeMass T P * d + starCharge T P ∧
          (P ∈ parts → ∀ H : WeightedGraph V, Consistent G H Q →
            (∀ f ∈ boundary T P, IsSTMinCut H f (T.parent f) (T.subtree f)) →
            ∀ e, e ≠ T.root → e ∈ P → T.parent e ∈ P →
              IsSTMinCut H e (T.parent e) (T.subtree e)) := by
        intro P
        by_cases hP : P ∈ parts
        · obtain ⟨Q, hQ, hcert⟩ := ih P (hU.separatorParts c hP) (hsmall P hP)
          exact ⟨Q, hQ, fun _ => hcert⟩
        · exact ⟨∅, by simp, fun h => (hP h).elim⟩
      choose Q hcard hcert using hex
      refine ⟨Qc ∪ parts.biUnion Q, ?_, fun H hH hboundary e he heU hpU => ?_⟩
      · have hmass := separatorParts_mass T U c
        have hstars := separatorParts_starCharge T U hc
        have hfront := frontierVolume_le_treeMass T U
        have hmul : 18 * (∑ P ∈ parts, treeMass T P) * d ≤
            18 * treeMass T U * d :=
          Nat.mul_le_mul_right d (Nat.mul_le_mul_left 18 hmass)
        have hsum : (∑ P ∈ parts, (18 * treeMass T P * d + starCharge T P)) =
            18 * (∑ P ∈ parts, treeMass T P) * d + ∑ P ∈ parts, starCharge T P := by
          rw [sum_add_distrib, ← sum_mul, ← mul_sum]
        have hchild := (card_biUnion_le (s := parts) (t := Q)).trans
          (sum_le_sum fun P _ => hcard P)
        rw [hsum] at hchild
        have hlocal : 18 * frontierVolume T U ≤ 18 * treeMass T U := Nat.mul_le_mul_left 18 hfront
        calc
          (Qc ∪ parts.biUnion Q).card ≤
              (18 * frontierVolume T U + (degree T c + 1) ^ 2) +
                (18 * (∑ P ∈ parts, treeMass T P) * d +
                  ∑ P ∈ parts, starCharge T P) :=
            (card_union_le Qc (parts.biUnion Q)).trans (Nat.add_le_add hQc hchild)
          _ ≤ (18 * treeMass T U + (degree T c + 1) ^ 2) +
                (18 * treeMass T U * d + ∑ P ∈ parts, starCharge T P) :=
            Nat.add_le_add (Nat.add_le_add_right hlocal _) (Nat.add_le_add_right hmul _)
          _ = (18 * treeMass T U + 18 * treeMass T U * d) +
                ((degree T c + 1) ^ 2 + ∑ P ∈ parts, starCharge T P) := by ring
          _ ≤ (18 * treeMass T U + 18 * treeMass T U * d) + starCharge T U :=
            Nat.add_le_add_left hstars _
          _ = 18 * treeMass T U * (d + 1) + starCharge T U := by ring
      · have hHc := hH.mono (Q := Qc) subset_union_left
        have hnew := hcent H hHc hboundary
        by_cases hinc : e = c ∨ T.parent e = c
        · exact hnew e he heU hpU hinc
        · obtain ⟨P, hP, heP⟩ := DirectedCertificate.Completion.separatorParts_cover
            T U c heU (fun h => hinc (Or.inl h))
          have hpP : T.parent e ∈ P := (DirectedCertificate.Completion.separatorParts_parent_iff
            T U c hP heU hpU (fun h => hinc (Or.inl h)) (fun h => hinc (Or.inr h)) rfl).mp heP
          have hHP : Consistent G H (Q P) := hH.mono (fun S hS =>
            mem_union_right _ (mem_biUnion.mpr ⟨P, hP, hS⟩))
          apply hcert P hP H hHP _ e he heP hpP
          intro f hf
          rcases separatorPart_boundary T U c hP hf with hb | ⟨hfU, hpfU, hfc⟩
          · exact hboundary f hb
          · exact hnew f (boundary_endpoints T hf).1 hfU hpfU hfc
    · have he : U = ∅ := not_nonempty_iff_eq_empty.mp hne
      subst U
      exact ⟨∅, by simp [treeMass, starCharge], fun _ _ _ _ _ he => (notMem_empty _ he).elim⟩

theorem treeMass_univ (T : TwoRespecting.RootedTree V) :
    treeMass T univ = Fintype.card V + 2 * (Fintype.card V - 1) := by
  simp only [treeMass, sum_add_distrib, sum_const, card_univ, smul_eq_mul, mul_one, sum_degree]

theorem starCharge_univ (T : TwoRespecting.RootedTree V) :
    starCharge T univ = (∑ v : V, (degree T v) ^ 2) +
      4 * (Fintype.card V - 1) + Fintype.card V := by
  have hpoly (v : V) : (degree T v + 1) ^ 2 = (degree T v) ^ 2 + 2 * degree T v + 1 := by ring
  simp only [starCharge, hpoly, sum_add_distrib, ← mul_sum, sum_const, card_univ,
    smul_eq_mul, mul_one, sum_degree]
  ring

/-- The requested degree-sensitive certificate uses one fixed family before all
unrestricted competitors, and includes every fundamental-shore value. -/
theorem exists_degree_certificate (G : WeightedGraph V) (T : TwoRespecting.RootedTree V)
    (tau : V → ℝ) (hn : 1 ≤ Fintype.card V) (hT : FundamentalCorrect G T tau) :
    ∃ Q : Finset (Finset V),
      Q.card ≤ 64 * Fintype.card V * Nat.clog 2 (2 * Fintype.card V) +
        ∑ v : V, (degree T v) ^ 2 ∧ TreeCertificate G T tau Q := by
  let n := Fintype.card V
  let L := Nat.clog 2 (2 * n)
  have hsize : (univ : Finset V).card < 2 ^ L := by
    have hp : 2 * n ≤ 2 ^ L := Nat.le_pow_clog (by decide : 1 < 2) (2 * n)
    have hn' : 0 < n := hn
    change n < 2 ^ L
    exact (by omega : n < 2 * n).trans_le hp
  obtain ⟨Q₀, hQ₀, hcert⟩ := centroid_certificate_rec G T tau hT L univ (pathClosed_univ T) hsize
  refine ⟨Q₀ ∪ fundamentalQueries T, ?_, subset_union_right, fun H hH e he => ?_⟩
  · have hL : 1 ≤ L := Nat.clog_pos (by decide) (by omega)
    have hnL : n ≤ n * L := by simpa using Nat.mul_le_mul_left n hL
    have hmass : treeMass T univ ≤ 3 * n := by rw [treeMass_univ]; omega
    have hml : 18 * treeMass T univ * L ≤ 54 * n * L := by
      have h := Nat.mul_le_mul_right L (Nat.mul_le_mul_left 18 hmass)
      nlinarith
    have hs : starCharge T univ + (n - 1) ≤ (∑ v : V, (degree T v) ^ 2) + 6 * n := by
      rw [starCharge_univ]
      omega
    have hu := card_union_le Q₀ (fundamentalQueries T)
    have hf := fundamentalQueries_card T
    change (Q₀ ∪ fundamentalQueries T).card ≤ 64 * n * L + _
    nlinarith
  · refine ⟨(hH _ (mem_union_right _ (fundamental_mem T he))).trans (hT e he).1, ?_⟩
    apply hcert H (hH.mono subset_union_left) _ e he (mem_univ e) (mem_univ _)
    intro f hf
    have h := (mem_filter.mp hf).2
    exact (h (by simp)).elim

theorem sum_degree_sq_le (T : TwoRespecting.RootedTree V) (D : ℕ)
    (hD : ∀ v, degree T v ≤ D) :
    (∑ v : V, (degree T v) ^ 2) ≤ 2 * (Fintype.card V - 1) * D := by
  calc
    _ ≤ ∑ v : V, degree T v * D := sum_le_sum fun v _ => by
      rw [pow_two]
      exact Nat.mul_le_mul_left _ (hD v)
    _ = _ := by rw [← sum_mul, sum_degree]

end
end CutQueryComplexity.Certificate.GomoryHu

#print axioms CutQueryComplexity.Certificate.GomoryHu.exists_refinement_certificate
#print axioms CutQueryComplexity.Certificate.GomoryHu.frontier_refines_star
#print axioms CutQueryComplexity.Certificate.GomoryHu.exists_centroid_step_certificate
#print axioms CutQueryComplexity.Certificate.GomoryHu.separatorPart_boundary
#print axioms CutQueryComplexity.Certificate.GomoryHu.exists_degree_certificate
#print axioms CutQueryComplexity.Certificate.GomoryHu.sum_degree_sq_le
