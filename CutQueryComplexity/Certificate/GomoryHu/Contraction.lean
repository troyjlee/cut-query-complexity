import CutQueryComplexity.Certificate.GomoryHu.Basic
import CutQueryComplexity.Certificate.FlowCert
import CutQueryComplexity.Certificate.SplittingOff

set_option autoImplicit false

/-! # Certified contraction preserving chosen representatives

The local certificate is applied to the actual quotient that contracts the
outside of a block to a sink. Its queries pull back to original cuts, so no
unknown boundary capacity is treated as public fixed data.
-/

namespace CutQueryComplexity.Certificate.GomoryHu

open Finset WeightedGraph
open scoped Classical
noncomputable section

variable {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]

def RootProtected (G : WeightedGraph V) (K : Finset V) (v : V) : Prop :=
  v ∈ K ∧ ∀ A, A ⊆ K → v ∈ A → G.cut K ≤ G.cut A

theorem RootProtected.of_minCut {G : WeightedGraph V} {K : Finset V} {v c : V}
    (h : IsSTMinCut G v c K) : RootProtected G K v :=
  ⟨h.1, fun A hA hv => h.2.2 A hv (fun hc => h.2.1 (hA hc))⟩

theorem rootProtected_singleton (G : WeightedGraph V) (v : V) :
    RootProtected G {v} v := by
  refine ⟨mem_singleton_self v, fun A hA hv => ?_⟩
  have he : A = {v} := subset_antisymm hA (singleton_subset_iff.mpr hv)
  rw [he]

def roundBlock (K : Finset V) (v : V) (S : Finset V) : Finset V :=
  if v ∈ S then S ∪ K else S \ K

theorem RootProtected.round_cut_le {G : WeightedGraph V} {K : Finset V} {v : V}
    (h : RootProtected G K v) (S : Finset V) : G.cut (roundBlock K v S) ≤ G.cut S := by
  by_cases hv : v ∈ S
  · have h₁ := G.cut_submodular S K
    have h₂ := h.2 (S ∩ K) inter_subset_right (mem_inter.mpr ⟨hv, h.1⟩)
    simp only [roundBlock, hv, ite_true]
    linarith
  · have h₁ := cut_posimodular_eq G S K
    have h₂ := h.2 (K \ S) sdiff_subset (mem_sdiff.mpr ⟨h.1, hv⟩)
    have h₃ := G.cross_nonneg (S ∩ K) (S ∪ K)ᶜ
    simp only [roundBlock, hv, ite_false]
    linarith

theorem roundBlock_mem_of_compatible (K : Finset V) (v : V) (S : Finset V)
    {x : V} (hx : x ∉ K ∨ x = v) : x ∈ roundBlock K v S ↔ x ∈ S := by
  rcases hx with hx | rfl
  · by_cases hv : v ∈ S <;> simp [roundBlock, hv, hx]
  · by_cases hxS : x ∈ S <;> simp [roundBlock, hxS]

theorem roundBlock_uniform (K : Finset V) (v : V) (S : Finset V) :
    K ⊆ roundBlock K v S ∨ Disjoint K (roundBlock K v S) := by
  by_cases hv : v ∈ S
  · left; simp only [roundBlock, hv, ite_true]; exact subset_union_right
  · right
    apply disjoint_left.mpr
    intro x hx hxR
    have := mem_sdiff.mp (show x ∈ S \ K from by simpa [roundBlock, hv] using hxR)
    exact this.2 hx

/-- Simultaneously round disjoint blocks without undoing an earlier rounding. -/
theorem exists_round_blocks (G : WeightedGraph V) (I : Finset B)
    (K : B → Finset V) (r : B → V) :
    (∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (K i) (K j)) →
    (∀ i ∈ I, RootProtected G (K i) (r i)) →
    ∀ S : Finset V, ∃ R : Finset V, G.cut R ≤ G.cut S ∧
      (∀ x, (∀ i ∈ I, x ∉ K i ∨ x = r i) → (x ∈ R ↔ x ∈ S)) ∧
      ∀ i ∈ I, K i ⊆ R ∨ Disjoint (K i) R := by
  induction I using Finset.induction_on with
  | empty =>
    intro _ _ S
    exact ⟨S, le_rfl, fun _ _ => Iff.rfl, by simp⟩
  | @insert i I hi ih =>
    intro hdis hroot S
    have hdisI : ∀ j ∈ I, ∀ k ∈ I, j ≠ k → Disjoint (K j) (K k) :=
      fun j hj k hk hne => hdis j (mem_insert_of_mem hj) k (mem_insert_of_mem hk) hne
    have hrootI : ∀ j ∈ I, RootProtected G (K j) (r j) :=
      fun j hj => hroot j (mem_insert_of_mem hj)
    obtain ⟨R, hRcut, hRmem, hRuniform⟩ := ih hdisI hrootI (roundBlock (K i) (r i) S)
    have hfix : ∀ x ∈ K i, (x ∈ R ↔ x ∈ roundBlock (K i) (r i) S) := by
      intro x hx
      apply hRmem x
      intro j hj
      left
      have hij : i ≠ j := by intro he; subst j; exact hi hj
      exact fun hxj => disjoint_left.mp
        (hdis i (mem_insert_self _ _) j (mem_insert_of_mem hj) hij) hx hxj
    refine ⟨R, hRcut.trans ((hroot i (mem_insert_self _ _)).round_cut_le S), ?_, ?_⟩
    · intro x hx
      exact (hRmem x (fun j hj => hx j (mem_insert_of_mem hj))).trans
        (roundBlock_mem_of_compatible _ _ _ (hx i (mem_insert_self _ _)))
    · intro j hj
      rcases mem_insert.mp hj with hji | hj
      · subst j
        rcases roundBlock_uniform (K i) (r i) S with hsub | hd
        · exact Or.inl (fun x hx => (hfix x hx).mpr (hsub hx))
        · right
          exact disjoint_left.mpr fun x hx hxR => disjoint_left.mp hd hx ((hfix x hx).mp hxR)
      · exact hRuniform j hj

def pullQueries (pi : V → B) (Q : Finset (Finset B)) : Finset (Finset V) :=
  Q.image (WeightedGraph.pull pi)

theorem pullQueries_card (pi : V → B) (Q : Finset (Finset B)) :
    (pullQueries pi Q).card ≤ Q.card := card_image_le

theorem consistent_contract {G H : WeightedGraph V} (pi : V → B)
    {Q : Finset (Finset B)} (h : Consistent G H (pullQueries pi Q)) :
    Consistent (G.contract pi) (H.contract pi) Q := by
  intro S hS
  rw [cut_contract, cut_contract]
  exact h _ (mem_image_of_mem _ hS)

/-- An actual quotient cut no more expensive than any original shore, preserving
the side of every chosen representative. -/
theorem exists_quotient_round (G : WeightedGraph V) (pi : V → B) (r : B → V)
    (hr : ∀ b, pi (r b) = b) (hroot : ∀ b, RootProtected G (fiber pi b) (r b))
    (S : Finset V) :
    ∃ Q : Finset B, (G.contract pi).cut Q ≤ G.cut S ∧
      ∀ b, b ∈ Q ↔ r b ∈ S := by
  have hdis : ∀ b ∈ (univ : Finset B), ∀ c ∈ (univ : Finset B),
      b ≠ c → Disjoint (fiber pi b) (fiber pi c) := by
    intro b _ c _ hbc
    refine disjoint_left.mpr fun x hx hy => hbc ?_
    exact ((mem_fiber pi b x).mp hx).symm.trans ((mem_fiber pi c x).mp hy)
  obtain ⟨R, hR, hmem, huniform⟩ :=
    exists_round_blocks G univ (fiber pi) r hdis (fun b _ => hroot b) S
  let Q : Finset B := univ.filter fun b => r b ∈ R
  have hpull : pull pi Q = R := by
    ext x
    simp only [mem_pull, Q, mem_filter, mem_univ, true_and]
    have hx : x ∈ fiber pi (pi x) := by simp
    have hy : r (pi x) ∈ fiber pi (pi x) := by simp [hr]
    rcases huniform (pi x) (mem_univ _) with hsub | hd
    · exact ⟨fun _ => hsub hx, fun _ => hsub hy⟩
    · have hnx := fun h => disjoint_left.mp hd hx h
      have hny := fun h => disjoint_left.mp hd hy h
      exact ⟨fun h => (hny h).elim, fun h => (hnx h).elim⟩
  refine ⟨Q, ?_, fun b => ?_⟩
  · rw [cut_contract, hpull]
    exact hR
  · simp only [Q, mem_filter, mem_univ, true_and]
    apply hmem (r b)
    intro c _
    by_cases hbc : b = c
    · subst c; exact Or.inr rfl
    · left; simpa [hr] using hbc

/-- Minimum quotient shores lift to genuine original minimum shores. -/
theorem lift_minCut {G : WeightedGraph V} (pi : V → B) (r : B → V)
    (hr : ∀ b, pi (r b) = b) (hroot : ∀ b, RootProtected G (fiber pi b) (r b))
    {s t : B} {Q : Finset B} (hQ : IsSTMinCut (G.contract pi) s t Q) :
    IsSTMinCut G (r s) (r t) (pull pi Q) := by
  refine ⟨by simpa [hr] using hQ.1, by simpa [hr] using hQ.2.1, ?_⟩
  intro S hs ht
  obtain ⟨R, hR, hmem⟩ := exists_quotient_round G pi r hr hroot S
  rw [← cut_contract]
  exact (hQ.2.2 R ((hmem s).mpr hs) (fun h => ht ((hmem t).mp h))).trans hR

/-- Keep each block vertex and contract its complement to one auxiliary sink. -/
def insideMap (K : Finset V) (x : V) : Option {u : V // u ∈ K} :=
  if hx : x ∈ K then some ⟨x, hx⟩ else none

@[simp] theorem insideMap_some (K : Finset V) (u : {u : V // u ∈ K}) :
    insideMap K u.val = some u := by simp [insideMap, u.property]

def insideShore (K A : Finset V) : Finset (Option {u : V // u ∈ K}) :=
  univ.filter fun q => match q with
    | none => False
    | some u => u.val ∈ A

@[simp] theorem none_not_mem_insideShore (K A : Finset V) :
    none ∉ insideShore K A := by simp [insideShore]

@[simp] theorem some_mem_insideShore (K A : Finset V) (u : {u : V // u ∈ K}) :
    some u ∈ insideShore K A ↔ u.val ∈ A := by simp [insideShore]

theorem pull_insideShore (K A : Finset V) (hA : A ⊆ K) :
    pull (insideMap K) (insideShore K A) = A := by
  ext x
  by_cases hx : x ∈ K
  · simp [insideMap, hx]
  · have hxA : x ∉ A := fun h => hx (hA h)
    simp [insideMap, hx, hxA]

theorem pull_inside_subset (K : Finset V) {Q : Finset (Option {u : V // u ∈ K})}
    (hQ : none ∉ Q) : pull (insideMap K) Q ⊆ K := by
  intro x hx
  by_contra hxK
  have hm := (mem_pull (insideMap K) Q x).mp hx
  exact hQ (by simpa [insideMap, hxK] using hm)

/-- The protected-block property itself has an actual local query certificate.
The quotient is formed anew for every competitor; no hidden capacity is frozen. -/
theorem exists_rootProtected_certificate (G : WeightedGraph V) (K : Finset V) (v : V)
    (hp : RootProtected G K v) :
    ∃ Q : Finset (Finset V), K ∈ Q ∧ Q.card ≤ 8 * (K.card + 1) + 2 ∧
      ∀ H : WeightedGraph V, Consistent G H Q → RootProtected H K v := by
  let pi := insideMap K
  let r : Option {u : V // u ∈ K} := some ⟨v, hp.1⟩
  let J := G.contract pi
  have hr : pi v = r := by simp [pi, r, insideMap, hp.1]
  have hdis : Disjoint ({r} : Finset (Option {u : V // u ∈ K})) {none} := by
    simp [r]
  obtain ⟨T, hTr, hTz, Q₀, hTQ, hQ₀, hcert⟩ := exists_cutCert J {r} {none} hdis
  have hrT : r ∈ T := hTr (mem_singleton_self _)
  have hzT : none ∉ T := fun h => disjoint_left.mp hTz h (mem_singleton_self _)
  have hvT : v ∈ pull pi T := by
    apply (mem_pull pi T v).mpr
    rw [hr]
    exact hrT
  have hTK : pull pi T ⊆ K := pull_inside_subset K hzT
  have hrepK : {r} ⊆ insideShore K K := by simp [r, hp.1]
  have hnoneK : Disjoint (insideShore K K) {none} := by simp
  have hself : Consistent J J Q₀ := fun _ _ => rfl
  have hval : J.cut T = G.cut K := by
    refine le_antisymm ?_ ?_
    · have h := hcert J hself (insideShore K K) hrepK hnoneK
      simpa [J, pi, cut_contract, pull_insideShore K K (subset_refl K)] using h
    · have h := hp.2 (pull pi T) hTK hvT
      simpa [J, cut_contract] using h
  let Q := insert K (pullQueries pi Q₀)
  refine ⟨Q, mem_insert_self _ _, ?_, fun H hH => ⟨hp.1, fun A hA hvA => ?_⟩⟩
  · have hc : Fintype.card (Option {u : V // u ∈ K}) = K.card + 1 := by simp
    have h₁ := card_insert_le K (pullQueries pi Q₀)
    have h₂ := pullQueries_card pi Q₀
    rw [hc] at hQ₀
    dsimp [Q]
    omega
  · have hlocal := consistent_contract pi (hH.mono (subset_insert K (pullQueries pi Q₀)))
    have hrepA : {r} ⊆ insideShore K A := by simp [r, hvA]
    have hnoneA : Disjoint (insideShore K A) {none} := by simp
    have hbound := hcert (H.contract pi) hlocal (insideShore K A) hrepA hnoneA
    have hTv : (H.contract pi).cut T = G.cut K := (hlocal T hTQ).trans hval
    have hKv : H.cut K = G.cut K := hH K (mem_insert_self _ _)
    rw [hTv, cut_contract, show pull pi (insideShore K A) = A from pull_insideShore K A hA]
      at hbound
    rw [hKv]
    exact hbound

/-- A genuine finite partition with a chosen representative in every block. -/
structure BlockPartition (V B : Type) [Fintype V] [DecidableEq V] where
  block : B → Finset V
  root : B → V
  root_mem : ∀ b, root b ∈ block b
  disjoint : ∀ b c, b ≠ c → Disjoint (block b) (block c)
  cover : ∀ x : V, ∃ b, x ∈ block b

namespace BlockPartition

variable (P : BlockPartition V B)

def projection (x : V) : B := (P.cover x).choose

theorem projection_mem (x : V) : x ∈ P.block (P.projection x) := (P.cover x).choose_spec

theorem projection_eq_iff (x : V) (b : B) : P.projection x = b ↔ x ∈ P.block b := by
  constructor
  · intro h
    rw [← h]
    exact P.projection_mem x
  · intro h
    by_contra hne
    exact disjoint_left.mp (P.disjoint _ _ hne) (P.projection_mem x) h

@[simp] theorem projection_root (b : B) : P.projection (P.root b) = b :=
  (P.projection_eq_iff _ _).mpr (P.root_mem b)

@[simp] theorem fiber_projection (b : B) : fiber P.projection b = P.block b := by
  ext x
  exact (mem_fiber _ _ _).trans (P.projection_eq_iff x b)

theorem root_injective : Function.Injective P.root := by
  intro b c h
  have := congrArg P.projection h
  simpa only [P.projection_root] using this

include P in
theorem card_le : Fintype.card B ≤ Fintype.card V := Fintype.card_le_of_injective _ P.root_injective

theorem sum_card : (∑ b : B, (P.block b).card) = Fintype.card V := by
  have hd : ((univ : Finset B) : Set B).PairwiseDisjoint P.block :=
    fun b _ c _ hbc => P.disjoint b c hbc
  rw [← card_biUnion hd]
  change (univ.biUnion P.block).card = (univ : Finset V).card
  congr 1
  ext x
  simp only [mem_biUnion, mem_univ, true_and, iff_true]
  exact P.cover x

/-- All representative-protection properties have a single linear-size certificate. -/
theorem exists_protection_certificate (G : WeightedGraph V)
    (hp : ∀ b, RootProtected G (P.block b) (P.root b)) :
    ∃ Q : Finset (Finset V), Q.card ≤ 18 * Fintype.card V ∧
      ∀ H : WeightedGraph V, Consistent G H Q →
        ∀ b, RootProtected H (P.block b) (P.root b) := by
  have hex := fun b => exists_rootProtected_certificate G (P.block b) (P.root b) (hp b)
  choose Q hmem hcard hcert using hex
  refine ⟨univ.biUnion Q, ?_, fun H hH b => hcert b H (hH.mono ?_)⟩
  · calc
      (univ.biUnion Q).card ≤ ∑ b : B, (Q b).card := card_biUnion_le
      _ ≤ ∑ b : B, (8 * ((P.block b).card + 1) + 2) := sum_le_sum fun b _ => hcard b
      _ = ∑ b : B, (8 * (P.block b).card + 10) :=
        sum_congr rfl fun b _ => by ring
      _ = 8 * Fintype.card V + 10 * Fintype.card B := by
        rw [sum_add_distrib, ← mul_sum, P.sum_card]
        simp [Nat.mul_comm]
      _ ≤ 18 * Fintype.card V := by nlinarith [P.card_le]
  · intro S hS
    exact mem_biUnion.mpr ⟨b, mem_univ b, hS⟩

/-- Learn the quotient completely and certify actual representative-preserving
contraction. The quadratic term is explicit; no weighted-star oracle is used. -/
theorem exists_learned_quotient_certificate (G : WeightedGraph V)
    (hp : ∀ b, RootProtected G (P.block b) (P.root b)) :
    ∃ Q : Finset (Finset V),
      Q.card ≤ 18 * Fintype.card V + (Fintype.card B) ^ 2 ∧
      ∀ H : WeightedGraph V, Consistent G H Q →
        (H.contract P.projection = G.contract P.projection) ∧
        ∀ b, RootProtected H (P.block b) (P.root b) := by
  obtain ⟨Q₀, hQ₀, hcert⟩ := P.exists_protection_certificate G hp
  refine ⟨Q₀ ∪ pullQueries P.projection (allPairQueries B), ?_, fun H hH => ?_⟩
  · exact (card_union_le _ _).trans (Nat.add_le_add hQ₀
      ((pullQueries_card _ _).trans allPairQueries_card))
  · exact ⟨eq_of_consistent_allPairQueries
      (consistent_contract _ (hH.mono subset_union_right)), hcert H (hH.mono subset_union_left)⟩

theorem lift_minCut {G : WeightedGraph V}
    (hp : ∀ b, RootProtected G (P.block b) (P.root b)) {s t : B} {Q : Finset B}
    (hQ : IsSTMinCut (G.contract P.projection) s t Q) :
    IsSTMinCut G (P.root s) (P.root t) (pull P.projection Q) := by
  apply GomoryHu.lift_minCut P.projection P.root P.projection_root _ hQ
  intro b
  simpa only [P.fiber_projection] using hp b

end BlockPartition

end
end CutQueryComplexity.Certificate.GomoryHu

#print axioms CutQueryComplexity.Certificate.GomoryHu.RootProtected.round_cut_le
#print axioms CutQueryComplexity.Certificate.GomoryHu.exists_round_blocks
#print axioms CutQueryComplexity.Certificate.GomoryHu.exists_quotient_round
#print axioms CutQueryComplexity.Certificate.GomoryHu.lift_minCut
#print axioms CutQueryComplexity.Certificate.GomoryHu.exists_rootProtected_certificate
#print axioms CutQueryComplexity.Certificate.GomoryHu.BlockPartition.exists_protection_certificate
#print axioms CutQueryComplexity.Certificate.GomoryHu.BlockPartition.exists_learned_quotient_certificate
