import CutQueryComplexity.StarContraction2022.Recovery.LearnBucket
import CutQueryComplexity.StarContraction2022.Probability.ConditionalRatio
import CutQueryComplexity.Primitive.BinarySearch
import CutQueryComplexity.Model.RandomizedReduction
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Public recovery of every row

The public program validates derived bilinear counts and its measured degree
partition. The tiny-row fallback uses actual count-guided binary queries and
uniform ranks without replacement. Finite expected-cost and learned-row distribution proofs
compose the bucket process, fallback and three-original-cut adapter. No hidden
matrix occurs in a query-program constructor.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CutQueryComplexity.StarContraction2022.Recovery

open Finset CutQueryComplexity.Probability
open scoped Classical NNReal ENNReal
noncomputable section

section OriginalQueries

variable {V R C : Type} [Fintype V] [DecidableEq V]
  [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C]

/-- The matrix is used only in honest-input proofs. The program takes the two
public embeddings, never this hidden Boolean table. -/
def graphMatrix (row : R ↪ V) (col : C ↪ V) (G : SimpleInput V) : BooleanMatrix R C :=
  fun u v => decide ((G.w (row u) (col v) : ℕ) = 1)

theorem graphMatrix_entry (row : R ↪ V) (col : C ↪ V) (G : SimpleInput V) (u : R) (v : C) :
    (if graphMatrix row col G u v then (1 : ℝ) else 0) = G.toWeighted.w (row u) (col v) := by
  have hb := (G.w (row u) (col v)).isLt
  have hc : (G.w (row u) (col v) : ℕ) = 0 ∨ (G.w (row u) (col v) : ℕ) = 1 := by omega
  rcases hc with hc | hc <;> simp [graphMatrix,CapacityGraph.toWeighted,hc]

theorem graphMatrix_bilinear (row : R ↪ V) (col : C ↪ V) (G : SimpleInput V)
    (q : BipartiteQuery R C) :
    (bilinear (graphMatrix row col G) q : ℝ) = G.toWeighted.cross (q.1.map row) (q.2.map col) := by
  simp only [bilinear,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,
    WeightedGraph.cross,Finset.sum_map]
  apply sum_congr rfl
  intro u _
  apply sum_congr rfl
  intro v _
  exact graphMatrix_entry row col G u v

theorem embedded_disjoint (row : R ↪ V) (col : C ↪ V)
    (hdisjoint : ∀ u v, row u ≠ col v) (X : Finset R) (Y : Finset C) :
    Disjoint (X.map row) (Y.map col) := by
  apply disjoint_left.mpr
  intro v hvX hvY
  obtain ⟨u,_,hu⟩ := mem_map.mp hvX
  obtain ⟨w,_,hw⟩ := mem_map.mp hvY
  exact hdisjoint u w (hu.trans hw.symm)

/-- Three original cuts, without incorrectly applying a bilinear range bound
to any individual original cut answer. -/
def originalBilinearCall (row : R ↪ V) (col : C ↪ V) (q : BipartiteQuery R C) :
    DTree (Finset V) ℝ ℝ 3 := crossQuery (q.1.map row) (q.2.map col)

def originalBilinearRead (row : R ↪ V) (col : C ↪ V) (read : Finset V → ℝ)
    (q : BipartiteQuery R C) : ℝ :=
  (read (q.1.map row)+read (q.2.map col)-read ((q.1.map row)∪(q.2.map col)))/2

theorem originalBilinearCall_run (row : R ↪ V) (col : C ↪ V) (read : Finset V → ℝ)
    (q : BipartiteQuery R C) :
    DTree.run read (originalBilinearCall row col q) = (originalBilinearRead row col read q,3) := rfl

theorem originalBilinearRead_honest (row : R ↪ V) (col : C ↪ V)
    (hdisjoint : ∀ u v, row u ≠ col v) (G : SimpleInput V) (q : BipartiteQuery R C) :
    originalBilinearRead row col G.toWeighted.cut q = (bilinear (graphMatrix row col G) q : ℝ) := by
  have h := crossQuery_run G.toWeighted (embedded_disjoint row col hdisjoint q.1 q.2)
  exact (congrArg Prod.fst h).trans (graphMatrix_bilinear row col G q).symm

/-- Explicit range validation is performed on the derived cross answer. -/
def validatedOriginalBilinearCall (row : R ↪ V) (col : C ↪ V) (q : BipartiteQuery R C) :
    DTree (Finset V) ℝ (Option (Fin (q.1.card*q.2.card+1))) 3 :=
  (originalBilinearCall row col q).map (validateCount (q.1.card*q.2.card))

theorem validatedOriginalBilinearCall_honest (row : R ↪ V) (col : C ↪ V)
    (hdisjoint : ∀ u v, row u ≠ col v) (G : SimpleInput V) (q : BipartiteQuery R C) :
    (validatedOriginalBilinearCall row col q).eval G.toWeighted.cut =
      some ⟨bilinear (graphMatrix row col G) q,Nat.lt_succ_of_le (bilinear_le _ _)⟩ := by
  rw [validatedOriginalBilinearCall,DTree.eval_map]
  change validateCount _ (originalBilinearRead row col G.toWeighted.cut q) = _
  rw [originalBilinearRead_honest row col hdisjoint G q]
  exact validateCount_of_nat _ _ (bilinear_le _ _)

theorem validatedOriginalBilinearCall_reject (row : R ↪ V) (col : C ↪ V)
    (read : Finset V → ℝ) (q : BipartiteQuery R C)
    (h : ¬∃ j : Fin (q.1.card*q.2.card+1),
      ((j : ℕ) : ℝ) = originalBilinearRead row col read q) :
    (validatedOriginalBilinearCall row col q).eval read = none := by
  simp only [validatedOriginalBilinearCall,DTree.eval_map]
  change validateCount _ (originalBilinearRead row col read q) = none
  simp only [validateCount,dite_eq_right h]

end OriginalQueries

section Simulation

variable {I A J B O : Type} {q k : ℕ}

/-- Exact cost multiplication for actual deterministic query adapters. The
concrete original-cut adapter below discharges this local contract with 3. -/
theorem substitute_run_exact (call : J → DTree I A B k) (read : I → A) (virtual : J → B)
    (hcall : ∀ j, DTree.run read (call j) = (virtual j,k)) (T : RTree J B O q) :
    RTree.run read (T.substitute call) =
      (RTree.run virtual T).map (fun out => (out.1,out.2*k)) := by
  induction q with
  | zero => simp [RTree.substitute,RTree.run_pure,RTree.run,PMF.map_comp,Function.comp_def]
  | succ q ih =>
      simp only [RTree.substitute,RTree.run_mix,PMF.bind_map,Function.comp_def,
        RTree.run,PMF.map_bind]
      congr 1
      funext action
      rcases action with o | ⟨j,next⟩
      · simp [RTree.run_pure,PMF.pure_map]
      · simp only [RTree.run_cast,RTree.run_bind,RTree.run_ofDeterministic,hcall,
          PMF.pure_bind,ih,PMF.map_comp,Function.comp_def]
        congr 1
        funext out
        congr 1
        ring

variable {V R C : Type} [Fintype V] [DecidableEq V]
  [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C]

def simulateOriginal (row : R ↪ V) (col : C ↪ V) (T : RTree (BipartiteQuery R C) ℝ O q) :
    RTree (Finset V) ℝ O (q*3) := T.substitute (originalBilinearCall row col)

theorem simulateOriginal_run (row : R ↪ V) (col : C ↪ V)
    (T : RTree (BipartiteQuery R C) ℝ O q) (read : Finset V → ℝ) :
    RTree.run read (simulateOriginal row col T) =
      (RTree.run (originalBilinearRead row col read) T).map (fun out => (out.1,out.2*3)) :=
  substitute_run_exact _ _ _ (originalBilinearCall_run row col read) T

theorem simulateOriginal_eval (row : R ↪ V) (col : C ↪ V)
    (T : RTree (BipartiteQuery R C) ℝ O q) (read : Finset V → ℝ) :
    (simulateOriginal row col T).eval read = T.eval (originalBilinearRead row col read) := by
  rw [RTree.eval,simulateOriginal_run,PMF.map_comp]
  rfl

theorem simulateOriginal_expected (row : R ↪ V) (col : C ↪ V)
    (T : RTree (BipartiteQuery R C) ℝ O q) (read : Finset V → ℝ) :
    (simulateOriginal row col T).expectedQueries read =
      3*T.expectedQueries (originalBilinearRead row col read) := by
  change expect (RTree.run read (simulateOriginal row col T)) (fun out => (out.2 : ℝ≥0∞)) = _
  rw [simulateOriginal_run,expect_map]
  simp only [Nat.cast_mul,Nat.cast_ofNat,expect_mul_const]
  exact mul_comm _ _

theorem simulateOriginal_every_oracle (row : R ↪ V) (col : C ↪ V)
    (T : RTree (BipartiteQuery R C) ℝ O q) (read : Finset V → ℝ) {out : O × ℕ}
    (hout : out ∈ (RTree.run read (simulateOriginal row col T)).support) : out.2 ≤ q*3 :=
  RTree.cost_le _ _ hout

end Simulation

section UniformRank

variable {R C : Type} [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C]

def remainingNeighbors (row : C → Bool) (known U : Finset C) : Finset C :=
  (U \ known).filter fun c => row c

theorem remainingNeighbors_split (row : C → Bool) (known U : Finset C) (m : ℕ) :
    (remainingNeighbors row known (Split.left m U)).card +
      (remainingNeighbors row known (U \ Split.left m U)).card =
    (remainingNeighbors row known U).card := by
  have hunion : remainingNeighbors row known (Split.left m U) ∪
      remainingNeighbors row known (U \ Split.left m U) = remainingNeighbors row known U := by
    ext c
    have hsub := Split.left_subset m U
    simp only [remainingNeighbors,mem_union,mem_filter,mem_sdiff]
    constructor
    · rintro (⟨⟨hc,hn⟩,hr⟩ | ⟨⟨⟨hc,_⟩,hn⟩,hr⟩)
      · exact ⟨⟨hsub hc,hn⟩,hr⟩
      · exact ⟨⟨hc,hn⟩,hr⟩
    · rintro ⟨⟨hc,hn⟩,hr⟩
      by_cases hl : c ∈ Split.left m U
      · exact Or.inl ⟨⟨hl,hn⟩,hr⟩
      · exact Or.inr ⟨⟨⟨hc,hl⟩,hn⟩,hr⟩
  have hdisjoint : Disjoint (remainingNeighbors row known (Split.left m U))
      (remainingNeighbors row known (U \ Split.left m U)) := by
    apply disjoint_left.mpr
    intro c hc hd
    exact ((mem_sdiff.mp (mem_filter.mp hd).1).1 |> mem_sdiff.mp).2
      (mem_sdiff.mp (mem_filter.mp hc).1).1
  rw [← card_union_of_disjoint hdisjoint,hunion]

/-- Public rank search. Each reply is validated against the queried half's
size; known selected neighbors are subtracted locally before comparing rank. -/
def rankSearch (u : R) (known : Finset C) : (depth : ℕ) → Finset C → ℕ →
    DTree (BipartiteQuery R C) ℝ (Option C) depth
  | 0,U,_ => U.toList.head?
  | depth+1,U,rank =>
      let L := Split.left (2^depth) U
      DTree.query ({u},L) fun answer =>
        match validateCount L.card answer with
        | none => DTree.pure none
        | some count =>
            if (known ∩ L).card ≤ count.val then
              let available := count.val-(known ∩ L).card
              if rank < available then rankSearch u known depth L rank
              else rankSearch u known depth (U \ L) (rank-available)
            else DTree.pure none

/-- Proof-side exact rank selector for the same public recursion. It is never
used to select a query, random rank, or program output using the hidden row. -/
def semanticRank (row : C → Bool) (known : Finset C) : ℕ → Finset C → ℕ → Option C
  | 0,U,_ => U.toList.head?
  | depth+1,U,rank =>
      let L := Split.left (2^depth) U
      let available := (remainingNeighbors row known L).card
      if rank < available then semanticRank row known depth L rank
      else semanticRank row known depth (U \ L) (rank-available)

theorem sampleCount_sub_known (row : C → Bool) (known U : Finset C)
    (hknown : ∀ c ∈ known, row c = true) :
    (known ∩ U).card ≤ sampleCount row U ∧
      sampleCount row U-(known ∩ U).card = (remainingNeighbors row known U).card := by
  have hsub : known ∩ U ⊆ U.filter fun c => row c := by
    intro c hc
    exact mem_filter.mpr ⟨(mem_inter.mp hc).2,hknown c (mem_inter.mp hc).1⟩
  have he : (U.filter (fun c => row c)) \ (known ∩ U) = remainingNeighbors row known U := by
    ext c
    simp only [mem_sdiff,mem_filter,mem_inter,remainingNeighbors]
    tauto
  rw [sampleCount_eq_filter_card]
  exact ⟨card_le_card hsub,by rw [← card_sdiff_of_subset hsub,he]⟩

theorem rankSearch_eval (M : BooleanMatrix R C) (u : R) (known : Finset C)
    (hknown : ∀ c ∈ known, M u c = true) (depth : ℕ) (U : Finset C) (rank : ℕ) :
    (rankSearch u known depth U rank).eval (fun q => (bilinear M q : ℝ)) =
      semanticRank (M u) known depth U rank := by
  induction depth generalizing U rank with
  | zero => rfl
  | succ depth ih =>
      have hc : bilinear M ({u},Split.left (2^depth) U) = sampleCount (M u) (Split.left (2^depth) U) := by
        simp [bilinear,sampleCount]
      rw [rankSearch,DTree.eval_query,hc,
        validateCount_of_nat _ _ (sampleCount_le_card _ _)]
      obtain ⟨hle,he⟩ := sampleCount_sub_known (M u) known (Split.left (2^depth) U) hknown
      simp only [ite_eq_left hle,he,semanticRank]
      split <;> exact ih _ _

theorem semanticRank_correct (row : C → Bool) (known : Finset C) (depth : ℕ)
    (U : Finset C) (rank : ℕ) (hcard : U.card ≤ 2^depth)
    (hrank : rank < (remainingNeighbors row known U).card) :
    ∃ c, semanticRank row known depth U rank = some c ∧ c ∈ remainingNeighbors row known U := by
  induction depth generalizing U rank with
  | zero =>
      have hN : (remainingNeighbors row known U).Nonempty := card_pos.mp (by omega)
      obtain ⟨c,hc⟩ := hN
      have hcU : c ∈ U := (mem_sdiff.mp (mem_filter.mp hc).1).1
      have hU : U = {c} := eq_singleton_iff_unique_mem.mpr
        ⟨hcU,fun x hx => (card_le_one.mp (by simpa using hcard)) x hx c hcU⟩
      exact ⟨c,by simp [semanticRank,hU],hc⟩
  | succ depth ih =>
      let L := Split.left (2^depth) U
      have hL : L.card ≤ 2^depth := Split.card_left_le _ _
      have hRight : (U \ L).card ≤ 2^depth := Split.card_right_le
        (by simpa only [pow_succ,Nat.mul_comm] using hcard)
      have hsplit := remainingNeighbors_split row known U (2^depth)
      change (remainingNeighbors row known L).card +
        (remainingNeighbors row known (U \ L)).card = (remainingNeighbors row known U).card at hsplit
      change ∃ c, (if rank < (remainingNeighbors row known L).card then
          semanticRank row known depth L rank
        else semanticRank row known depth (U \ L) (rank-(remainingNeighbors row known L).card)) =
          some c ∧ c ∈ remainingNeighbors row known U
      by_cases hleft : rank < (remainingNeighbors row known L).card
      · obtain ⟨c,he,hc⟩ := ih L rank hL hleft
        refine ⟨c,by simpa only [ite_eq_left hleft] using he,?_⟩
        obtain ⟨hcLK,hcrow⟩ := mem_filter.mp hc
        obtain ⟨hcL,hcn⟩ := mem_sdiff.mp hcLK
        exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨Split.left_subset _ _ hcL,hcn⟩,hcrow⟩
      · have hr : rank-(remainingNeighbors row known L).card <
            (remainingNeighbors row known (U \ L)).card := by omega
        obtain ⟨c,he,hc⟩ := ih (U \ L) _ hRight hr
        refine ⟨c,by simpa only [ite_eq_right hleft] using he,?_⟩
        obtain ⟨hcRK,hcrow⟩ := mem_filter.mp hc
        obtain ⟨hcR,hcn⟩ := mem_sdiff.mp hcRK
        exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨(mem_sdiff.mp hcR).1,hcn⟩,hcrow⟩

/-- The actual binary query program returns a new true neighbor for every
valid rank in the remaining row. -/
theorem rankSearch_correct (M : BooleanMatrix R C) (u : R) (known U : Finset C)
    (hknown : ∀ c ∈ known, M u c = true) (depth rank : ℕ)
    (hcard : U.card ≤ 2^depth) (hrank : rank < (remainingNeighbors (M u) known U).card) :
    ∃ c, (rankSearch u known depth U rank).eval (fun q => (bilinear M q : ℝ)) = some c ∧
      c ∈ U ∧ c ∉ known ∧ M u c = true := by
  obtain ⟨c,he,hc⟩ := semanticRank_correct (M u) known depth U rank hcard hrank
  refine ⟨c,(rankSearch_eval M u known hknown depth U rank).trans he,?_⟩
  simpa only [remainingNeighbors,mem_filter,mem_sdiff,and_assoc] using hc

theorem rankSearch_every_oracle (u : R) (known U : Finset C) (depth rank : ℕ)
    (read : BipartiteQuery R C → ℝ) : (rankSearch u known depth U rank).cost read ≤ depth :=
  DTree.cost_le _ _


/-- Different valid ranks lead to different returned neighbors in the actual
balanced partition order, even though Finset.toList has no external ordering. -/
theorem semanticRank_injective (row : C → Bool) (known : Finset C) (depth : ℕ)
    (U : Finset C) (hcard : U.card ≤ 2^depth) {a b : ℕ}
    (ha : a < (remainingNeighbors row known U).card)
    (hb : b < (remainingNeighbors row known U).card)
    (he : semanticRank row known depth U a = semanticRank row known depth U b) : a = b := by
  induction depth generalizing U a b with
  | zero =>
      have hsub : remainingNeighbors row known U ⊆ U := by
        intro c hc
        exact (mem_sdiff.mp (mem_filter.mp hc).1).1
      have hN := card_le_card hsub
      norm_num at hcard
      omega
  | succ depth ih =>
      let L := Split.left (2^depth) U
      let d := (remainingNeighbors row known L).card
      have hL : L.card ≤ 2^depth := Split.card_left_le _ _
      have hRight : (U \ L).card ≤ 2^depth := Split.card_right_le
        (by simpa only [pow_succ,Nat.mul_comm] using hcard)
      have hsplit := remainingNeighbors_split row known U (2^depth)
      change d+(remainingNeighbors row known (U \ L)).card =
        (remainingNeighbors row known U).card at hsplit
      change (if a < d then semanticRank row known depth L a else
        semanticRank row known depth (U \ L) (a-d)) =
        (if b < d then semanticRank row known depth L b else
          semanticRank row known depth (U \ L) (b-d)) at he
      by_cases haL : a < d
      · by_cases hbL : b < d
        · simp only [ite_eq_left haL,ite_eq_left hbL] at he
          exact ih L hL haL hbL he
        · simp only [ite_eq_left haL,ite_eq_right hbL] at he
          have hbR : b-d < (remainingNeighbors row known (U \ L)).card := by omega
          obtain ⟨c,hc,hcN⟩ := semanticRank_correct row known depth L a hL haL
          obtain ⟨e,he',heN⟩ := semanticRank_correct row known depth (U \ L) (b-d) hRight hbR
          have hce : c=e := Option.some.inj (hc.symm.trans (he.trans he'))
          have hcL := (mem_sdiff.mp (mem_filter.mp hcN).1).1
          have heL := (mem_sdiff.mp (mem_sdiff.mp (mem_filter.mp heN).1).1).2
          exact (heL (hce ▸ hcL)).elim
      · by_cases hbL : b < d
        · simp only [ite_eq_right haL,ite_eq_left hbL] at he
          have haR : a-d < (remainingNeighbors row known (U \ L)).card := by omega
          obtain ⟨c,hc,hcN⟩ := semanticRank_correct row known depth (U \ L) (a-d) hRight haR
          obtain ⟨e,he',heN⟩ := semanticRank_correct row known depth L b hL hbL
          have hce : c=e := Option.some.inj (hc.symm.trans (he.trans he'))
          have hcL := (mem_sdiff.mp (mem_sdiff.mp (mem_filter.mp hcN).1).1).2
          have heL := (mem_sdiff.mp (mem_filter.mp heN).1).1
          exact (hcL (hce.symm ▸ heL)).elim
        · simp only [ite_eq_right haL,ite_eq_right hbL] at he
          have haR : a-d < (remainingNeighbors row known (U \ L)).card := by omega
          have hbR : b-d < (remainingNeighbors row known (U \ L)).card := by omega
          have hdiff := ih (U \ L) hRight haR hbR he
          omega

/-- A proof-side finite bijection certified by the query recursion. -/
def rankVertex (row : C → Bool) (known : Finset C) (depth : ℕ) (U : Finset C)
    (hcard : U.card ≤ 2^depth) (j : Fin (remainingNeighbors row known U).card) :
    remainingNeighbors row known U :=
  ⟨Classical.choose (semanticRank_correct row known depth U j.val hcard j.isLt),
    (Classical.choose_spec (semanticRank_correct row known depth U j.val hcard j.isLt)).2⟩

theorem rankVertex_spec (row : C → Bool) (known : Finset C) (depth : ℕ) (U : Finset C)
    (hcard : U.card ≤ 2^depth) (j : Fin (remainingNeighbors row known U).card) :
    semanticRank row known depth U j.val = some (rankVertex row known depth U hcard j).val :=
  (Classical.choose_spec (semanticRank_correct row known depth U j.val hcard j.isLt)).1

theorem rankVertex_bijective (row : C → Bool) (known : Finset C) (depth : ℕ) (U : Finset C)
    (hcard : U.card ≤ 2^depth) : Function.Bijective (rankVertex row known depth U hcard) := by
  have hinj : Function.Injective (rankVertex row known depth U hcard) := by
    intro i j hij
    apply Fin.ext
    apply semanticRank_injective row known depth U hcard i.isLt j.isLt
    rw [rankVertex_spec row known depth U hcard i,
      rankVertex_spec row known depth U hcard j,hij]
  refine ⟨hinj,?_⟩
  by_contra hsurj
  have hc := Fintype.card_lt_of_injective_not_surjective _ hinj hsurj
  simp only [Fintype.card_fin,Fintype.card_coe,lt_self_iff_false] at hc

private theorem uniform_map_equiv {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (e : A ≃ B) :
    (PMF.uniformOfFintype A).map e = PMF.uniformOfFintype B := by
  ext b
  rw [PMF.map_apply,tsum_eq_single (e.symm b)]
  · simp only [Equiv.apply_symm_apply,ite_true,PMF.uniformOfFintype_apply,Fintype.card_congr e]
  · intro a ha
    apply ite_eq_right
    intro he
    apply ha
    exact e.injective (he.symm.trans (e.apply_symm_apply b).symm)

private theorem uniform_subtype_val (N : Finset C) (hN : N.Nonempty) [Nonempty N] :
    (PMF.uniformOfFintype N).map (fun v => v.val) = PMF.uniformOfFinset N hN := by
  ext c
  rw [PMF.map_apply]
  by_cases hc : c ∈ N
  · rw [tsum_eq_single (⟨c,hc⟩ : N)]
    · simp [PMF.uniformOfFintype_apply,PMF.uniformOfFinset_apply,hc,Fintype.card_coe]
    · intro v hv
      apply ite_eq_right
      intro he
      apply hv
      apply Subtype.ext
      exact he.symm
  · have hz : ∀ v : N, c ≠ v.val := fun v he => hc (he ▸ v.property)
    simp only [hz,ite_false,tsum_zero,PMF.uniformOfFinset_apply,ite_eq_right hc]

/-- Sample a public finite rank, then locate it with actual binary queries. -/
def drawRemaining (u : R) (known : Finset C) (count : ℕ) :
    RTree (BipartiteQuery R C) ℝ (Option C) (searchDepth C) :=
  if h : 0 < count then
    letI : Nonempty (Fin count) := ⟨⟨0,h⟩⟩
    RTree.mix ((PMF.uniformOfFintype (Fin count)).map fun j =>
      RTree.ofDeterministic (rankSearch u known (searchDepth C) univ j.val))
  else RTree.pure (PMF.pure none)

/-- A uniformly drawn rank produces the actual uniform neighbor law on the
remaining row. This is derived from the query recursion's finite bijection. -/
theorem drawRemaining_uniform (M : BooleanMatrix R C) (u : R) (known : Finset C)
    (hknown : ∀ c ∈ known, M u c = true)
    (hN : (remainingNeighbors (M u) known univ).Nonempty) :
    (drawRemaining u known (remainingNeighbors (M u) known univ).card).eval
      (fun q => (bilinear M q : ℝ)) =
      (PMF.uniformOfFinset (remainingNeighbors (M u) known univ) hN).map some := by
  let N := remainingNeighbors (M u) known univ
  have hcard : (univ : Finset C).card ≤ 2^searchDepth C := card_le_pow_searchDepth univ
  have hpos : 0 < N.card := card_pos.mpr hN
  letI : Nonempty (Fin N.card) := ⟨⟨0,hpos⟩⟩
  letI : Nonempty N := hN.to_subtype
  let e : Fin N.card ≃ N := Equiv.ofBijective
    (rankVertex (M u) known (searchDepth C) univ hcard)
    (rankVertex_bijective (M u) known (searchDepth C) univ hcard)
  have hm := uniform_map_equiv e
  have heval :
      (drawRemaining u known N.card).eval (fun q => (bilinear M q : ℝ)) =
      ((PMF.uniformOfFintype (Fin N.card)).map e).map (fun v => some v.val) := by
    rw [drawRemaining,dite_eq_left hpos,RTree.eval_mix,PMF.bind_map]
    simp only [Function.comp_def,RTree.eval_ofDeterministic,rankSearch_eval M u known hknown]
    change (PMF.uniformOfFintype (Fin N.card)).map
      (fun j => semanticRank (M u) known (searchDepth C) univ j.val) = _
    simp only [PMF.map_comp,Function.comp_def]
    congr 1
    funext j
    exact rankVertex_spec (M u) known (searchDepth C) univ hcard j
  rw [heval,hm]
  have hs := uniform_subtype_val N hN
  have h := congrArg (fun μ : PMF C => μ.map some) hs
  simpa only [PMF.map_comp,Function.comp_def] using h

/-- A real finite without-replacement query program. Degree guards guarantee
its public count stays meaningful; inconsistent answers abort immediately. -/
def learnRanks (u : R) (degree : ℕ) : (k : ℕ) → Finset C →
    RTree (BipartiteQuery R C) ℝ (Option (Finset C)) (k*searchDepth C)
  | 0,known => RTree.pure (PMF.pure (some known))
  | k+1,known =>
      ((drawRemaining u known (degree-known.card)).bind fun answer =>
        match answer with
        | none => RTree.pure (PMF.pure none)
        | some v =>
            if v ∉ known then learnRanks u degree k (insert v known)
            else RTree.pure (PMF.pure none)).cast (by ring)

theorem learnRanks_every_oracle (u : R) (degree k : ℕ) (known : Finset C)
    (read : BipartiteQuery R C → ℝ) {out : Option (Finset C) × ℕ}
    (hout : out ∈ (RTree.run read (learnRanks u degree k known)).support) :
    out.2 ≤ k*searchDepth C := RTree.cost_le _ _ hout

theorem remainingNeighbors_univ (row : C → Bool) (known : Finset C) :
    remainingNeighbors row known univ = (univ.filter fun c => row c) \ known := by
  ext c
  simp only [remainingNeighbors,mem_filter,mem_sdiff,mem_univ,true_and]
  exact and_comm

theorem remainingNeighbors_card (row : C → Bool) (known : Finset C)
    (hknown : ∀ c ∈ known, row c = true) :
    (remainingNeighbors row known univ).card = sampleCount row univ-known.card := by
  have hsub : known ⊆ univ.filter (fun c => row c) := by
    intro c hc
    exact mem_filter.mpr ⟨mem_univ _,hknown c hc⟩
  rw [remainingNeighbors_univ,card_sdiff_of_subset hsub,← sampleCount_eq_filter_card]

/-- The actual rank fallback never aborts on a valid remaining-degree promise.
It returns exactly k new distinct true neighbors, retaining any earlier list. -/
theorem learnRanks_correct (M : BooleanMatrix R C) (u : R) (k : ℕ) (known : Finset C)
    (hknown : ∀ c ∈ known, M u c = true)
    (hsize : known.card+k ≤ sampleCount (M u) univ)
    {answer : Option (Finset C)}
    (hanswer : answer ∈ ((learnRanks u (sampleCount (M u) univ) k known).eval
      (fun q => (bilinear M q : ℝ))).support) :
    ∃ N, answer = some N ∧ known ⊆ N ∧ N.card = known.card+k ∧
      ∀ c ∈ N, M u c = true := by
  induction k generalizing known answer with
  | zero =>
      have he : answer = some known := by
        simpa only [learnRanks,RTree.eval_pure,PMF.mem_support_pure_iff] using hanswer
      exact ⟨known,he,Subset.rfl,by omega,hknown⟩
  | succ k ih =>
      have hremaining : (remainingNeighbors (M u) known univ).Nonempty := by
        rw [← card_pos,remainingNeighbors_card (M u) known hknown]
        omega
      rw [learnRanks,RTree.eval_cast,RTree.eval_bind,
        ← remainingNeighbors_card (M u) known hknown,
        drawRemaining_uniform M u known hknown hremaining] at hanswer
      obtain ⟨first,hfirst,hlater⟩ := (PMF.mem_support_bind_iff _ _ _).mp hanswer
      obtain ⟨v,hv,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hfirst
      have hvmem : v ∈ remainingNeighbors (M u) known univ := by
        simpa only [PMF.mem_support_uniformOfFinset_iff] using hv
      have hvnot : v ∉ known := (mem_sdiff.mp (mem_filter.mp hvmem).1).2
      have hvtrue : M u v = true := (mem_filter.mp hvmem).2
      simp only [ite_eq_left hvnot] at hlater
      have hknown' : ∀ c ∈ insert v known, M u c = true := by
        intro c hc
        rcases mem_insert.mp hc with rfl | hc
        · exact hvtrue
        · exact hknown c hc
      have hsize' : (insert v known).card+k ≤ sampleCount (M u) univ := by
        rw [card_insert_of_notMem hvnot]
        omega
      obtain ⟨N,hN,hsub,hcard,htrue⟩ := ih (insert v known) hknown' hsize' hlater
      refine ⟨N,hN,(subset_insert _ _).trans hsub,?_,htrue⟩
      rw [card_insert_of_notMem hvnot] at hcard
      omega

theorem learnRanks_initial_correct (M : BooleanMatrix R C) (u : R) (k : ℕ)
    (hk : k ≤ sampleCount (M u) univ) {answer : Option (Finset C)}
    (hanswer : answer ∈ ((learnRanks u (sampleCount (M u) univ) k ∅).eval
      (fun q => (bilinear M q : ℝ))).support) :
    ∃ N, answer = some N ∧ N.card = k ∧ ∀ c ∈ N, M u c = true := by
  obtain ⟨N,hN,_,hcard,htrue⟩ := learnRanks_correct M u k ∅
    (by simp) (by simpa using hk) hanswer
  exact ⟨N,hN,by simpa using hcard,htrue⟩

/-- Proof-side finite subset law. The operational fallback samples ranks and
does not receive the hidden neighbor set used to state this law. -/
def uniformSubset (N : Finset C) (k : ℕ) (hk : k ≤ N.card) : PMF (Finset C) :=
  PMF.uniformOfFinset (N.powersetCard k) (powersetCard_nonempty.mpr hk)

theorem uniformSubset_support (N : Finset C) (k : ℕ) (hk : k ≤ N.card) (S : Finset C) :
    S ∈ (uniformSubset N k hk).support ↔ S ⊆ N ∧ S.card = k := by
  simp only [uniformSubset,PMF.mem_support_uniformOfFinset_iff,mem_powersetCard]

private theorem uniform_map_insert (N : Finset C) (k : ℕ) (hk : k ≤ N.card)
    (v : C) (hv : v ∉ N) (S : Finset C) :
    ((uniformSubset N k hk).map (insert v)) S =
      if v ∈ S then uniformSubset N k hk (S.erase v) else 0 := by
  rw [PMF.map_apply,tsum_eq_single (S.erase v)]
  · by_cases hvS : v ∈ S
    · simp only [insert_erase hvS,ite_true,ite_eq_left hvS]
    · have he : S ≠ insert v (S.erase v) := by
        intro he
        exact hvS (he ▸ mem_insert_self _ _)
      simp only [ite_eq_right he,ite_eq_right hvS]
  · intro T hT
    by_cases he : S = insert v T
    · by_cases hpos : T ∈ (uniformSubset N k hk).support
      · have hvT : v ∉ T := fun hm => hv (((uniformSubset_support N k hk T).mp hpos).1 hm)
        have herase : S.erase v = T := by rw [he,erase_insert hvT]
        exact (hT herase.symm).elim
      · have hz : uniformSubset N k hk T = 0 := by
          simpa only [PMF.mem_support_iff,not_not] using hpos
        simp only [hz,ite_self]
    · simp only [ite_eq_right he]

private theorem pmf_bind_congr_on_support {X Y : Type} (μ : PMF X)
    {f g : X → PMF Y} (h : ∀ x ∈ μ.support, f x = g x) : μ.bind f = μ.bind g := by
  ext y
  simp only [PMF.bind_apply]
  apply tsum_congr
  intro x
  by_cases hx : x ∈ μ.support
  · rw [h x hx]
  · have hz : μ x = 0 := by simpa only [PMF.mem_support_iff,not_not] using hx
    simp only [hz,zero_mul]

/-- The exact finite recursion of uniform subsets: one uniform element followed
by a uniform subset of the remaining set. This will identify repeated ranks. -/
theorem uniformSubset_step (N : Finset C) (k : ℕ) (hk : k+1 ≤ N.card) :
    (PMF.uniformOfFinset N (card_pos.mp (by omega))).bind (fun v =>
      if hv : v ∈ N then
        (uniformSubset (N.erase v) k (by
          rw [card_erase_of_mem hv]
          omega)).map (insert v)
      else PMF.pure ∅) = uniformSubset N (k+1) hk := by
  let μ := (PMF.uniformOfFinset N (card_pos.mp (by omega))).bind (fun v =>
    if hv : v ∈ N then
      (uniformSubset (N.erase v) k (by rw [card_erase_of_mem hv]; omega)).map (insert v)
    else PMF.pure ∅)
  have hsupport : ∀ S ∈ μ.support, S ⊆ N ∧ S.card = k+1 := by
    intro S hS
    obtain ⟨v,hv,htail⟩ := (PMF.mem_support_bind_iff _ _ _).mp hS
    have hvN : v ∈ N := by simpa only [PMF.mem_support_uniformOfFinset_iff] using hv
    rw [dite_eq_left hvN] at htail
    obtain ⟨T,hT,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp htail
    have ht := (uniformSubset_support _ _ _ T).mp hT
    have hvT : v ∉ T := fun hvT => (mem_erase.mp (ht.1 hvT)).1 rfl
    exact ⟨insert_subset hvN (ht.1.trans (erase_subset _ _)),by rw [card_insert_of_notMem hvT,ht.2]⟩
  change μ = uniformSubset N (k+1) hk
  ext S
  by_cases hS : S ⊆ N ∧ S.card = k+1
  · have hmass : μ S =
        (S.card : ℝ≥0∞)*(N.card : ℝ≥0∞)⁻¹*((N.card-1).choose k : ℝ≥0∞)⁻¹ := by
      change (PMF.bind _ _) S = _
      rw [PMF.bind_apply,tsum_fintype]
      calc
        _ = ∑ v : C, if v ∈ S then
            (N.card : ℝ≥0∞)⁻¹*((N.card-1).choose k : ℝ≥0∞)⁻¹ else 0 := by
          apply sum_congr rfl
          intro v _
          by_cases hvS : v ∈ S
          · have hvN := hS.1 hvS
            have herase : S.erase v ∈ (N.erase v).powersetCard k := by
              apply mem_powersetCard.mpr
              refine ⟨erase_subset_erase v hS.1,?_⟩
              rw [card_erase_of_mem hvS,hS.2]
              omega
            rw [PMF.uniformOfFinset_apply_of_mem _ hvN,dite_eq_left hvN,
              uniform_map_insert _ _ _ v (notMem_erase _ _) S,ite_eq_left hvS]
            simp only [uniformSubset,PMF.uniformOfFinset_apply_of_mem _ herase,
              card_powersetCard,card_erase_of_mem hvN,ite_eq_left hvS]
          · by_cases hvN : v ∈ N
            · simp only [dite_eq_left hvN,uniform_map_insert _ _ _ v (notMem_erase _ _),
                ite_eq_right hvS,mul_zero]
            · simp only [PMF.uniformOfFinset_apply_of_notMem _ hvN,zero_mul,ite_eq_right hvS]
        _ = _ := by rw [sum_ite_mem_eq]; simp [mul_assoc]
    rw [hmass]
    change _ = (PMF.uniformOfFinset _ _) S
    rw [PMF.uniformOfFinset_apply_of_mem _ (mem_powersetCard.mpr hS),card_powersetCard,hS.2]
    have hn : N.card ≠ 0 := by omega
    have ha : (N.card-1).choose k ≠ 0 := Nat.ne_of_gt (Nat.choose_pos (by omega))
    have hb : N.card.choose (k+1) ≠ 0 := Nat.ne_of_gt (Nat.choose_pos hk)
    have he : N.card*((N.card-1).choose k) = N.card.choose (k+1)*(k+1) := by
      have h := Nat.add_one_mul_choose_eq (N.card-1) k
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ N.card)] using h
    have heR : (N.card : ℝ)*((N.card-1).choose k : ℝ) =
        (N.card.choose (k+1) : ℝ)*(k+1) := by exact_mod_cast he
    apply (ENNReal.toReal_eq_toReal_iff'
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp)
        (ENNReal.inv_ne_top.mpr (by exact_mod_cast hn)))
        (ENNReal.inv_ne_top.mpr (by exact_mod_cast ha)))
      (ENNReal.inv_ne_top.mpr (by exact_mod_cast hb))).mp
    simp only [ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_natCast]
    have hnR : (N.card : ℝ) ≠ 0 := by exact_mod_cast hn
    have haR : ((N.card-1).choose k : ℝ) ≠ 0 := by exact_mod_cast ha
    have hbR : (N.card.choose (k+1) : ℝ) ≠ 0 := by exact_mod_cast hb
    push_cast
    field_simp [hnR,haR,hbR] <;> nlinarith [heR]
  · have hzero : μ S = 0 := by
      by_contra h
      exact hS (hsupport S h)
    rw [hzero]
    have hnot : S ∉ N.powersetCard (k+1) := by simpa only [mem_powersetCard] using hS
    exact (PMF.uniformOfFinset_apply_of_notMem _ hnot).symm

/-- Finite proof-side sampling recursion, with the same without-replacement
mechanism as the implemented rank fallback. -/
def rankSubsetLaw (N : Finset C) : ℕ → PMF (Finset C)
  | 0 => PMF.pure ∅
  | k+1 => if hN : N.Nonempty then
      (PMF.uniformOfFinset N hN).bind fun v =>
        (rankSubsetLaw (N.erase v) k).map (insert v)
    else PMF.pure ∅

theorem rankSubsetLaw_uniform (N : Finset C) (k : ℕ) (hk : k ≤ N.card) :
    rankSubsetLaw N k = uniformSubset N k hk := by
  induction k generalizing N with
  | zero =>
      ext S
      simp [rankSubsetLaw,uniformSubset,PMF.pure_apply,powersetCard_zero,eq_comm]
  | succ k ih =>
      have hN : N.Nonempty := card_pos.mp (by omega)
      rw [rankSubsetLaw,dite_eq_left hN,← uniformSubset_step N k hk]
      apply pmf_bind_congr_on_support
      intro v hv
      have hvN : v ∈ N := by simpa only [PMF.mem_support_uniformOfFinset_iff] using hv
      rw [dite_eq_left hvN,ih (N.erase v) (by rw [card_erase_of_mem hvN]; omega)]

theorem remainingNeighbors_insert (row : C → Bool) (known : Finset C) (v : C) :
    remainingNeighbors row (insert v known) univ =
      (remainingNeighbors row known univ).erase v := by
  ext c
  simp only [remainingNeighbors,mem_filter,mem_sdiff,mem_univ,true_and,mem_insert,mem_erase]
  tauto

/-- Exact coupling of every finite rank program with finite sampling without
replacement. All appearances of M belong to the correctness statement. -/
theorem learnRanks_law (M : BooleanMatrix R C) (u : R) (k : ℕ) (known : Finset C)
    (hknown : ∀ c ∈ known, M u c = true)
    (hsize : known.card+k ≤ sampleCount (M u) univ) :
    (learnRanks u (sampleCount (M u) univ) k known).eval
      (fun q => (bilinear M q : ℝ)) =
      (rankSubsetLaw (remainingNeighbors (M u) known univ) k).map
        (fun S => some (known ∪ S)) := by
  induction k generalizing known with
  | zero => simp only [learnRanks,RTree.eval_pure,rankSubsetLaw,PMF.pure_map,union_empty]
  | succ k ih =>
      let N := remainingNeighbors (M u) known univ
      have hN : N.Nonempty := by
        rw [← card_pos,remainingNeighbors_card (M u) known hknown]
        omega
      rw [learnRanks,RTree.eval_cast,RTree.eval_bind,
        ← remainingNeighbors_card (M u) known hknown,
        drawRemaining_uniform M u known hknown hN,PMF.bind_map]
      rw [rankSubsetLaw,dite_eq_left hN,PMF.map_bind]
      simp only [Function.comp_def]
      apply pmf_bind_congr_on_support
      intro v hv
      have hvN : v ∈ N := by simpa only [PMF.mem_support_uniformOfFinset_iff] using hv
      have hvnot : v ∉ known := (mem_sdiff.mp (mem_filter.mp hvN).1).2
      have hvtrue : M u v = true := (mem_filter.mp hvN).2
      have hknown' : ∀ c ∈ insert v known, M u c = true := by
        intro c hc
        rcases mem_insert.mp hc with rfl | hc
        · exact hvtrue
        · exact hknown c hc
      have hsize' : (insert v known).card+k ≤ sampleCount (M u) univ := by
        rw [card_insert_of_notMem hvnot]
        omega
      rw [ite_eq_left hvnot,ih (insert v known) hknown' hsize',remainingNeighbors_insert]
      simp only [PMF.map_comp,Function.comp_def,insert_union,union_insert]

/-- The fallback returns the exact uniform k-subset of the true neighbor set,
not merely a sequence of individually uniform or possibly repeated neighbors. -/
theorem learnRanks_uniform (M : BooleanMatrix R C) (u : R) (k : ℕ)
    (hk : k ≤ sampleCount (M u) univ) :
    (learnRanks u (sampleCount (M u) univ) k ∅).eval (fun q => (bilinear M q : ℝ)) =
      (uniformSubset (univ.filter fun c => M u c) k
        (by simpa only [← sampleCount_eq_filter_card] using hk)).map some := by
  rw [learnRanks_law M u k ∅ (by simp) (by simpa using hk),
    rankSubsetLaw_uniform _ k (by
      rw [remainingNeighbors_card (M u) ∅ (by simp)]
      simpa using hk)]
  simp only [remainingNeighbors_univ,sdiff_empty,empty_union]

end UniformRank


section AcceptedRowLaw

open CutQueryComplexity.StarContraction2022.Probability

variable {C R : Type} [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]

/-- The hidden neighbor set appears only in distributional correctness proofs. -/
def rowNeighbors (row : C → Bool) : Finset C := univ.filter fun c => row c

theorem rowNeighbors_restrict (row : C → Bool) (S : Finset C) :
    S.filter (fun c => row c) = S ∩ rowNeighbors row := by
  ext c
  simp only [mem_filter,mem_inter,rowNeighbors,mem_univ,true_and]

theorem sampleCount_eq_restriction (row : C → Bool) (S : Finset C) :
    sampleCount row S = (S ∩ rowNeighbors row).card := by
  rw [sampleCount_eq_filter_card,rowNeighbors_restrict]

/-- The actual finite coin sampler has exactly the checked Bernoulli law on a
fixed row. No statement about independence of different row restrictions occurs. -/
theorem columnProposal_restriction (p : ℝ≥0) (hp : p ≤ 1) (N : Finset C) :
    (columnProposal (C := C) p hp).map (fun S => S ∩ N) =
      bernoulliSubset N (p : ℝ≥0∞) (by exact_mod_cast hp) := by
  ext S : 1
  rw [columnProposal_restrict_apply,bernoulliSubset_apply]
  by_cases hSN : S ⊆ N <;> simp [hSN,ENNReal.coe_sub]

theorem firstSuccess_map {α β : Type} (p : PMF (Option α)) (f : α → β) (T : ℕ) :
    (firstSuccess p T).map (Option.map f) = firstSuccess (p.map (Option.map f)) T := by
  induction T with
  | zero => simp only [firstSuccess,PMF.pure_map,Option.map_none]
  | succ T ih =>
      simp only [firstSuccess,PMF.map_bind,PMF.bind_map,Function.comp_def]
      congr 1
      funext o
      cases o with
      | none => simpa only [Option.map_none] using ih
      | some x => simp only [Option.map_some,PMF.pure_map]

theorem rowProposal_map {α β : Type} (μ : PMF α) (f : α → β) (W : β → Prop) :
    (rowProposal μ (fun x => W (f x))).map (Option.map f) = rowProposal (μ.map f) W := by
  simp only [rowProposal,PMF.map_comp,Function.comp_def]
  congr 1
  funext x
  by_cases hx : W (f x) <;> simp only [hx,ite_true,ite_false,Option.map_some,Option.map_none]

theorem rowProposal_some {α : Type} (μ : PMF α) (P : α → Prop) (x : α) :
    rowProposal μ P (some x) = if P x then μ x else 0 := by
  rw [rowProposal,PMF.map_apply,tsum_eq_single x]
  · by_cases hx : P x <;> simp [hx]
  · intro y hy
    by_cases hPy : P y
    · have he : (some x : Option α) ≠ some y := fun h => hy (Option.some.inj h).symm
      simp only [ite_eq_left hPy,ite_eq_right he]
    · simp only [ite_eq_right hPy,Option.some_ne_none,ite_false]

private theorem acceptance_mass_pos {α : Type} (μ : PMF α) (P : α → Prop)
    (h : ∃ x, P x ∧ x ∈ μ.support) : 0 < mass μ P := by
  obtain ⟨x,hP,hx⟩ := h
  have hm : μ x ≤ mass μ P := by
    rw [mass_eq_tsum]
    simpa only [ite_eq_left hP] using
      (ENNReal.le_tsum (f := fun y => if P y then μ y else 0) x)
  exact (bot_lt_iff_ne_bot.mpr hx).trans_le hm

private theorem rowProposal_rejection_lt_one {α : Type} [Fintype α] [DecidableEq α]
    (μ : PMF α) (P : α → Prop)
    (h : ∃ x, P x ∧ x ∈ μ.support) : (rowProposal μ P none).toReal < 1 := by
  have hp := ENNReal.toReal_pos (ne_of_gt (acceptance_mass_pos μ P h)) (mass_ne_top μ P)
  have hc := real_add_compl μ P
  rw [rowProposal_none]
  linarith

/-- The exact finite-completion factor multiplying the accepted law. The
conditioning is only on this row's own acceptance predicate. -/
theorem firstSuccess_conditioned_real {α : Type} [Fintype α] [DecidableEq α]
    (μ : PMF α) (P : α → Prop) (h : ∃ x, P x ∧ x ∈ μ.support) (T : ℕ) (x : α) :
    (firstSuccess (rowProposal μ P) T (some x)).toReal =
      (1-(mass μ (fun y => ¬P y)).toReal^T)*((μ.filter {x | P x} h) x).toReal := by
  rw [firstSuccess_some_real _ _ _ (rowProposal_rejection_lt_one μ P h),
    rowProposal_some,rowProposal_none,filter_apply_mass,ENNReal.toReal_div]
  have hc := real_add_compl μ P
  have hd : 1-(mass μ (fun y => ¬P y)).toReal = (mass μ P).toReal := by linarith
  rw [hd]

theorem firstSuccess_conditioned_some_le {α : Type} [Fintype α] [DecidableEq α]
    (μ : PMF α) (P : α → Prop) (h : ∃ x, P x ∧ x ∈ μ.support) (T : ℕ) (x : α) :
    firstSuccess (rowProposal μ P) T (some x) ≤ (μ.filter {x | P x} h) x := by
  apply (ENNReal.toReal_le_toReal (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [firstSuccess_conditioned_real μ P h T x]
  have hn := pow_nonneg (ENNReal.toReal_nonneg (a := mass μ (fun y => ¬P y))) T
  have hm : 0 ≤ ((μ.filter {x | P x} h) x).toReal := ENNReal.toReal_nonneg
  nlinarith

theorem firstSuccess_conditioned_bad_le {α : Type} [Fintype α] [DecidableEq α]
    (μ : PMF α) (P : α → Prop) (h : ∃ x, P x ∧ x ∈ μ.support) (T : ℕ) (Bad : α → Prop) :
    mass (firstSuccess (rowProposal μ P) T) (fun o => o.elim False Bad) ≤
      mass (μ.filter {x | P x} h) Bad := by
  simp only [mass_eq_tsum,tsum_fintype,Fintype.sum_option,Option.elim_none,ite_false,
    zero_add,Option.elim_some]
  apply sum_le_sum
  intro x _
  by_cases hx : Bad x
  · simp only [ite_eq_left hx]
    exact firstSuccess_conditioned_some_le μ P h T x
  · simp only [ite_eq_right hx,le_refl]

theorem firstSuccess_conditioned_expect_le {α : Type} [Fintype α] [DecidableEq α]
    (μ : PMF α) (P : α → Prop) (h : ∃ x, P x ∧ x ∈ μ.support) (T : ℕ) (f : α → ℝ≥0∞) :
    expect (firstSuccess (rowProposal μ P) T) (fun o => o.elim 0 f) ≤
      expect (μ.filter {x | P x} h) f := by
  simp only [CutQueryComplexity.Probability.expect,tsum_fintype,Fintype.sum_option,
    Option.elim_none,mul_zero,zero_add,Option.elim_some]
  apply sum_le_sum
  intro x _
  exact mul_le_mul (firstSuccess_conditioned_some_le μ P h T x) le_rfl (by positivity) (by positivity)

/-- Passing from sampled columns to learned true neighbors commutes with a
row's acceptance test. It does not discard correlations between different rows. -/
theorem rowProposal_restriction (row : C → Bool) (p : ℝ≥0) (hp : p ≤ 1) (k : ℕ) :
    (rowProposal (columnProposal (C := C) p hp) (bucketAccept k row)).map
        (Option.map (fun S => S ∩ rowNeighbors row)) =
      rowProposal (bernoulliSubset (rowNeighbors row) (p : ℝ≥0∞) (by exact_mod_cast hp))
        (fun S => k ≤ S.card ∧ S.card ≤ 8*k) := by
  have he : bucketAccept k row =
      fun S => k ≤ (S ∩ rowNeighbors row).card ∧ (S ∩ rowNeighbors row).card ≤ 8*k := by
    funext S
    simp only [bucketAccept,sampleCount_eq_restriction]
  rw [he]
  simpa only [columnProposal_restriction] using
    (rowProposal_map (columnProposal (C := C) p hp)
      (fun S => S ∩ rowNeighbors row) (fun S : Finset C => k ≤ S.card ∧ S.card ≤ 8*k))

private theorem recovery_map_equal_on_support {α β : Type} (μ : PMF α) {f g : α → β}
    (h : ∀ x ∈ μ.support, f x = g x) : μ.map f = μ.map g := by
  ext y
  simp only [PMF.map_apply]
  apply tsum_congr
  intro x
  by_cases hx : x ∈ μ.support
  · rw [h x hx]
  · have hz : μ x = 0 := by simpa only [PMF.mem_support_iff,not_not] using hx
    simp [hz]

/-- Actual learned-row marginal, including its finite-horizon absence event.
The graph is a proof parameter; it is absent from the public query constructor. -/
theorem learnBucketRounds_learned_law (M : BooleanMatrix R C) (r k T : ℕ) (u : R) :
    ((learnBucketRounds r k T (BucketState.initial : BucketState R C)).eval
      (fun q => (bilinear M q : ℝ))).map (fun st => st.learned u) =
      firstSuccess (rowProposal
        (bernoulliSubset (rowNeighbors (M u)) (bucketProbability r k : ℝ≥0∞)
          (by exact_mod_cast bucketProbability_le_one r k))
        (fun S => k ≤ S.card ∧ S.card ≤ 8*k)) T := by
  let μ := (learnBucketRounds r k T (BucketState.initial : BucketState R C)).eval
    (fun q => (bilinear M q : ℝ))
  have hlearn : μ.map (fun st => st.learned u) =
      μ.map (fun st => (st.proposal u).map (fun S => S ∩ rowNeighbors (M u))) := by
    apply recovery_map_equal_on_support
    intro st hst
    obtain ⟨out,hout,he⟩ := (PMF.mem_support_map_iff _ _ _).mp hst
    have hi := learnBucketRounds_invariant M r k T BucketState.initial
      (BucketInvariant.initial M k) hout
    have hi' : BucketInvariant M k st := by simpa only [he] using hi
    cases hp : st.proposal u with
    | none => simpa only [hp,Option.map_none] using (hi'.2 u).1.mp hp
    | some S =>
        simpa only [hp,Option.map_some,rowNeighbors_restrict] using (hi'.2 u).2 S hp |>.1
  calc
    _ = μ.map (fun st => (st.proposal u).map (fun S => S ∩ rowNeighbors (M u))) := hlearn
    _ = (μ.map (fun st => st.proposal u)).map (Option.map (fun S => S ∩ rowNeighbors (M u))) := by
      rw [PMF.map_comp]
      rfl
    _ = _ := by
      dsimp only [μ]
      rw [learnBucketRounds_row_law M r k T u,firstSuccess_map,rowProposal_restriction]

/-- Actual geometric rejection guarantees a nonempty accepted size window.
The witness is derived, not supplied as a recovery correctness premise. -/
theorem bucketRow_window_supported (row : C → Bool) (r k : ℕ) (hk : 10 ≤ k) (hkr : k ≤ r)
    (hdlo : r ≤ sampleCount row univ) (hdhi : sampleCount row univ ≤ 2*r) :
    ∃ j : Fin ((rowNeighbors row).card+1), k ≤ j.val ∧ j.val ≤ 8*k ∧
      j ∈ (binomialSize (rowNeighbors row).card (bucketProbability r k : ℝ≥0∞)
        (by exact_mod_cast bucketProbability_le_one r k)).support := by
  let μ := bernoulliSubset (rowNeighbors row) (bucketProbability r k : ℝ≥0∞)
    (show (bucketProbability r k : ℝ≥0∞) ≤ 1 by exact_mod_cast bucketProbability_le_one r k)
  let W : Finset C → Prop := fun S => k ≤ S.card ∧ S.card ≤ 8*k
  have hreject : rowProposal μ W none ≤ (2 : ℝ≥0∞)⁻¹ := by
    have he := congrArg (fun p : PMF (Option (Finset C)) => p none)
      (rowProposal_restriction row (bucketProbability r k) (bucketProbability_le_one r k) k)
    have hnone : ((rowProposal (columnProposal (C := C) (bucketProbability r k)
        (bucketProbability_le_one r k)) (bucketAccept k row)).map
          (Option.map (fun S => S ∩ rowNeighbors row))) none =
        rowProposal (columnProposal (C := C) (bucketProbability r k)
          (bucketProbability_le_one r k)) (bucketAccept k row) none := by
      simp [PMF.map_apply,tsum_fintype,Fintype.sum_option]
    rw [hnone] at he
    rw [← he]
    exact bucket_row_reject_le_half row r k hk hkr hdlo hdhi
  have hmass : mass μ W ≠ 0 := by
    intro hz
    have hc := mass_add_compl μ W
    rw [hz,zero_add] at hc
    rw [rowProposal_none,hc] at hreject
    norm_num at hreject
  have hex : ∃ S, W S ∧ S ∈ μ.support := by
    by_contra! hno
    apply hmass
    rw [mass_eq_tsum]
    apply ENNReal.tsum_eq_zero.mpr
    intro S
    by_cases hS : W S
    · rw [ite_eq_left hS]
      simpa only [PMF.mem_support_iff,not_not] using hno S hS
    · simp only [ite_eq_right hS]
  obtain ⟨S,hS,hμ⟩ := hex
  dsimp only [μ] at hμ
  rw [bernoulliSubset_eq_sizeMixture,sizeMixture] at hμ
  obtain ⟨j,hj,hSj⟩ := (PMF.mem_support_bind_iff _ _ _).mp hμ
  have hcard := ((fixedSize_support _ _ _ _).mp hSj).2
  exact ⟨j,by simpa only [hcard] using hS.1,by simpa only [hcard] using hS.2,hj⟩

/-- The checked accepted-window tail now applies to the implemented learned
row. The finite completion factor is at most one, so no horizon or cap
conditioning is hidden in this bound. -/
theorem learnBucketRounds_row_ratio_tail (M : BooleanMatrix R C) (r k T : ℕ) (u : R)
    (hk : 10 ≤ k) (hkr : k ≤ r)
    (hdlo : r ≤ sampleCount (M u) univ) (hdhi : sampleCount (M u) univ ≤ 2*r)
    (Z : Finset C) (hZ : Z ⊆ rowNeighbors (M u)) (eps : ℝ) (heps : 0 < eps) :
    mass ((learnBucketRounds r k T (BucketState.initial : BucketState R C)).eval
      (fun q => (bilinear M q : ℝ)))
      (fun st => (st.learned u).elim False
        (fun S => (Z.card : ℝ)/(rowNeighbors (M u)).card+eps < crossingRatio Z S)) ≤
      ENNReal.ofReal (((Z.card : ℝ)/(rowNeighbors (M u)).card)/k/eps^2) := by
  let N := rowNeighbors (M u)
  let p : ℝ≥0∞ := bucketProbability r k
  have hp : p ≤ 1 := by
    dsimp only [p]
    exact_mod_cast bucketProbability_le_one r k
  let W : ℕ → Prop := fun j => k ≤ j ∧ j ≤ 8*k
  have hW : ∃ j : Fin (N.card+1), W j.val ∧ j ∈ (binomialSize N.card p hp).support := by
    obtain ⟨j,hlo,hhi,hj⟩ := bucketRow_window_supported (M u) r k hk hkr hdlo hdhi
    exact ⟨j,⟨hlo,hhi⟩,hj⟩
  rw [← mass_map _ (fun st : BucketState R C => st.learned u)
    (fun o : Option (Finset C) => o.elim False
      (fun S => (Z.card : ℝ)/(rowNeighbors (M u)).card+eps < crossingRatio Z S)),
    learnBucketRounds_learned_law]
  have h := firstSuccess_conditioned_bad_le (bernoulliSubset N p hp) (fun S => W S.card)
    (bernoulliSubset_window_supported N p hp W hW) T
    (fun S => (Z.card : ℝ)/N.card+eps < crossingRatio Z S)
  rw [condition_bernoulliSubset_window N p hp W hW] at h
  exact h.trans (acceptedBernoulli_ratio_tail N Z p hp W hW k (by omega) hZ
    (fun _ hj => hj.1) eps heps)

/-- The accepted row has mean crossing ratio rho; finite noncompletion can
only reduce the unconditional mean, with absent rows assigned zero. -/
theorem learnBucketRounds_row_ratio_mean (M : BooleanMatrix R C) (r k T : ℕ) (u : R)
    (hk : 10 ≤ k) (hkr : k ≤ r)
    (hdlo : r ≤ sampleCount (M u) univ) (hdhi : sampleCount (M u) univ ≤ 2*r)
    (Z : Finset C) (hZ : Z ⊆ rowNeighbors (M u)) :
    expect ((learnBucketRounds r k T (BucketState.initial : BucketState R C)).eval
      (fun q => (bilinear M q : ℝ)))
      (fun st => (st.learned u).elim 0 (fun S => ENNReal.ofReal (crossingRatio Z S))) ≤
      ENNReal.ofReal ((Z.card : ℝ)/(rowNeighbors (M u)).card) := by
  let N := rowNeighbors (M u)
  let p : ℝ≥0∞ := bucketProbability r k
  have hp : p ≤ 1 := by
    dsimp only [p]
    exact_mod_cast bucketProbability_le_one r k
  let W : ℕ → Prop := fun j => k ≤ j ∧ j ≤ 8*k
  have hW : ∃ j : Fin (N.card+1), W j.val ∧ j ∈ (binomialSize N.card p hp).support := by
    obtain ⟨j,hlo,hhi,hj⟩ := bucketRow_window_supported (M u) r k hk hkr hdlo hdhi
    exact ⟨j,⟨hlo,hhi⟩,hj⟩
  rw [← CutQueryComplexity.Probability.expect_map _ (fun st : BucketState R C => st.learned u)
    (fun o : Option (Finset C) => o.elim 0
      (fun S => ENNReal.ofReal (crossingRatio Z S))),learnBucketRounds_learned_law]
  have h := firstSuccess_conditioned_expect_le (bernoulliSubset N p hp) (fun S => W S.card)
    (bernoulliSubset_window_supported N p hp W hW) T
    (fun S => ENNReal.ofReal (crossingRatio Z S))
  rw [condition_bernoulliSubset_window N p hp W hW] at h
  have hpos : ∀ j ∈ ((binomialSize N.card p hp).filter
      {j : Fin (N.card+1) | W j.val} hW).support, 0 < j.val := by
    intro j hj
    have hwin : W j.val := ((PMF.mem_support_filter_iff _).mp hj).1
    exact lt_of_lt_of_le (by omega : 0 < k) hwin.1
  exact h.trans_eq (sizeMixture_ratio_mean N Z _ hZ hpos)

/-- The actual rank fallback has the same tail bound by its proved uniform
without-replacement law. It pays logarithmic queries per sampled rank. -/
theorem learnRanks_row_ratio_tail (M : BooleanMatrix R C) (u : R) (k : ℕ)
    (hk : 0 < k) (hdegree : k ≤ sampleCount (M u) univ)
    (Z : Finset C) (hZ : Z ⊆ rowNeighbors (M u)) (eps : ℝ) (heps : 0 < eps) :
    mass ((learnRanks u (sampleCount (M u) univ) k ∅).eval (fun q => (bilinear M q : ℝ)))
      (fun o => o.elim False (fun S => (Z.card : ℝ)/(rowNeighbors (M u)).card+eps < crossingRatio Z S)) ≤
      ENNReal.ofReal (((Z.card : ℝ)/(rowNeighbors (M u)).card)/k/eps^2) := by
  rw [learnRanks_uniform M u k hdegree,mass_map]
  exact fixedSize_ratio_tail (rowNeighbors (M u)) Z k hZ hk
    (by simpa only [rowNeighbors,← sampleCount_eq_filter_card] using hdegree) eps heps

theorem learnRanks_row_ratio_mean (M : BooleanMatrix R C) (u : R) (k : ℕ)
    (hk : 0 < k) (hdegree : k ≤ sampleCount (M u) univ)
    (Z : Finset C) (hZ : Z ⊆ rowNeighbors (M u)) :
    expect ((learnRanks u (sampleCount (M u) univ) k ∅).eval (fun q => (bilinear M q : ℝ)))
      (fun o => o.elim 0 (fun S => ENNReal.ofReal (crossingRatio Z S))) =
      ENNReal.ofReal ((Z.card : ℝ)/(rowNeighbors (M u)).card) := by
  rw [learnRanks_uniform M u k hdegree,expect_map]
  exact fixedSize_ratio_mean (rowNeighbors (M u)) Z k hZ hk
    (by simpa only [rowNeighbors,← sampleCount_eq_filter_card] using hdegree)

end AcceptedRowLaw


section BucketNumerics

/-- Scalar form of the proved primitive-B expression, with zero for an empty
row bucket. All logarithms remain tied to the actual bucket cardinality. -/
def bucketNumeric (b t k : ℕ) : ℝ :=
  (bucketConstant : ℝ)*((b : ℝ)+(k : ℝ)*b*Real.log (2*(t : ℝ))/Real.log (2*(b : ℝ)))

@[simp] theorem bucketNumeric_zero (t k : ℕ) : bucketNumeric 0 t k = 0 := by
  simp [bucketNumeric]

theorem bucketNumeric_nonneg (b t k : ℕ) (ht : 1 ≤ t) : 0 ≤ bucketNumeric b t k := by
  by_cases hb : b = 0
  · simp [hb]
  · have hbR : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
    have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
    exact mul_nonneg (Nat.cast_nonneg _) (add_nonneg (Nat.cast_nonneg _)
      (div_nonneg (mul_nonneg (by positivity) (Real.log_nonneg (by linarith)))
        (Real.log_nonneg (by linarith))))

theorem bucketNumeric_large (b t k : ℕ) (ht : 1 ≤ t) (hk : 1 ≤ k)
    (hlarge : Real.exp (Real.log (t : ℝ)/6) ≤ b) :
    bucketNumeric b t k ≤ 7*(bucketConstant : ℝ)*k*b := by
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hz : 0 ≤ Real.log (t : ℝ) := Real.log_nonneg htR
  have hbR : (1 : ℝ) ≤ b := (Real.one_le_exp (by positivity)).trans hlarge
  have hb0 : (0 : ℝ) < b := by linarith
  have hden : 0 < Real.log (2*(b : ℝ)) := Real.log_pos (by linarith)
  have hlogb : Real.log (t : ℝ)/6 ≤ Real.log (b : ℝ) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hlarge
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hratio : Real.log (2*(t : ℝ))/Real.log (2*(b : ℝ)) ≤ 6 := by
    apply (div_le_iff₀ hden).mpr
    rw [Real.log_mul (by norm_num) (by linarith : (t : ℝ) ≠ 0),
      Real.log_mul (by norm_num) hb0.ne']
    nlinarith
  have hb : (b : ℝ) ≤ (k : ℝ)*b := by nlinarith
  have hc0 : 0 ≤ (bucketConstant : ℝ) := Nat.cast_nonneg _
  calc
    _ = (bucketConstant : ℝ)*((b : ℝ)+(k : ℝ)*b*
        (Real.log (2*(t : ℝ))/Real.log (2*(b : ℝ)))) := by unfold bucketNumeric; ring
    _ ≤ (bucketConstant : ℝ)*((b : ℝ)+6*(k : ℝ)*b) := by
      have hterm : (k : ℝ)*b*(Real.log (2*(t : ℝ))/Real.log (2*(b : ℝ))) ≤
          6*(k : ℝ)*b := by
        calc
          _ ≤ (k : ℝ)*b*6 := mul_le_mul_of_nonneg_left hratio (by positivity)
          _ = _ := by ring
      exact mul_le_mul_of_nonneg_left (add_le_add (le_refl (b : ℝ)) hterm) hc0
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hb hc0]

theorem bucketNumeric_small (b t k : ℕ) (ht : 1 ≤ t) (hk : 1 ≤ k)
    (hsmall : (b : ℝ) ≤ Real.exp (Real.log (t : ℝ)/6)) :
    bucketNumeric b t k ≤ (bucketConstant : ℝ)*k*(3+2*Real.log (t : ℝ))*
      Real.exp (Real.log (t : ℝ)/6) := by
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hz : 0 ≤ Real.log (t : ℝ) := Real.log_nonneg htR
  by_cases hb : b = 0
  · rw [hb,bucketNumeric_zero]
    positivity
  · have hbR : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
    have hlog2 : (1 : ℝ)/2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hden := Real.log_le_log (by norm_num : (0 : ℝ)<2)
      (show (2 : ℝ) ≤ 2*(b : ℝ) by linarith)
    have hlog2up : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)]
    have hnum : Real.log (2*(t : ℝ)) ≤ 1+Real.log (t : ℝ) := by
      rw [Real.log_mul (by norm_num) (by linarith : (t : ℝ) ≠ 0)]
      linarith
    have hratio : Real.log (2*(t : ℝ))/Real.log (2*(b : ℝ)) ≤
        2*(1+Real.log (t : ℝ)) := by
      apply (div_le_iff₀ (by linarith : 0 < Real.log (2*(b : ℝ)))).mpr
      nlinarith [mul_nonneg hz (sub_nonneg.mpr (hlog2.trans hden))]
    have hb : (b : ℝ) ≤ (k : ℝ)*b := by nlinarith
    have hc0 : 0 ≤ (bucketConstant : ℝ) := Nat.cast_nonneg _
    calc
      _ = (bucketConstant : ℝ)*((b : ℝ)+(k : ℝ)*b*
          (Real.log (2*(t : ℝ))/Real.log (2*(b : ℝ)))) := by unfold bucketNumeric; ring
      _ ≤ (bucketConstant : ℝ)*((b : ℝ)+(k : ℝ)*b*(2*(1+Real.log (t : ℝ)))) := by gcongr
      _ ≤ (bucketConstant : ℝ)*k*(3+2*Real.log (t : ℝ))*b := by
        nlinarith [mul_le_mul_of_nonneg_left hb hc0]
      _ ≤ _ := by gcongr

/-- The explicit exponential-series estimate in section3.3. It supplies the
uniform small-bucket bound without an asymptotic threshold. -/
theorem smallBucket_exponential {z : ℝ} (hz : 0 ≤ z) :
    2*(1+z)*(3+2*z)*Real.exp (z/6) ≤ 354*Real.exp (z/3) := by
  have hu : 0 ≤ z/6 := by positivity
  have h2 := Real.pow_div_factorial_le_exp (z/6) hu 2
  have h1 := Real.pow_div_factorial_le_exp (z/6) hu 1
  norm_num at h2 h1
  have h0 : 1 ≤ Real.exp (z/6) := Real.one_le_exp hu
  have hp : 2*(1+z)*(3+2*z) ≤ 354*Real.exp (z/6) := by nlinarith
  calc
    _ ≤ (354*Real.exp (z/6))*Real.exp (z/6) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_nonneg _)
    _ = _ := by rw [mul_assoc,← Real.exp_add]; congr 2; ring

/-- Summing the actual B bounds over geometric degree buckets costs at most
361*C_B*k*m. Empty buckets contribute zero; small buckets use the sharp
separating bound instead of dense learning. -/
theorem sum_bucketNumeric_le {J : Type} [Fintype J] [DecidableEq J]
    (sizes : J → ℕ) (m t k : ℕ) (ht : 1 ≤ t) (hk : 1 ≤ k)
    (hsum : ∑ j, sizes j ≤ m)
    (hcount : (Fintype.card J : ℝ) ≤ 2*(1+Real.log (t : ℝ)))
    (hm : Real.exp (Real.log (t : ℝ)/3) ≤ m) :
    (∑ j, bucketNumeric (sizes j) t k) ≤ 361*(bucketConstant : ℝ)*k*m := by
  let large : Finset J := univ.filter fun j => Real.exp (Real.log (t : ℝ)/6) ≤ sizes j
  let small : Finset J := univ \ large
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hz : 0 ≤ Real.log (t : ℝ) := Real.log_nonneg htR
  have hc : 0 ≤ (bucketConstant : ℝ) := Nat.cast_nonneg _
  have hsumR : (∑ j, (sizes j : ℝ)) ≤ m := by exact_mod_cast hsum
  have hlargeSum : (∑ j ∈ large, (sizes j : ℝ)) ≤ m := by
    apply (sum_le_sum_of_subset_of_nonneg (subset_univ large)
      (fun j _ _ => Nat.cast_nonneg (sizes j))).trans hsumR
  have hlarge : (∑ j ∈ large, bucketNumeric (sizes j) t k) ≤
      7*(bucketConstant : ℝ)*k*m := by
    calc
      _ ≤ ∑ j ∈ large, 7*(bucketConstant : ℝ)*k*sizes j := by
        apply sum_le_sum
        intro j hj
        exact bucketNumeric_large _ t k ht hk (mem_filter.mp hj).2
      _ = (7*(bucketConstant : ℝ)*k)*(∑ j ∈ large, (sizes j : ℝ)) := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hlargeSum (by positivity)
  have hsmall : (∑ j ∈ small, bucketNumeric (sizes j) t k) ≤
      354*(bucketConstant : ℝ)*k*m := by
    let z := Real.log (t : ℝ)
    have hn : (small.card : ℝ) ≤ Fintype.card J := by exact_mod_cast card_le_univ small
    have hfactor : 0 ≤ (bucketConstant : ℝ)*k*(3+2*z)*Real.exp (z/6) := by
      dsimp [z]
      positivity
    calc
      _ ≤ ∑ _j ∈ small, (bucketConstant : ℝ)*k*(3+2*z)*Real.exp (z/6) := by
        apply sum_le_sum
        intro j hj
        have hn : ¬Real.exp (z/6) ≤ sizes j := by
          intro h
          exact (mem_sdiff.mp hj).2 (mem_filter.mpr ⟨mem_univ _,h⟩)
        exact bucketNumeric_small _ t k ht hk (le_of_not_ge hn)
      _ = (small.card : ℝ)*((bucketConstant : ℝ)*k*(3+2*z)*Real.exp (z/6)) := by simp
      _ ≤ (2*(1+z))*((bucketConstant : ℝ)*k*(3+2*z)*Real.exp (z/6)) :=
        mul_le_mul_of_nonneg_right (hn.trans hcount) hfactor
      _ = ((bucketConstant : ℝ)*k)*(2*(1+z)*(3+2*z)*Real.exp (z/6)) := by ring
      _ ≤ ((bucketConstant : ℝ)*k)*(354*Real.exp (z/3)) :=
        mul_le_mul_of_nonneg_left (smallBucket_exponential hz) (by positivity)
      _ ≤ ((bucketConstant : ℝ)*k)*(354*(m : ℝ)) := by gcongr
      _ = _ := by ring
  have he := sum_sdiff (f := fun j => bucketNumeric (sizes j) t k) (subset_univ large)
  have hsplit : (∑ j, bucketNumeric (sizes j) t k) =
      (∑ j ∈ large, bucketNumeric (sizes j) t k)+∑ j ∈ small, bucketNumeric (sizes j) t k := by
    dsimp only [small]
    exact he.symm.trans (add_comm _ _)
  rw [hsplit]
  nlinarith

def recoveryBucketCount (t : ℕ) : ℕ := 1+Nat.clog 2 t

theorem recovery_clog_bound (t : ℕ) (ht : 1 ≤ t) :
    (Nat.clog 2 t : ℝ) ≤ 2*Real.log (t : ℝ)+1 := by
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hz : 0 ≤ Real.log (t : ℝ) := Real.log_nonneg htR
  have hlog2 : (1/2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hb : Real.logb 2 t ≤ 2*Real.log (t : ℝ) := by
    rw [Real.logb,div_le_iff₀ (by linarith : 0 < Real.log 2)]
    nlinarith [mul_nonneg hz (sub_nonneg.mpr hlog2.le)]
  have hceil : (Nat.clog 2 t : ℝ) ≤ Real.logb 2 t+1 := by
    rw [← Real.natCeil_logb_natCast]
    exact (Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num) htR)).le
  linarith

theorem recoveryBucketCount_bound (t : ℕ) (ht : 1 ≤ t) :
    (recoveryBucketCount t : ℝ) ≤ 2*(1+Real.log (t : ℝ)) := by
  have h := recovery_clog_bound t ht
  unfold recoveryBucketCount
  push_cast
  linarith

/-- The sparse-row branch pays for logarithmic rank searches using the column
term in k*(m+t), including m bounded and t arbitrarily large. -/
theorem tinyRows_search_envelope (m t : ℕ) (ht : 1 ≤ t)
    (hm : (m : ℝ) ≤ Real.exp (Real.log (t : ℝ)/3)) :
    (m : ℝ)*Nat.clog 2 t ≤ 3*(t : ℝ) := by
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hz : 0 ≤ Real.log (t : ℝ) := Real.log_nonneg htR
  have hc := recovery_clog_bound t ht
  have hexp := Real.add_one_le_exp (2*Real.log (t : ℝ)/3)
  have hpoly : 2*Real.log (t : ℝ)+1 ≤ 3*Real.exp (2*Real.log (t : ℝ)/3) := by linarith
  calc
    _ ≤ Real.exp (Real.log (t : ℝ)/3)*(2*Real.log (t : ℝ)+1) :=
      mul_le_mul hm hc (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ ≤ Real.exp (Real.log (t : ℝ)/3)*(3*Real.exp (2*Real.log (t : ℝ)/3)) :=
      mul_le_mul_of_nonneg_left hpoly (Real.exp_nonneg _)
    _ = 3*(t : ℝ) := by
      rw [← mul_assoc,mul_comm (Real.exp _) 3,mul_assoc,← Real.exp_add,
        show Real.log (t : ℝ)/3+2*Real.log (t : ℝ)/3 = Real.log (t : ℝ) by ring,
        Real.exp_log (by linarith)]

theorem tinyRows_original_budget (m t k : ℕ) (ht : 1 ≤ t) (hk : 1 ≤ k)
    (hm : (m : ℝ) ≤ Real.exp (Real.log (t : ℝ)/3)) :
    3*m+3*k*m*Nat.clog 2 t ≤ 12*k*(m+t) := by
  have h := tinyRows_search_envelope m t ht hm
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h' := mul_le_mul_of_nonneg_left h (show 0 ≤ 3*(k : ℝ) by positivity)
  have hkm : (m : ℝ) ≤ (k : ℝ)*m := by nlinarith [(Nat.cast_nonneg m : (0 : ℝ)≤m)]
  exact_mod_cast (show 3*(m : ℝ)+3*(k : ℝ)*m*Nat.clog 2 t ≤
    12*(k : ℝ)*(m+t) by nlinarith [(Nat.cast_nonneg t : (0 : ℝ)≤t)])

end BucketNumerics


section RecoveryProgram

variable {R C : Type} [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C]

/-- Geometric buckets are formed only from the public validated degree table. -/
def degreeBucket (degree : R → ℕ) (k i : ℕ) : Finset R :=
  univ.filter fun u => k*2^i ≤ degree u ∧ degree u < k*2^(i+1)

@[simp] theorem mem_degreeBucket (degree : R → ℕ) (k i : ℕ) (u : R) :
    u ∈ degreeBucket degree k i ↔
      k*2^i ≤ degree u ∧ degree u < k*2^(i+1) := by
  simp [degreeBucket]

theorem degreeBucket_disjoint (degree : R → ℕ) (k : ℕ) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (degreeBucket degree k i) (degreeBucket degree k j) := by
  apply disjoint_left.mpr
  intro u hui huj
  rcases (mem_degreeBucket degree k i u).mp hui with ⟨hli,hui⟩
  rcases (mem_degreeBucket degree k j u).mp huj with ⟨hlj,huj⟩
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hp : (2 : ℕ)^(i+1) ≤ 2^j :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hm := Nat.mul_le_mul_left k hp
    omega
  · have hp : (2 : ℕ)^(j+1) ≤ 2^i :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hm := Nat.mul_le_mul_left k hp
    omega

/-- Every honest measured degree at least k belongs to a public bucket before
the dimension-determined stopping index. No hidden degree is used to select
the operational stopping index. -/
theorem degreeBucket_cover (degree : R → ℕ) (k t : ℕ) (hk : 0 < k)
    (u : R) (hlo : k ≤ degree u) (hhi : degree u ≤ t) :
    ∃ i : Fin (recoveryBucketCount t), u ∈ degreeBucket degree k i.val := by
  let i := Nat.log 2 (degree u/k)
  have hq : 0 < degree u/k := Nat.div_pos hlo hk
  have hlow : k*2^i ≤ degree u := by
    have h := (Nat.le_div_iff_mul_le hk).mp
      (Nat.pow_log_le_self 2 (Nat.ne_of_gt hq))
    simpa only [i,Nat.mul_comm] using h
  have hupp : degree u < k*2^(i+1) := by
    have h := (Nat.div_lt_iff_lt_mul hk).mp
      (Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) (degree u/k))
    simpa only [i,Nat.succ_eq_add_one,Nat.mul_comm] using h
  have hlog : i ≤ Nat.clog 2 t :=
    (Nat.log_mono_right ((Nat.div_le_self (degree u) k).trans hhi)).trans
      (Nat.log_le_clog 2 t)
  have hi : i < recoveryBucketCount t := by
    unfold recoveryBucketCount
    omega
  exact ⟨⟨i,hi⟩,(mem_degreeBucket degree k i u).mpr ⟨hlow,hupp⟩⟩

/-- The §3.3 row-count sum is the exact sum of the constructed buckets, rather
than an assumed list of bucket sizes. -/
theorem degreeBucket_card_sum (degree : R → ℕ) (k t : ℕ) (hk : 0 < k)
    (hdegree : ∀ u, k ≤ degree u ∧ degree u ≤ t) :
    ∑ i : Fin (recoveryBucketCount t), (degreeBucket degree k i.val).card =
      Fintype.card R := by
  have hd : ((univ : Finset (Fin (recoveryBucketCount t))) : Set (Fin (recoveryBucketCount t))).PairwiseDisjoint
      (fun i => degreeBucket degree k i.val) := by
    intro i _ j _ hij
    exact degreeBucket_disjoint degree k (fun he => hij (Fin.ext he))
  have hu : (univ : Finset (Fin (recoveryBucketCount t))).biUnion
      (fun i => degreeBucket degree k i.val) = univ := by
    ext u
    simp only [mem_biUnion,mem_univ,true_and,iff_true]
    exact degreeBucket_cover degree k t hk u (hdegree u).1 (hdegree u).2
  have h := card_biUnion hd
  rw [hu,card_univ] at h
  exact h.symm

theorem degreeBucket_range (degree : R → ℕ) (k i : ℕ)
    (u : degreeBucket degree k i) :
    k*2^i ≤ degree u.val ∧ degree u.val ≤ 2*(k*2^i) := by
  have h := (mem_degreeBucket degree k i u.val).mp u.property
  rw [pow_succ] at h
  constructor
  · exact h.1
  · nlinarith [h.2]

/-- The numerical bucket estimate applied to the actual public partition.
The lower degree promise is used only to prove coverage in the analysis. -/
theorem degreeBucket_numeric_sum (degree : R → ℕ) (k : ℕ) (hk : 1 ≤ k)
    (ht : 1 ≤ Fintype.card C)
    (hdegree : ∀ u, k ≤ degree u ∧ degree u ≤ Fintype.card C)
    (hm : Real.exp (Real.log (Fintype.card C : ℝ)/3) ≤ (Fintype.card R : ℝ)) :
    ∑ i : Fin (recoveryBucketCount (Fintype.card C)),
      bucketNumeric (degreeBucket degree k i.val).card (Fintype.card C) k ≤
      361*(bucketConstant : ℝ)*k*Fintype.card R := by
  apply sum_bucketNumeric_le
    (fun i : Fin (recoveryBucketCount (Fintype.card C)) =>
      (degreeBucket degree k i.val).card) (Fintype.card R) (Fintype.card C) k ht hk
  · exact le_of_eq (degreeBucket_card_sum degree k (Fintype.card C) (by omega) hdegree)
  · simpa only [Fintype.card_fin] using recoveryBucketCount_bound (Fintype.card C) ht
  · exact hm

def liftRowQuery (A : Finset R) (q : BipartiteQuery A C) : BipartiteQuery R C :=
  (q.1.map ⟨Subtype.val,Subtype.val_injective⟩,q.2)

/-- Public row-label substitution has exactly one query per virtual query. -/
def liftRows {O : Type} {q : ℕ} (A : Finset R) (T : RTree (BipartiteQuery A C) ℝ O q) :
    RTree (BipartiteQuery R C) ℝ O q :=
  (T.substitute (fun question => DTree.query (liftRowQuery A question) (fun answer => DTree.pure answer))).cast
    (Nat.mul_one q)

theorem liftRows_run {O : Type} {q : ℕ} (A : Finset R)
    (T : RTree (BipartiteQuery A C) ℝ O q) (read : BipartiteQuery R C → ℝ) :
    RTree.run read (liftRows A T) = RTree.run (fun question => read (liftRowQuery A question)) T := by
  rw [liftRows,RTree.run_cast,substitute_run_exact _ read
    (fun question => read (liftRowQuery A question)) (fun _ => rfl)]
  simp only [Nat.zero_add,Nat.mul_one]
  exact PMF.map_id _

def BucketState.merge (st : BucketState R C) (A : Finset R) (next : BucketState A C) :
    BucketState R C where
  proposal u := if hu : u ∈ A then next.proposal ⟨u,hu⟩ else st.proposal u
  learned u := if hu : u ∈ A then next.learned ⟨u,hu⟩ else st.learned u
  failed := st.failed || next.failed

theorem bucketRoundBudget_subtype (A : Finset R) : bucketRoundBudget A C ≤ bucketRoundBudget R C := by
  simp only [bucketRoundBudget,Fintype.card_coe]
  exact Nat.add_le_add (card_le_univ A) (Nat.mul_le_mul_right _ (card_le_univ A))

/-- Exactly T rounds on one public bucket. Empty buckets and previously failed
states do not issue any further query. -/
def recoverOneBucket (degree : R → ℕ) (k T i : ℕ) (st : BucketState R C) :
    RTree (BipartiteQuery R C) ℝ (BucketState R C) (T*bucketRoundBudget R C) :=
  if st.failed = true then RTree.pure (PMF.pure st) else
    let A := degreeBucket degree k i
    if A = ∅ then RTree.pure (PMF.pure st) else
      ((liftRows A (learnBucketRounds (k*2^i) k T BucketState.initial)).map
        (st.merge A)).weaken (Nat.mul_le_mul_left T (bucketRoundBudget_subtype (C := C) A))

/-- Finite composition through all public degree buckets. It never reads a
hidden degree, a successful event or an expected running-time value. -/
def recoverBuckets (degree : R → ℕ) (k T : ℕ) : (stages : ℕ) → BucketState R C →
    RTree (BipartiteQuery R C) ℝ (BucketState R C) (stages*(T*bucketRoundBudget R C))
  | 0,st => RTree.pure (PMF.pure st)
  | stages+1,st =>
      ((recoverOneBucket degree k T stages st).bind
        (fun next => recoverBuckets degree k T stages next)).cast (by ring)

/-- Recording a rank-selected row uses only the returned explicit list. -/
def BucketState.recordRanks (st : BucketState R C) (u : R) (N : Finset C) : BucketState R C where
  proposal := Function.update st.proposal u (some N)
  learned := Function.update st.learned u (some N)
  failed := st.failed

/-- The fallback processes the public row list, drawing ranks without
replacement using the already measured and validated degrees. -/
def recoverRankRows (degree : R → ℕ) (k : ℕ) : (rows : List R) → BucketState R C →
    RTree (BipartiteQuery R C) ℝ (BucketState R C) (rows.length*(k*searchDepth C))
  | [],st => RTree.pure (PMF.pure st)
  | u::rows,st =>
      if st.failed = true then RTree.pure (PMF.pure st) else
        ((learnRanks u (degree u) k ∅).bind fun out => match out with
          | none => RTree.pure (PMF.pure st.abort)
          | some N => recoverRankRows degree k rows (st.recordRanks u N)).cast
          (by simp only [List.length_cons]; ring)

def recoveryContinuationBudget (R C : Type) [Fintype R] [Fintype C] (k T : ℕ) : ℕ :=
  recoveryBucketCount (Fintype.card C)*(T*bucketRoundBudget R C)+
    Fintype.card R*(k*searchDepth C)

def recoverFiniteBudget (R C : Type) [Fintype R] [Fintype C] (k T : ℕ) : ℕ :=
  Fintype.card R+recoveryContinuationBudget R C k T

/-- The final branch decision depends only on dimensions; natural degrees are
used only after range validation. The caller will impose an actual query cap. -/
def recoverRounds (k T : ℕ) :
    RTree (BipartiteQuery R C) ℝ (BucketState R C) (recoverFiniteBudget R C k T) :=
  if Fintype.card R = 0 then RTree.pure (PMF.pure BucketState.initial) else
    (RTree.ofDeterministic (rowCountProgram (univ : Finset R) (univ : Finset C))).bind
      (fun out => match out with
        | none => RTree.pure (PMF.pure (BucketState.initial : BucketState R C).abort)
        | some degree =>
            if 10 ≤ k ∧ ∀ u, k ≤ degree u then
              if Real.exp (Real.log (Fintype.card C : ℝ)/3) ≤ (Fintype.card R : ℝ) then
                (recoverBuckets degree k T (recoveryBucketCount (Fintype.card C))
                  BucketState.initial).weaken
                  (show recoveryBucketCount (Fintype.card C)*(T*bucketRoundBudget R C) ≤
                    recoveryContinuationBudget R C k T by
                    unfold recoveryContinuationBudget
                    exact Nat.le_add_right _ _)
              else
                (recoverRankRows degree k (univ : Finset R).toList BucketState.initial).weaken
                  (show (univ : Finset R).toList.length*(k*searchDepth C) ≤
                    recoveryContinuationBudget R C k T by
                    simp only [length_toList,card_univ,recoveryContinuationBudget]
                    omega)
            else RTree.pure (PMF.pure (BucketState.initial : BucketState R C).abort)) |>.cast
        (by simp only [card_univ,recoverFiniteBudget])

theorem recoverRounds_every_oracle (k T : ℕ) (read : BipartiteQuery R C → ℝ)
    {out : BucketState R C × ℕ}
    (hout : out ∈ (RTree.run read (recoverRounds (R := R) (C := C) k T)).support) :
    out.2 ≤ recoverFiniteBudget R C k T := RTree.cost_le _ _ hout

/-- Fixed classical recovery constants; the B constant is already a concrete
natural number rather than an uninstantiated primitive hypothesis. -/
def recoveryCoefficient : ℕ := 3*(1+400*bucketConstant)

def recoveryHardCoefficient : ℕ := 100*recoveryCoefficient+12

def recoverClock (R C : Type) [Fintype R] [Fintype C] (k : ℕ) : ℕ :=
  recoveryHardCoefficient*k*(Fintype.card R+Fintype.card C)

private theorem expected_cast {I A O : Type} {q q' : ℕ} (T : RTree I A O q)
    (h : q = q') (read : I → A) :
    (T.cast h).expectedQueries read = T.expectedQueries read := by
  unfold RTree.expectedQueries
  rw [RTree.run_cast]

private theorem expected_weaken {I A O : Type} {q q' : ℕ} (T : RTree I A O q)
    (h : q ≤ q') (read : I → A) :
    (T.weaken h).expectedQueries read = T.expectedQueries read := by
  unfold RTree.expectedQueries
  rw [RTree.run_weaken]

private theorem expected_pure {I A O : Type} (q : ℕ) (p : PMF O) (read : I → A) :
    (RTree.pure (q := q) p).expectedQueries read = 0 := by
  change expect (RTree.run read (RTree.pure p)) (fun out => (out.2 : ℝ≥0∞)) = 0
  rw [RTree.run_pure,expect_map]
  simpa only [Nat.cast_zero] using CutQueryComplexity.Probability.expect_const p 0

theorem recovery_expected_bind {I A O P : Type} {q r : ℕ}
    (T : RTree I A O q) (f : O → RTree I A P r) (read : I → A) :
    (T.bind f).expectedQueries read = T.expectedQueries read +
      expect (T.eval read) (fun out => (f out).expectedQueries read) := by
  change expect (RTree.run read (T.bind f)) (fun out => (out.2 : ℝ≥0∞)) = _
  rw [RTree.run_bind,expect_bind]
  simp only [expect_map,Nat.cast_add,expect_add,expect_const]
  change _ + expect (RTree.run read T) (fun out => (f out.1).expectedQueries read) =
    _ + expect ((RTree.run read T).map Prod.fst) (fun out => (f out).expectedQueries read)
  simp only [expect_map] <;> rfl

private theorem expected_map {I A O P : Type} {q : ℕ} (T : RTree I A O q)
    (f : O → P) (read : I → A) :
    (T.map f).expectedQueries read = T.expectedQueries read := by
  rw [RTree.map,expected_cast,recovery_expected_bind]
  simp only [expected_pure,expect_const,add_zero]

private theorem recovery_run_map {I A O P : Type} {q : ℕ} (T : RTree I A O q)
    (f : O → P) (read : I → A) :
    RTree.run read (T.map f) = (RTree.run read T).map (fun out => (f out.1,out.2)) := by
  rw [RTree.map,RTree.run_cast,RTree.run_bind]
  simp only [RTree.run_pure,PMF.pure_map,Nat.add_zero]
  rfl

theorem liftRows_expected {O : Type} {q : ℕ} (A : Finset R)
    (T : RTree (BipartiteQuery A C) ℝ O q) (read : BipartiteQuery R C → ℝ) :
    (liftRows A T).expectedQueries read =
      T.expectedQueries (fun question => read (liftRowQuery A question)) := by
  unfold RTree.expectedQueries
  rw [liftRows_run]

theorem liftRowQuery_bilinear (M : BooleanMatrix R C) (A : Finset R)
    (q : BipartiteQuery A C) :
    bilinear M (liftRowQuery A q) = bilinear (fun u : A => M u.val) q := by
  simp only [bilinear,liftRowQuery,sum_map,Function.Embedding.coeFn_mk]

theorem BucketInvariant.merge (M : BooleanMatrix R C) (k : ℕ)
    (st : BucketState R C) (A : Finset R) (next : BucketState A C)
    (hst : BucketInvariant M k st) (hn : BucketInvariant (fun u : A => M u.val) k next) :
    BucketInvariant M k (st.merge A next) := by
  refine ⟨by simp only [BucketState.merge,hst.1,hn.1,Bool.or_false],?_⟩
  intro u
  by_cases hu : u ∈ A
  · simpa only [BucketState.merge,dite_eq_left hu] using hn.2 ⟨u,hu⟩
  · simpa only [BucketState.merge,dite_eq_right hu] using hst.2 u

theorem BucketInvariant.recordRanks (M : BooleanMatrix R C) (k : ℕ)
    (st : BucketState R C) (u : R) (N : Finset C) (hst : BucketInvariant M k st)
    (hN : ∀ c ∈ N, M u c = true) (hsize : k ≤ N.card) :
    BucketInvariant M k (st.recordRanks u N) := by
  refine ⟨hst.1,?_⟩
  intro v
  by_cases hv : v = u
  · subst v
    simp only [BucketState.recordRanks,Function.update_self,Option.some_ne_none,iff_self,true_and]
    intro S hS
    have he : N = S := Option.some.inj hS
    subst S
    have hfilter : N.filter (fun c => M u c) = N := filter_eq_self.mpr hN
    rw [hfilter]
    exact ⟨rfl,hsize⟩
  · simpa only [BucketState.recordRanks,Function.update_of_ne hv] using hst.2 v

/-- Honest execution of a bucket is exactly execution on its row subtype,
followed by public state merging. This also records the unchanged actual cost. -/
theorem recoverOneBucket_honest_run (M : BooleanMatrix R C) (degree : R → ℕ)
    (k T i : ℕ) (st : BucketState R C) (hf : st.failed = false) :
    let A := degreeBucket degree k i
    RTree.run (fun q => (bilinear M q : ℝ)) (recoverOneBucket degree k T i st) =
      if A = ∅ then PMF.pure (st,0) else
        (RTree.run (fun q => (bilinear (fun u : A => M u.val) q : ℝ))
          (learnBucketRounds (k*2^i) k T BucketState.initial)).map
            (fun out => (st.merge A out.1,out.2)) := by
  dsimp only
  rw [recoverOneBucket,ite_eq_right (by simp [hf])]
  dsimp only
  split
  · simp only [RTree.run_pure,PMF.pure_map]
  · rw [RTree.run_weaken,recovery_run_map,liftRows_run]
    have hread : (fun q => (bilinear M (liftRowQuery (degreeBucket degree k i) q) : ℝ)) =
        (fun q => (bilinear (fun u : degreeBucket degree k i => M u.val) q : ℝ)) := by
      funext q
      rw [liftRowQuery_bilinear]
    rw [hread]

theorem recoverOneBucket_invariant (M : BooleanMatrix R C) (degree : R → ℕ)
    (k T i : ℕ) (st : BucketState R C) (hst : BucketInvariant M k st)
    {out : BucketState R C × ℕ}
    (hout : out ∈ (RTree.run (fun q => (bilinear M q : ℝ))
      (recoverOneBucket degree k T i st)).support) : BucketInvariant M k out.1 := by
  rw [recoverOneBucket_honest_run M degree k T i st hst.1] at hout
  split at hout
  · have he : out = (st,0) := (PMF.mem_support_pure_iff _ _).mp hout
    simpa only [he] using hst
  · obtain ⟨next,hnext,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
    exact BucketInvariant.merge M k st _ next.1 hst
      (learnBucketRounds_invariant _ (k*2^i) k T BucketState.initial
        (BucketInvariant.initial _ _) hnext)

theorem recoverBuckets_invariant (M : BooleanMatrix R C) (degree : R → ℕ)
    (k T stages : ℕ) (st : BucketState R C) (hst : BucketInvariant M k st)
    {out : BucketState R C × ℕ}
    (hout : out ∈ (RTree.run (fun q => (bilinear M q : ℝ))
      (recoverBuckets degree k T stages st)).support) : BucketInvariant M k out.1 := by
  induction stages generalizing st out with
  | zero =>
      have he : out = (st,0) := by
        simpa only [recoverBuckets,RTree.run_pure,PMF.pure_map,PMF.mem_support_pure_iff] using hout
      simpa only [he] using hst
  | succ stages ih =>
      rw [recoverBuckets,RTree.run_cast,RTree.run_bind] at hout
      obtain ⟨first,hfirst,hlater⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
      obtain ⟨later,hrest,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hlater
      exact ih first.1 (recoverOneBucket_invariant M degree k T stages st hst hfirst)
        (out := later) hrest

/-- A bucket updates only its own rows. An unfinished row in that bucket forces
at least T actual queries, by the checked finite round-progress mechanism. -/
theorem recoverOneBucket_row_progress (M : BooleanMatrix R C) (degree : R → ℕ)
    (k T i : ℕ) (st : BucketState R C) (hf : st.failed = false) (u : R)
    {out : BucketState R C × ℕ}
    (hout : out ∈ (RTree.run (fun q => (bilinear M q : ℝ))
      (recoverOneBucket degree k T i st)).support) :
    (u ∉ degreeBucket degree k i → out.1.proposal u = st.proposal u) ∧
    (u ∈ degreeBucket degree k i → out.1.proposal u = none → T ≤ out.2) := by
  rw [recoverOneBucket_honest_run M degree k T i st hf] at hout
  split at hout
  · rename_i hA
    have he : out = (st,0) := (PMF.mem_support_pure_iff _ _).mp hout
    subst out
    refine ⟨fun _ => rfl,?_⟩
    intro hu
    have hfalse : False := by simpa only [hA,notMem_empty] using hu
    exact hfalse.elim
  · obtain ⟨next,hnext,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
    constructor
    · intro hu
      simp only [BucketState.merge,dite_eq_right hu]
    · intro hu hnone
      have hlocal : next.1.proposal ⟨u,hu⟩ = none := by
        simpa only [BucketState.merge,dite_eq_left hu] using hnone
      have hnonempty : next.1.pending.Nonempty := by
        exact ⟨⟨u,hu⟩,by simp [BucketState.pending,pendingRows,hlocal]⟩
      exact (learnBucketRounds_progress (fun v : degreeBucket degree k i => M v.val)
        (k*2^i) k T BucketState.initial rfl hnext).2.2 hnonempty

theorem recoverBuckets_outside (M : BooleanMatrix R C) (degree : R → ℕ)
    (k T stages : ℕ) (st : BucketState R C) (hst : BucketInvariant M k st) (u : R)
    (hu : ∀ i < stages, u ∉ degreeBucket degree k i) {out : BucketState R C × ℕ}
    (hout : out ∈ (RTree.run (fun q => (bilinear M q : ℝ))
      (recoverBuckets degree k T stages st)).support) : out.1.proposal u = st.proposal u := by
  induction stages generalizing st out with
  | zero =>
      have he : out = (st,0) := by
        simpa only [recoverBuckets,RTree.run_pure,PMF.pure_map,PMF.mem_support_pure_iff] using hout
      simp only [he]
  | succ stages ih =>
      rw [recoverBuckets,RTree.run_cast,RTree.run_bind] at hout
      obtain ⟨first,hfirst,hlater⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
      obtain ⟨later,hrest,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hlater
      have hfirstInv := recoverOneBucket_invariant M degree k T stages st hst hfirst
      have hl := ih first.1 hfirstInv (fun i hi => hu i (by omega)) hrest
      have hf := (recoverOneBucket_row_progress M degree k T stages st hst.1 u hfirst).1
        (hu stages (by omega))
      exact hl.trans hf

/-- Honest states determine a learned row from its retained proposal. -/
theorem BucketInvariant.learned_eq_of_proposal_eq (M : BooleanMatrix R C) (k : ℕ)
    (st next : BucketState R C) (hst : BucketInvariant M k st) (hnext : BucketInvariant M k next)
    (u : R) (he : next.proposal u = st.proposal u) : next.learned u = st.learned u := by
  cases hp : st.proposal u with
  | none =>
      have hp' : next.proposal u = none := he.trans hp
      rw [(hst.2 u).1.mp hp,(hnext.2 u).1.mp hp']
  | some S =>
      have hp' : next.proposal u = some S := he.trans hp
      rw [((hst.2 u).2 S hp).1,((hnext.2 u).2 S hp').1]

/-- Rows outside the remaining degree buckets keep their learned lists exactly. -/
theorem recoverBuckets_outside_learned_law (M : BooleanMatrix R C) (degree : R → ℕ)
    (k T stages : ℕ) (st : BucketState R C) (hst : BucketInvariant M k st) (u : R)
    (hu : ∀ i < stages, u ∉ degreeBucket degree k i) :
    ((recoverBuckets degree k T stages st).eval (fun q => (bilinear M q : ℝ))).map
      (fun next => next.learned u) = PMF.pure (st.learned u) := by
  rw [RTree.eval,PMF.map_comp]
  calc
    _ = (RTree.run (fun q => (bilinear M q : ℝ)) (recoverBuckets degree k T stages st)).map
        (fun _ => st.learned u) := by
      apply recovery_map_equal_on_support
      intro out hout
      exact BucketInvariant.learned_eq_of_proposal_eq M k st out.1 hst
        (recoverBuckets_invariant M degree k T stages st hst hout) u
        (recoverBuckets_outside M degree k T stages st hst u hu hout)
    _ = _ := PMF.map_const _ _

/-- The one-bucket row law is independent of the previously recorded other
rows, because the implementation runs a fresh local state on that public bucket. -/
theorem recoverOneBucket_learned_law (M : BooleanMatrix R C) (degree : R → ℕ)
    (k T i : ℕ) (st : BucketState R C) (hf : st.failed = false) (u : R)
    (hu : u ∈ degreeBucket degree k i) :
    ((recoverOneBucket degree k T i st).eval (fun q => (bilinear M q : ℝ))).map
      (fun next => next.learned u) =
    ((learnBucketRounds (k*2^i) k T (BucketState.initial : BucketState (degreeBucket degree k i) C)).eval
      (fun q => (bilinear (fun v : degreeBucket degree k i => M v.val) q : ℝ))).map
      (fun next => next.learned ⟨u,hu⟩) := by
  have hA : degreeBucket degree k i ≠ ∅ := (show (degreeBucket degree k i).Nonempty from ⟨u,hu⟩).ne_empty
  simp only [RTree.eval,PMF.map_comp]
  rw [recoverOneBucket_honest_run M degree k T i st hf,ite_eq_right hA,PMF.map_comp]
  congr 1
  funext out
  simp only [Function.comp_def,BucketState.merge,dite_eq_left hu]

/-- Exact pre-cap learned marginal through the sequential bucket composition.
Earlier and later buckets are accounted for by public state updates; no joint
row independence premise is used. -/
theorem recoverBuckets_learned_law (M : BooleanMatrix R C) (degree : R → ℕ)
    (k T stages : ℕ) (st : BucketState R C) (hst : BucketInvariant M k st)
    (u : R) (i : ℕ) (hi : i < stages) (hu : u ∈ degreeBucket degree k i) :
    ((recoverBuckets degree k T stages st).eval (fun q => (bilinear M q : ℝ))).map
      (fun next => next.learned u) =
    ((learnBucketRounds (k*2^i) k T (BucketState.initial : BucketState (degreeBucket degree k i) C)).eval
      (fun q => (bilinear (fun v : degreeBucket degree k i => M v.val) q : ℝ))).map
      (fun next => next.learned ⟨u,hu⟩) := by
  induction stages generalizing st with
  | zero => omega
  | succ stages ih =>
      rw [recoverBuckets,RTree.eval_cast,RTree.eval_bind,PMF.map_bind]
      have hinv : ∀ next ∈ ((recoverOneBucket degree k T stages st).eval
          (fun q => (bilinear M q : ℝ))).support, BucketInvariant M k next := by
        intro next hnext
        obtain ⟨out,hout,he⟩ := (PMF.mem_support_map_iff _ _ _).mp hnext
        simpa only [he] using recoverOneBucket_invariant M degree k T stages st hst hout
      by_cases hi' : i < stages
      · calc
          _ = ((recoverOneBucket degree k T stages st).eval (fun q => (bilinear M q : ℝ))).bind
              (fun _ => ((learnBucketRounds (k*2^i) k T
                (BucketState.initial : BucketState (degreeBucket degree k i) C)).eval
                (fun q => (bilinear (fun v : degreeBucket degree k i => M v.val) q : ℝ))).map
                  (fun next => next.learned ⟨u,hu⟩)) := by
            apply pmf_bind_congr_on_support
            intro next hnext
            exact ih next (hinv next hnext) hi'
          _ = _ := PMF.bind_const _ _
      · have hieq : i = stages := by omega
        subst i
        have houtside : ∀ j < stages, u ∉ degreeBucket degree k j := by
          intro j hj huj
          exact (disjoint_left.mp (degreeBucket_disjoint degree k (by omega : stages ≠ j))) hu huj
        calc
          _ = ((recoverOneBucket degree k T stages st).eval (fun q => (bilinear M q : ℝ))).bind
              (fun next => PMF.pure (next.learned u)) := by
            apply pmf_bind_congr_on_support
            intro next hnext
            exact recoverBuckets_outside_learned_law M degree k T stages next (hinv next hnext) u houtside
          _ = ((recoverOneBucket degree k T stages st).eval (fun q => (bilinear M q : ℝ))).map
              (fun next => next.learned u) := rfl
          _ = _ := recoverOneBucket_learned_law M degree k T stages st hst.1 u hu

theorem recoverBuckets_row_progress (M : BooleanMatrix R C) (degree : R → ℕ)
    (k T stages : ℕ) (st : BucketState R C) (hst : BucketInvariant M k st)
    (u : R) (i : ℕ) (hi : i < stages) (hu : u ∈ degreeBucket degree k i)
    {out : BucketState R C × ℕ}
    (hout : out ∈ (RTree.run (fun q => (bilinear M q : ℝ))
      (recoverBuckets degree k T stages st)).support)
    (hnone : out.1.proposal u = none) : T ≤ out.2 := by
  induction stages generalizing st out with
  | zero => omega
  | succ stages ih =>
      rw [recoverBuckets,RTree.run_cast,RTree.run_bind] at hout
      obtain ⟨first,hfirst,hlater⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
      obtain ⟨later,hrest,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hlater
      have hfirstInv := recoverOneBucket_invariant M degree k T stages st hst hfirst
      by_cases hi' : i < stages
      · have hcost := ih first.1 hfirstInv hi' hrest hnone
        dsimp only
        omega
      · have hieq : i = stages := by omega
        subst i
        have houtside : ∀ j < stages, u ∉ degreeBucket degree k j := by
          intro j hj huj
          exact (disjoint_left.mp (degreeBucket_disjoint degree k (by omega : stages ≠ j))) hu huj
        have hframe := recoverBuckets_outside M degree k T stages first.1 hfirstInv u houtside hrest
        have hfirstNone : first.1.proposal u = none := hframe.symm.trans hnone
        have hcost := (recoverOneBucket_row_progress M degree k T stages st hst.1 u hfirst).2 hu hfirstNone
        dsimp only
        omega

theorem recoverBuckets_unfinished_cost (M : BooleanMatrix R C) (degree : R → ℕ)
    (k T : ℕ) (hk : 0 < k)
    (hdegree : ∀ u, k ≤ degree u ∧ degree u ≤ Fintype.card C)
    {out : BucketState R C × ℕ}
    (hout : out ∈ (RTree.run (fun q => (bilinear M q : ℝ))
      (recoverBuckets degree k T (recoveryBucketCount (Fintype.card C)) BucketState.initial)).support)
    (hunfinished : out.1.pending.Nonempty) : T ≤ out.2 := by
  obtain ⟨u,hu⟩ := hunfinished
  obtain ⟨i,hi⟩ := degreeBucket_cover degree k (Fintype.card C) hk u (hdegree u).1 (hdegree u).2
  exact recoverBuckets_row_progress M degree k T _ BucketState.initial (BucketInvariant.initial M k)
    u i.val i.isLt hi hout (mem_filter.mp hu).2

theorem BucketInvariant.completed_true_neighbors (M : BooleanMatrix R C) (k : ℕ)
    (st : BucketState R C) (h : BucketInvariant M k st) (hc : st.complete) :
    ∀ u, ∃ N, st.learned u = some N ∧ k ≤ N.card ∧ ∀ c ∈ N, M u c = true := by
  intro u
  have hp : st.proposal u ≠ none := by
    intro hp
    have hm : u ∈ st.pending := by simp [BucketState.pending,pendingRows,hp]
    rw [hc.2] at hm
    exact notMem_empty u hm
  obtain ⟨S,hS⟩ := Option.ne_none_iff_exists'.mp hp
  obtain ⟨hlearn,hsize⟩ := (h.2 u).2 S hS
  exact ⟨S.filter (fun c => M u c),hlearn,hsize,fun c hc => (mem_filter.mp hc).2⟩

/-- One actual bucket has the proved B expectation, even when earlier buckets
have produced an arbitrary public state. All hidden facts are proof-side. -/
theorem recoverOneBucket_expected (M : BooleanMatrix R C) (degree : R → ℕ)
    (k T i : ℕ) (st : BucketState R C) (hk : 10 ≤ k) (ht : 1 ≤ Fintype.card C)
    (hdegree : ∀ u, degree u = sampleCount (M u) univ) :
    (recoverOneBucket degree k T i st).expectedQueries (fun q => (bilinear M q : ℝ)) ≤
      ENNReal.ofReal (bucketNumeric (degreeBucket degree k i).card (Fintype.card C) k) := by
  unfold recoverOneBucket
  split
  · rw [expected_pure]
    exact bot_le
  · dsimp only
    split
    · rw [expected_pure]
      exact bot_le
    · rename_i hA
      let A := degreeBucket degree k i
      have hs : 1 ≤ Fintype.card A := by
        simp only [Fintype.card_coe]
        exact card_pos.mpr (nonempty_iff_ne_empty.mpr hA)
      have hkr : k ≤ k*2^i := by
        have hp : 1 ≤ (2 : ℕ)^i := Nat.one_le_pow i 2 (by omega)
        nlinarith
      have hrange : ∀ u : A,
          k*2^i ≤ sampleCount (M u.val) univ ∧
            sampleCount (M u.val) univ ≤ 2*(k*2^i) := by
        intro u
        simpa only [hdegree u.val] using degreeBucket_range degree k i u
      rw [expected_weaken,expected_map,liftRows_expected]
      have he : (fun question => (bilinear M (liftRowQuery A question) : ℝ)) =
          (fun question => (bilinear (fun u : A => M u.val) question : ℝ)) := by
        funext q
        rw [liftRowQuery_bilinear]
      rw [he]
      have h := learnBucketRounds_expected_bound (fun u : A => M u.val)
        (k*2^i) k T hk hkr hs ht hrange
      simpa only [bucketExpectedBound,bucketNumeric,Fintype.card_coe] using h

/-- Expected costs add through the actual finite sequential bucket program.
No independence between row outputs or bucket completion events is assumed. -/
theorem recoverBuckets_expected (M : BooleanMatrix R C) (degree : R → ℕ)
    (k T stages : ℕ) (st : BucketState R C) (hk : 10 ≤ k) (ht : 1 ≤ Fintype.card C)
    (hdegree : ∀ u, degree u = sampleCount (M u) univ) :
    (recoverBuckets degree k T stages st).expectedQueries (fun q => (bilinear M q : ℝ)) ≤
      ∑ i ∈ range stages,
        ENNReal.ofReal (bucketNumeric (degreeBucket degree k i).card (Fintype.card C) k) := by
  induction stages generalizing st with
  | zero => simp only [recoverBuckets,expected_pure,range_zero,sum_empty,le_refl]
  | succ stages ih =>
      rw [recoverBuckets,expected_cast,recovery_expected_bind,sum_range_succ]
      have hfirst := recoverOneBucket_expected M degree k T stages st hk ht hdegree
      have hlater : expect ((recoverOneBucket degree k T stages st).eval
          (fun q => (bilinear M q : ℝ)))
          (fun next => (recoverBuckets degree k T stages next).expectedQueries
            (fun q => (bilinear M q : ℝ))) ≤
          ∑ i ∈ range stages,
            ENNReal.ofReal (bucketNumeric (degreeBucket degree k i).card (Fintype.card C) k) :=
        expect_le_of_le_on_support _ (fun next _ => ih next)
      exact (add_le_add hfirst hlater).trans_eq (add_comm _ _)

theorem recoverBuckets_expected_linear (M : BooleanMatrix R C) (degree : R → ℕ)
    (k T : ℕ) (st : BucketState R C) (hk : 10 ≤ k) (ht : 1 ≤ Fintype.card C)
    (hdegree : ∀ u, degree u = sampleCount (M u) univ)
    (hlo : ∀ u, k ≤ degree u)
    (hm : Real.exp (Real.log (Fintype.card C : ℝ)/3) ≤ (Fintype.card R : ℝ)) :
    (recoverBuckets degree k T (recoveryBucketCount (Fintype.card C)) st).expectedQueries
      (fun q => (bilinear M q : ℝ)) ≤
      ENNReal.ofReal (361*(bucketConstant : ℝ)*k*Fintype.card R) := by
  have h := recoverBuckets_expected M degree k T (recoveryBucketCount (Fintype.card C)) st hk ht hdegree
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ =>
    bucketNumeric_nonneg (degreeBucket degree k i).card (Fintype.card C) k ht)] at h
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  have hbound := degreeBucket_numeric_sum (C := C) degree k (by omega) ht
    (fun u => ⟨hlo u,by rw [hdegree u]; exact sampleCount_le_card (M u) univ |>.trans_eq (card_univ)⟩) hm
  rw [Fin.sum_univ_eq_sum_range
    (fun i => bucketNumeric (degreeBucket degree k i).card (Fintype.card C) k)
    (recoveryBucketCount (Fintype.card C))] at hbound
  exact hbound

def fullDegrees (M : BooleanMatrix R C) : R → ℕ := fun u => sampleCount (M u) univ

theorem honestRowCounts_univ (M : BooleanMatrix R C) :
    honestRowCounts M univ univ = fullDegrees M := by
  funext u
  simp only [honestRowCounts,mem_univ,ite_true,fullDegrees]

/-- Rank rows preserve honest learned information and remove every processed
row from the pending set. This proof uses actual successful rank executions. -/
theorem recoverRankRows_correct (M : BooleanMatrix R C) (k : ℕ) (rows : List R)
    (st : BucketState R C) (hst : BucketInvariant M k st)
    (hdegree : ∀ u ∈ rows, k ≤ fullDegrees M u) {out : BucketState R C}
    (hout : out ∈ ((recoverRankRows (fullDegrees M) k rows st).eval
      (fun q => (bilinear M q : ℝ))).support) :
    BucketInvariant M k out ∧
      ∀ u, out.proposal u = none → st.proposal u = none ∧ u ∉ rows := by
  induction rows generalizing st out with
  | nil =>
      have he : out = st := by
        simpa only [recoverRankRows,RTree.eval_pure,PMF.mem_support_pure_iff] using hout
      subst out
      exact ⟨hst,fun u hu => ⟨hu,by simp⟩⟩
  | cons u rows ih =>
      rw [recoverRankRows,ite_eq_right (by simp [hst.1]),RTree.eval_cast,RTree.eval_bind] at hout
      obtain ⟨first,hfirst,hlater⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
      obtain ⟨N,hN,hcard,htrue⟩ := learnRanks_initial_correct M u k
        (hdegree u List.mem_cons_self) hfirst
      subst first
      have hst' := BucketInvariant.recordRanks M k st u N hst htrue (by omega)
      obtain ⟨hfinal,hpending⟩ := ih (st.recordRanks u N) hst'
        (fun v hv => hdegree v (List.mem_cons_of_mem _ hv)) hlater
      refine ⟨hfinal,?_⟩
      intro v hv
      obtain ⟨hbefore,hnot⟩ := hpending v hv
      have hvu : v ≠ u := by
        intro he
        subst v
        simpa only [BucketState.recordRanks,Function.update_self,Option.some_ne_none] using hbefore
      refine ⟨?_,?_⟩
      · simpa only [BucketState.recordRanks,Function.update_of_ne hvu] using hbefore
      · simp only [List.mem_cons,not_or]
        exact ⟨hvu,hnot⟩

/-- Rank processing leaves every unlisted row unchanged. -/
theorem recoverRankRows_outside_learned (M : BooleanMatrix R C) (k : ℕ) (rows : List R)
    (st : BucketState R C) (hst : BucketInvariant M k st)
    (hdegree : ∀ v ∈ rows, k ≤ fullDegrees M v) (u : R) (hu : u ∉ rows)
    {out : BucketState R C}
    (hout : out ∈ ((recoverRankRows (fullDegrees M) k rows st).eval
      (fun q => (bilinear M q : ℝ))).support) : out.learned u = st.learned u := by
  induction rows generalizing st with
  | nil =>
      have he : out = st := by simpa only [recoverRankRows,RTree.eval_pure,PMF.mem_support_pure_iff] using hout
      simp only [he]
  | cons v rows ih =>
      rw [recoverRankRows,ite_eq_right (by simp [hst.1]),RTree.eval_cast,RTree.eval_bind] at hout
      obtain ⟨first,hfirst,hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
      obtain ⟨N,hN,hcard,htrue⟩ := learnRanks_initial_correct M v k
        (hdegree v List.mem_cons_self) hfirst
      subst first
      have hst' := BucketInvariant.recordRanks M k st v N hst htrue (by omega)
      have hnot : u ≠ v ∧ u ∉ rows := by simpa only [List.mem_cons,not_or] using hu
      have hl := ih (st.recordRanks v N) hst' (fun w hw => hdegree w (List.mem_cons_of_mem _ hw))
        hnot.2 hrest
      simpa only [BucketState.recordRanks,Function.update_of_ne hnot.1] using hl

theorem recoverRankRows_outside_learned_law (M : BooleanMatrix R C) (k : ℕ) (rows : List R)
    (st : BucketState R C) (hst : BucketInvariant M k st)
    (hdegree : ∀ v ∈ rows, k ≤ fullDegrees M v) (u : R) (hu : u ∉ rows) :
    ((recoverRankRows (fullDegrees M) k rows st).eval (fun q => (bilinear M q : ℝ))).map
      (fun next => next.learned u) = PMF.pure (st.learned u) := by
  calc
    _ = ((recoverRankRows (fullDegrees M) k rows st).eval (fun q => (bilinear M q : ℝ))).map
        (fun _ => st.learned u) := by
      apply recovery_map_equal_on_support
      intro out hout
      exact recoverRankRows_outside_learned M k rows st hst hdegree u hu hout
    _ = _ := PMF.map_const _ _

/-- The actual fallback's row marginal through all preceding and following
rank draws. Distinct row labels are processed once; no prior output is supplied
as a conditional-distribution assumption. -/
theorem recoverRankRows_learned_law (M : BooleanMatrix R C) (k : ℕ) (rows : List R)
    (hnodup : rows.Nodup) (st : BucketState R C) (hst : BucketInvariant M k st)
    (hdegree : ∀ v ∈ rows, k ≤ fullDegrees M v) (u : R) (hu : u ∈ rows) :
    ((recoverRankRows (fullDegrees M) k rows st).eval (fun q => (bilinear M q : ℝ))).map
      (fun next => next.learned u) =
      (learnRanks u (fullDegrees M u) k ∅).eval (fun q => (bilinear M q : ℝ)) := by
  induction rows generalizing st with
  | nil => simp only [List.not_mem_nil] at hu
  | cons v rows ih =>
      obtain ⟨hvrows,hnodup'⟩ := List.nodup_cons.mp hnodup
      have hdrest : ∀ w ∈ rows, k ≤ fullDegrees M w := fun w hw => hdegree w (List.mem_cons_of_mem _ hw)
      rw [recoverRankRows,ite_eq_right (by simp [hst.1]),RTree.eval_cast,RTree.eval_bind,PMF.map_bind]
      by_cases huv : u = v
      · subst u
        calc
          _ = ((learnRanks v (fullDegrees M v) k ∅).eval (fun q => (bilinear M q : ℝ))).bind
              (fun o => PMF.pure o) := by
            apply pmf_bind_congr_on_support
            intro o ho
            obtain ⟨N,hN,hcard,htrue⟩ := learnRanks_initial_correct M v k
              (hdegree v List.mem_cons_self) ho
            subst o
            have hst' := BucketInvariant.recordRanks M k st v N hst htrue (by omega)
            simpa only [BucketState.recordRanks,Function.update_self] using
              recoverRankRows_outside_learned_law M k rows (st.recordRanks v N) hst' hdrest v hvrows
          _ = _ := PMF.bind_pure _
      · have hurest : u ∈ rows := (List.mem_cons.mp hu).resolve_left huv
        calc
          _ = ((learnRanks v (fullDegrees M v) k ∅).eval (fun q => (bilinear M q : ℝ))).bind
              (fun _ => (learnRanks u (fullDegrees M u) k ∅).eval (fun q => (bilinear M q : ℝ))) := by
            apply pmf_bind_congr_on_support
            intro o ho
            obtain ⟨N,hN,hcard,htrue⟩ := learnRanks_initial_correct M v k
              (hdegree v List.mem_cons_self) ho
            subst o
            have hst' := BucketInvariant.recordRanks M k st v N hst htrue (by omega)
            exact ih hnodup' (st.recordRanks v N) hst' hdrest hurest
          _ = _ := PMF.bind_const _ _

theorem recoverRankRows_complete (M : BooleanMatrix R C) (k : ℕ)
    (hdegree : ∀ u, k ≤ fullDegrees M u) {out : BucketState R C}
    (hout : out ∈ ((recoverRankRows (fullDegrees M) k (univ : Finset R).toList
      BucketState.initial).eval (fun q => (bilinear M q : ℝ))).support) :
    BucketInvariant M k out ∧ out.complete := by
  obtain ⟨hinv,hpending⟩ := recoverRankRows_correct M k (univ : Finset R).toList
    BucketState.initial (BucketInvariant.initial M k) (fun u _ => hdegree u) hout
  refine ⟨hinv,hinv.1,?_⟩
  apply eq_empty_iff_forall_notMem.mpr
  intro u hu
  have hnone : out.proposal u = none := (mem_filter.mp hu).2
  exact (hpending u hnone).2 (by simp)

/-- The full recovery program's learned table is honest on every supported
true-input execution. Completion and tail bounds are separate properties. -/
theorem recoverRounds_invariant (M : BooleanMatrix R C) (k T : ℕ)
    (hk : 10 ≤ k) (hdegree : ∀ u, k ≤ fullDegrees M u) {out : BucketState R C}
    (hout : out ∈ ((recoverRounds (R := R) (C := C) k T).eval
      (fun q => (bilinear M q : ℝ))).support) : BucketInvariant M k out := by
  by_cases hR : Fintype.card R = 0
  · rw [recoverRounds,ite_eq_left hR,RTree.eval_pure] at hout
    have he := (PMF.mem_support_pure_iff _ _).mp hout
    simpa only [he] using BucketInvariant.initial M k
  · have hquery := rowCountProgram_honest M (univ : Finset R) (univ : Finset C)
    rw [honestRowCounts_univ] at hquery
    have heval : (rowCountProgram (univ : Finset R) (univ : Finset C)).eval
        (fun q => (bilinear M q : ℝ)) = some (fullDegrees M) := congrArg Prod.fst hquery
    rw [recoverRounds,ite_eq_right hR,RTree.eval_cast,RTree.eval_bind,
      RTree.eval_ofDeterministic,heval,PMF.pure_bind] at hout
    dsimp only at hout
    rw [ite_eq_left ⟨hk,hdegree⟩] at hout
    split at hout
    · rw [RTree.eval_weaken,RTree.eval] at hout
      obtain ⟨runout,hrun,he⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
      have h := recoverBuckets_invariant M (fullDegrees M) k T _ BucketState.initial
        (BucketInvariant.initial M k) hrun
      simpa only [he] using h
    · rw [RTree.eval_weaken] at hout
      exact (recoverRankRows_complete M k hdegree hout).1

theorem recoverRounds_true_neighbors (M : BooleanMatrix R C) (k T : ℕ)
    (hk : 10 ≤ k) (hdegree : ∀ u, k ≤ fullDegrees M u) {out : BucketState R C}
    (hout : out ∈ ((recoverRounds (R := R) (C := C) k T).eval
      (fun q => (bilinear M q : ℝ))).support) (hc : out.complete) :
    ∀ u, ∃ N, out.learned u = some N ∧ k ≤ N.card ∧ ∀ c ∈ N, M u c = true :=
  BucketInvariant.completed_true_neighbors M k out (recoverRounds_invariant M k T hk hdegree hout) hc

/-- The honest finite run retains the cost of measuring all row degrees. The
branch selector is the same public dimension comparison used by the program. -/
theorem recoverRounds_honest_run (M : BooleanMatrix R C) (k T : ℕ)
    (hR : Fintype.card R ≠ 0) (hk : 10 ≤ k)
    (hdegree : ∀ u, k ≤ fullDegrees M u) :
    RTree.run (fun q => (bilinear M q : ℝ)) (recoverRounds (R := R) (C := C) k T) =
      if Real.exp (Real.log (Fintype.card C : ℝ)/3) ≤ (Fintype.card R : ℝ) then
        (RTree.run (fun q => (bilinear M q : ℝ))
          (recoverBuckets (fullDegrees M) k T (recoveryBucketCount (Fintype.card C))
            BucketState.initial)).map (fun out => (out.1,Fintype.card R+out.2))
      else (RTree.run (fun q => (bilinear M q : ℝ))
          (recoverRankRows (fullDegrees M) k (univ : Finset R).toList BucketState.initial)).map
            (fun out => (out.1,Fintype.card R+out.2)) := by
  have hquery := rowCountProgram_honest M (univ : Finset R) (univ : Finset C)
  rw [honestRowCounts_univ] at hquery
  rw [recoverRounds,ite_eq_right hR,RTree.run_cast,RTree.run_bind,
    RTree.run_ofDeterministic,hquery,PMF.pure_bind]
  dsimp only
  rw [ite_eq_left ⟨hk,hdegree⟩]
  split <;> simp only [RTree.run_weaken,card_univ]

/-- In the bucket branch, the full measured-degree program has exactly the
fresh local bucket marginal at each row. Its measured degree table is derived
from the honest oracle only in this proof. -/
theorem recoverRounds_bucket_learned_law (M : BooleanMatrix R C) (k T : ℕ)
    (hk : 10 ≤ k) (hdegree : ∀ u, k ≤ fullDegrees M u)
    (hlarge : Real.exp (Real.log (Fintype.card C : ℝ)/3) ≤ (Fintype.card R : ℝ))
    (u : R) (i : ℕ) (hi : i < recoveryBucketCount (Fintype.card C))
    (hu : u ∈ degreeBucket (fullDegrees M) k i) :
    ((recoverRounds (R := R) (C := C) k T).eval (fun q => (bilinear M q : ℝ))).map
      (fun st => st.learned u) =
    ((learnBucketRounds (k*2^i) k T
      (BucketState.initial : BucketState (degreeBucket (fullDegrees M) k i) C)).eval
      (fun q => (bilinear (fun v : degreeBucket (fullDegrees M) k i => M v.val) q : ℝ))).map
      (fun st => st.learned ⟨u,hu⟩) := by
  have hR : Fintype.card R ≠ 0 := (Fintype.card_pos_iff.mpr ⟨u⟩).ne'
  simp only [RTree.eval,PMF.map_comp,Function.comp_def]
  change (RTree.run _ (recoverRounds (R := R) (C := C) k T)).map
    (fun out => out.1.learned u) = _
  rw [recoverRounds_honest_run M k T hR hk hdegree,ite_eq_left hlarge,PMF.map_comp]
  simpa only [RTree.eval,PMF.map_comp,Function.comp_def] using
    recoverBuckets_learned_law M (fullDegrees M) k T _ BucketState.initial
      (BucketInvariant.initial M k) u i hi hu

theorem recoverRounds_rank_learned_law (M : BooleanMatrix R C) (k T : ℕ)
    (hk : 10 ≤ k) (hdegree : ∀ u, k ≤ fullDegrees M u)
    (hsmall : ¬Real.exp (Real.log (Fintype.card C : ℝ)/3) ≤ (Fintype.card R : ℝ)) (u : R) :
    ((recoverRounds (R := R) (C := C) k T).eval (fun q => (bilinear M q : ℝ))).map
      (fun st => st.learned u) =
      (learnRanks u (fullDegrees M u) k ∅).eval (fun q => (bilinear M q : ℝ)) := by
  have hR : Fintype.card R ≠ 0 := (Fintype.card_pos_iff.mpr ⟨u⟩).ne'
  simp only [RTree.eval,PMF.map_comp,Function.comp_def]
  change (RTree.run _ (recoverRounds (R := R) (C := C) k T)).map
    (fun out => out.1.learned u) = _
  rw [recoverRounds_honest_run M k T hR hk hdegree,ite_eq_right hsmall,PMF.map_comp]
  simpa only [RTree.eval,PMF.map_comp,Function.comp_def] using
    recoverRankRows_learned_law M k (univ : Finset R).toList (Finset.nodup_toList univ)
      BucketState.initial (BucketInvariant.initial M k) (fun v _ => hdegree v) u (by simp)

/-- Full Recover's finite pre-cap one-row tail. The degree partition and tiny-row
fallback are the actual public branches, and the bound preserves all correlations
between distinct rows. -/
theorem recoverRounds_row_ratio_tail (M : BooleanMatrix R C) (k T : ℕ)
    (hk : 10 ≤ k) (hdegree : ∀ u, k ≤ fullDegrees M u) (u : R)
    (Z : Finset C) (hZ : Z ⊆ rowNeighbors (M u)) (eps : ℝ) (heps : 0 < eps) :
    mass ((recoverRounds (R := R) (C := C) k T).eval (fun q => (bilinear M q : ℝ)))
      (fun st => (st.learned u).elim False (fun S =>
        (Z.card : ℝ)/(rowNeighbors (M u)).card+eps <
          CutQueryComplexity.StarContraction2022.Probability.crossingRatio Z S)) ≤
      ENNReal.ofReal (((Z.card : ℝ)/(rowNeighbors (M u)).card)/k/eps^2) := by
  by_cases hlarge : Real.exp (Real.log (Fintype.card C : ℝ)/3) ≤ (Fintype.card R : ℝ)
  · obtain ⟨i,hi⟩ := degreeBucket_cover (fullDegrees M) k (Fintype.card C) (by omega) u
      (hdegree u) (by simpa only [fullDegrees,card_univ] using sampleCount_le_card (M u) univ)
    have hlaw := recoverRounds_bucket_learned_law M k T hk hdegree hlarge u i.val i.isLt hi
    have he := congrArg (fun μ : PMF (Option (Finset C)) => mass μ (fun o => o.elim False
      (fun S => (Z.card : ℝ)/(rowNeighbors (M u)).card+eps <
        CutQueryComplexity.StarContraction2022.Probability.crossingRatio Z S))) hlaw
    simp only [mass_map] at he
    apply he.le.trans
    have hkr : k ≤ k*2^i.val := by
      have h := Nat.one_le_pow i.val 2 (by omega)
      nlinarith
    have hd := degreeBucket_range (fullDegrees M) k i.val ⟨u,hi⟩
    exact learnBucketRounds_row_ratio_tail (fun v : degreeBucket (fullDegrees M) k i.val => M v.val)
      (k*2^i.val) k T ⟨u,hi⟩ hk hkr hd.1 hd.2 Z hZ eps heps
  · have hlaw := recoverRounds_rank_learned_law M k T hk hdegree hlarge u
    have he := congrArg (fun μ : PMF (Option (Finset C)) => mass μ (fun o => o.elim False
      (fun S => (Z.card : ℝ)/(rowNeighbors (M u)).card+eps <
        CutQueryComplexity.StarContraction2022.Probability.crossingRatio Z S))) hlaw
    simp only [mass_map] at he
    exact he.le.trans (learnRanks_row_ratio_tail M u k (by omega) (hdegree u) Z hZ eps heps)

theorem recoverRounds_row_ratio_mean (M : BooleanMatrix R C) (k T : ℕ)
    (hk : 10 ≤ k) (hdegree : ∀ u, k ≤ fullDegrees M u) (u : R)
    (Z : Finset C) (hZ : Z ⊆ rowNeighbors (M u)) :
    expect ((recoverRounds (R := R) (C := C) k T).eval (fun q => (bilinear M q : ℝ)))
      (fun st => (st.learned u).elim 0 (fun S => ENNReal.ofReal
        (CutQueryComplexity.StarContraction2022.Probability.crossingRatio Z S))) ≤
      ENNReal.ofReal ((Z.card : ℝ)/(rowNeighbors (M u)).card) := by
  by_cases hlarge : Real.exp (Real.log (Fintype.card C : ℝ)/3) ≤ (Fintype.card R : ℝ)
  · obtain ⟨i,hi⟩ := degreeBucket_cover (fullDegrees M) k (Fintype.card C) (by omega) u
      (hdegree u) (by simpa only [fullDegrees,card_univ] using sampleCount_le_card (M u) univ)
    have hlaw := recoverRounds_bucket_learned_law M k T hk hdegree hlarge u i.val i.isLt hi
    have he := congrArg (fun μ : PMF (Option (Finset C)) => expect μ (fun o => o.elim 0
      (fun S => ENNReal.ofReal (CutQueryComplexity.StarContraction2022.Probability.crossingRatio Z S)))) hlaw
    simp only [expect_map] at he
    apply he.le.trans
    have hkr : k ≤ k*2^i.val := by
      have h := Nat.one_le_pow i.val 2 (by omega)
      nlinarith
    have hd := degreeBucket_range (fullDegrees M) k i.val ⟨u,hi⟩
    exact learnBucketRounds_row_ratio_mean (fun v : degreeBucket (fullDegrees M) k i.val => M v.val)
      (k*2^i.val) k T ⟨u,hi⟩ hk hkr hd.1 hd.2 Z hZ
  · have hlaw := recoverRounds_rank_learned_law M k T hk hdegree hlarge u
    have he := congrArg (fun μ : PMF (Option (Finset C)) => expect μ (fun o => o.elim 0
      (fun S => ENNReal.ofReal (CutQueryComplexity.StarContraction2022.Probability.crossingRatio Z S)))) hlaw
    simp only [expect_map] at he
    exact he.le.trans (learnRanks_row_ratio_mean M u k (by omega) (hdegree u) Z hZ).le

/-- A finite unfinished execution has paid for every one of its T attempts in
some degree bucket. The rank branch finishes outright on honest input. -/
theorem recoverRounds_unfinished_cost (M : BooleanMatrix R C) (k T : ℕ)
    (hk : 10 ≤ k) (hdegree : ∀ u, k ≤ fullDegrees M u)
    {out : BucketState R C × ℕ}
    (hout : out ∈ (RTree.run (fun q => (bilinear M q : ℝ))
      (recoverRounds (R := R) (C := C) k T)).support)
    (hunfinished : ¬out.1.complete) : T ≤ out.2 := by
  by_cases hR : Fintype.card R = 0
  · haveI : IsEmpty R := Fintype.card_eq_zero_iff.mp hR
    rw [recoverRounds,ite_eq_left hR,RTree.run_pure,PMF.pure_map] at hout
    have he : out = (BucketState.initial,0) := (PMF.mem_support_pure_iff _ _).mp hout
    subst out
    apply False.elim
    apply hunfinished
    refine ⟨rfl,eq_empty_iff_forall_notMem.mpr ?_⟩
    intro u
    exact isEmptyElim u
  · rw [recoverRounds_honest_run M k T hR hk hdegree] at hout
    split at hout
    · obtain ⟨next,hnext,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
      have hinv := recoverBuckets_invariant M (fullDegrees M) k T _ BucketState.initial
        (BucketInvariant.initial M k) hnext
      have hpend : next.1.pending.Nonempty := by
        apply nonempty_iff_ne_empty.mpr
        intro he
        exact hunfinished ⟨hinv.1,he⟩
      have hc := recoverBuckets_unfinished_cost M (fullDegrees M) k T (by omega)
        (fun u => ⟨hdegree u,by
          simpa only [fullDegrees,card_univ] using sampleCount_le_card (M u) univ⟩)
        hnext hpend
      dsimp only
      omega
    · obtain ⟨next,hnext,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
      have heval : next.1 ∈ ((recoverRankRows (fullDegrees M) k (univ : Finset R).toList
          BucketState.initial).eval (fun q => (bilinear M q : ℝ))).support :=
        (PMF.mem_support_map_iff _ _ _).mpr ⟨next,hnext,rfl⟩
      exact (hunfinished (recoverRankRows_complete M k hdegree heval).2).elim

/-- Exact honest branch cost after the measured degree table is validated.
This equality accounts for the initial degree queries explicitly. -/
theorem recoverRounds_expected_branch (M : BooleanMatrix R C) (k T : ℕ)
    (hR : Fintype.card R ≠ 0) (hk : 10 ≤ k)
    (hdegree : ∀ u, k ≤ fullDegrees M u) :
    (recoverRounds (R := R) (C := C) k T).expectedQueries (fun q => (bilinear M q : ℝ)) =
      (Fintype.card R : ℝ≥0∞)+
        if Real.exp (Real.log (Fintype.card C : ℝ)/3) ≤ (Fintype.card R : ℝ) then
          (recoverBuckets (fullDegrees M) k T (recoveryBucketCount (Fintype.card C))
            BucketState.initial).expectedQueries (fun q => (bilinear M q : ℝ))
        else (recoverRankRows (fullDegrees M) k (univ : Finset R).toList BucketState.initial).expectedQueries
          (fun q => (bilinear M q : ℝ)) := by
  have hquery := rowCountProgram_honest M (univ : Finset R) (univ : Finset C)
  rw [honestRowCounts_univ] at hquery
  have heval : (rowCountProgram (univ : Finset R) (univ : Finset C)).eval
      (fun q => (bilinear M q : ℝ)) = some (fullDegrees M) := congrArg Prod.fst hquery
  have hexp : (RTree.ofDeterministic (rowCountProgram (univ : Finset R) (univ : Finset C))).expectedQueries
      (fun q => (bilinear M q : ℝ)) = Fintype.card R := by
    change expect (RTree.run _ _) (fun out => (out.2 : ℝ≥0∞)) = _
    simp only [RTree.run_ofDeterministic,hquery,expect_pure,card_univ]
  rw [recoverRounds,ite_eq_right hR,expected_cast,recovery_expected_bind,
    RTree.eval_ofDeterministic,heval,expect_pure,hexp]
  dsimp only
  rw [ite_eq_left ⟨hk,hdegree⟩]
  split <;> rw [expected_weaken]

/-- Uniform finite expected budget for the operational Recover program in
bilinear-query units. The tiny-row branch pays for actual logarithmic rank
queries; its column term is retained. -/
theorem recoverRounds_expected_bound (M : BooleanMatrix R C) (k T : ℕ)
    (hk : 10 ≤ k) (hdegree : ∀ u, k ≤ fullDegrees M u) :
    (recoverRounds (R := R) (C := C) k T).expectedQueries (fun q => (bilinear M q : ℝ)) ≤
      ENNReal.ofReal ((1+400*(bucketConstant : ℝ))*k*(Fintype.card R+Fintype.card C)) := by
  by_cases hR : Fintype.card R = 0
  · rw [recoverRounds,ite_eq_left hR,expected_pure]
    exact bot_le
  · have hRpos : 0 < Fintype.card R := by omega
    let u := (Fintype.card_pos_iff.mp hRpos).some
    have ht : 1 ≤ Fintype.card C := by
      have h := (hdegree u).trans (sampleCount_le_card (M u) univ)
      rw [card_univ] at h
      omega
    rw [recoverRounds_expected_branch M k T hR hk hdegree]
    by_cases hm : Real.exp (Real.log (Fintype.card C : ℝ)/3) ≤ (Fintype.card R : ℝ)
    · rw [ite_eq_left hm]
      have hb := recoverBuckets_expected_linear M (fullDegrees M) k T BucketState.initial hk ht
        (fun _ => rfl) hdegree hm
      calc
        _ ≤ (Fintype.card R : ℝ≥0∞)+ENNReal.ofReal (361*(bucketConstant : ℝ)*k*Fintype.card R) :=
          add_le_add (le_refl _) hb
        _ = ENNReal.ofReal ((Fintype.card R : ℝ)+361*(bucketConstant : ℝ)*k*Fintype.card R) := by
          rw [ENNReal.ofReal_add (Nat.cast_nonneg _) (by positivity),ENNReal.ofReal_natCast]
        _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
          have hc : 0 ≤ (bucketConstant : ℝ) := Nat.cast_nonneg _
          have hmR : 0 ≤ (Fintype.card R : ℝ) := Nat.cast_nonneg _
          have htR : 0 ≤ (Fintype.card C : ℝ) := Nat.cast_nonneg _
          calc
            _ ≤ (k : ℝ)*Fintype.card R+400*(bucketConstant : ℝ)*k*Fintype.card R := by
              apply add_le_add
              · simpa only [one_mul] using mul_le_mul_of_nonneg_right hkR hmR
              · have hcoeff : 361*(bucketConstant : ℝ) ≤ 400*bucketConstant := by nlinarith
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg k)) hmR
            _ = (1+400*(bucketConstant : ℝ))*k*Fintype.card R := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right htR) (by positivity)
    · rw [ite_eq_right hm]
      have hb := RTree.expectedQueries_le_budget
        (recoverRankRows (fullDegrees M) k (univ : Finset R).toList BucketState.initial)
        (fun q => (bilinear M q : ℝ))
      have hsmall := tinyRows_original_budget (Fintype.card R) (Fintype.card C) k ht (by omega)
        (le_of_not_ge hm)
      have hsmallR : (Fintype.card R : ℝ)+Fintype.card R*(k*searchDepth C) ≤
          4*(k : ℝ)*(Fintype.card R+Fintype.card C) := by
        have hh : (3 : ℝ)*Fintype.card R+3*k*Fintype.card R*Nat.clog 2 (Fintype.card C) ≤
            12*k*(Fintype.card R+Fintype.card C) := by exact_mod_cast hsmall
        unfold searchDepth
        nlinarith
      calc
        _ ≤ (Fintype.card R : ℝ≥0∞)+Fintype.card R*(k*searchDepth C) := by
          simpa only [length_toList,card_univ,Nat.cast_mul] using add_le_add (le_refl (Fintype.card R : ℝ≥0∞)) hb
        _ = ENNReal.ofReal ((Fintype.card R : ℝ)+Fintype.card R*(k*searchDepth C)) := by
          simpa only [Nat.cast_add,Nat.cast_mul] using
            (ENNReal.ofReal_natCast (Fintype.card R+Fintype.card R*(k*searchDepth C))).symm
        _ ≤ ENNReal.ofReal (4*(k : ℝ)*(Fintype.card R+Fintype.card C)) :=
          ENNReal.ofReal_le_ofReal hsmallR
        _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          have hconstant : (4 : ℝ) ≤ 1+400*bucketConstant := by norm_num [bucketConstant]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hconstant (Nat.cast_nonneg _))
            (by positivity)

end RecoveryProgram

section OriginalRecovery

variable {V R C : Type} [Fintype V] [DecidableEq V]
  [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C]

/-- Every bilinear count is implemented by exactly three original cut queries.
The explicit constant pays for this substitution and the initial degree table. -/
theorem recoverRounds_original_expected_bound (row : R ↪ V) (col : C ↪ V)
    (hdisjoint : ∀ u v, row u ≠ col v) (G : SimpleInput V) (k T : ℕ)
    (hk : 10 ≤ k) (hdegree : ∀ u, k ≤ fullDegrees (graphMatrix row col G) u) :
    (simulateOriginal row col (recoverRounds (R := R) (C := C) k T)).expectedQueries G.toWeighted.cut ≤
      ENNReal.ofReal ((recoveryCoefficient : ℝ)*k*(Fintype.card R+Fintype.card C)) := by
  rw [simulateOriginal_expected]
  have hread : originalBilinearRead row col G.toWeighted.cut =
      fun q => (bilinear (graphMatrix row col G) q : ℝ) := by
    funext q
    exact originalBilinearRead_honest row col hdisjoint G q
  rw [hread]
  have h := mul_le_mul_right (recoverRounds_expected_bound (graphMatrix row col G) k T hk hdegree)
    (3 : ℝ≥0∞)
  apply h.trans_eq
  rw [← ENNReal.ofReal_ofNat 3,← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  simp only [recoveryCoefficient,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one]
  ring

end OriginalRecovery

end
end CutQueryComplexity.StarContraction2022.Recovery

#print axioms CutQueryComplexity.StarContraction2022.Recovery.graphMatrix_bilinear
#print axioms CutQueryComplexity.StarContraction2022.Recovery.validatedOriginalBilinearCall_honest
#print axioms CutQueryComplexity.StarContraction2022.Recovery.validatedOriginalBilinearCall_reject
#print axioms CutQueryComplexity.StarContraction2022.Recovery.simulateOriginal_run
#print axioms CutQueryComplexity.StarContraction2022.Recovery.simulateOriginal_expected
#print axioms CutQueryComplexity.StarContraction2022.Recovery.simulateOriginal_every_oracle
#print axioms CutQueryComplexity.StarContraction2022.Recovery.rankSearch_correct
#print axioms CutQueryComplexity.StarContraction2022.Recovery.rankSearch_every_oracle

#print axioms CutQueryComplexity.StarContraction2022.Recovery.sum_bucketNumeric_le
#print axioms CutQueryComplexity.StarContraction2022.Recovery.recoveryBucketCount_bound
#print axioms CutQueryComplexity.StarContraction2022.Recovery.tinyRows_original_budget

#print axioms CutQueryComplexity.StarContraction2022.Recovery.semanticRank_injective
#print axioms CutQueryComplexity.StarContraction2022.Recovery.rankVertex_bijective
#print axioms CutQueryComplexity.StarContraction2022.Recovery.drawRemaining_uniform
#print axioms CutQueryComplexity.StarContraction2022.Recovery.learnRanks_every_oracle

#print axioms CutQueryComplexity.StarContraction2022.Recovery.liftRows_run
#print axioms CutQueryComplexity.StarContraction2022.Recovery.recoverRounds_every_oracle

#print axioms CutQueryComplexity.StarContraction2022.Recovery.simulateOriginal_eval
#print axioms CutQueryComplexity.StarContraction2022.Recovery.uniformSubset_step
#print axioms CutQueryComplexity.StarContraction2022.Recovery.learnRanks_uniform
#print axioms CutQueryComplexity.StarContraction2022.Recovery.columnProposal_restriction
#print axioms CutQueryComplexity.StarContraction2022.Recovery.firstSuccess_conditioned_real
#print axioms CutQueryComplexity.StarContraction2022.Recovery.firstSuccess_conditioned_bad_le
#print axioms CutQueryComplexity.StarContraction2022.Recovery.firstSuccess_conditioned_expect_le
#print axioms CutQueryComplexity.StarContraction2022.Recovery.learnBucketRounds_learned_law
#print axioms CutQueryComplexity.StarContraction2022.Recovery.bucketRow_window_supported
#print axioms CutQueryComplexity.StarContraction2022.Recovery.learnBucketRounds_row_ratio_tail
#print axioms CutQueryComplexity.StarContraction2022.Recovery.learnBucketRounds_row_ratio_mean
#print axioms CutQueryComplexity.StarContraction2022.Recovery.learnRanks_row_ratio_tail
#print axioms CutQueryComplexity.StarContraction2022.Recovery.learnRanks_row_ratio_mean
#print axioms CutQueryComplexity.StarContraction2022.Recovery.degreeBucket_cover
#print axioms CutQueryComplexity.StarContraction2022.Recovery.degreeBucket_card_sum
#print axioms CutQueryComplexity.StarContraction2022.Recovery.degreeBucket_numeric_sum
#print axioms CutQueryComplexity.StarContraction2022.Recovery.recoverBuckets_learned_law
#print axioms CutQueryComplexity.StarContraction2022.Recovery.recoverRankRows_learned_law
#print axioms CutQueryComplexity.StarContraction2022.Recovery.recoverRounds_invariant
#print axioms CutQueryComplexity.StarContraction2022.Recovery.recoverRounds_true_neighbors
#print axioms CutQueryComplexity.StarContraction2022.Recovery.recoverRounds_bucket_learned_law
#print axioms CutQueryComplexity.StarContraction2022.Recovery.recoverRounds_rank_learned_law
#print axioms CutQueryComplexity.StarContraction2022.Recovery.recoverRounds_row_ratio_tail
#print axioms CutQueryComplexity.StarContraction2022.Recovery.recoverRounds_row_ratio_mean
#print axioms CutQueryComplexity.StarContraction2022.Recovery.recoverRounds_unfinished_cost
#print axioms CutQueryComplexity.StarContraction2022.Recovery.recoverRounds_expected_bound
#print axioms CutQueryComplexity.StarContraction2022.Recovery.recoverRounds_original_expected_bound
