import CutQueryComplexity.AllPairsAudit.CutAlgebra
import CutQueryComplexity.Primitive.CrossSearch
import CutQueryComplexity.Primitive.Residual

/-!
# Capped recovery of original interblock edges

The program takes only a public block map and a public integer edge cap.
It first measures all block cuts. It aborts before enumeration if their sum
exceeds twice the cap. Otherwise, a single global fuel bound pays for all
row searches: each successful search removes one positive ordered pair,
and each unsuccessful search removes one row.

The correctness proof uses unit input weights, but neither a friendly-cut
partition nor any all-pairs minimum-cut preservation assumption. The budget
holds for every answer sequence, including failed sparsifier executions.
-/

set_option autoImplicit false

namespace CutQueryComplexity.AllPairs

open Finset WeightedGraph
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

def rowSupport (G : WeightedGraph V) (u : V) (T : Finset V) : Finset V :=
  T.filter fun v => 0 < G.w u v

def rowTargets (G : WeightedGraph V) : List (V × Finset V) → Finset (V × V)
  | [] => ∅
  | (u, T) :: xs => (rowSupport G u T).image (Prod.mk u) ∪ rowTargets G xs

/-- Proof-only progress measure; the executable program never reads it. -/
def rowWork (G : WeightedGraph V) : List (V × Finset V) → ℕ
  | [] => 0
  | (u, T) :: xs => (rowSupport G u T).card + 1 + rowWork G xs

omit [Fintype V] in
theorem rowSupport_erase (G : WeightedGraph V) (u v : V) (T : Finset V) :
    rowSupport G u (T.erase v) = (rowSupport G u T).erase v := by
  ext x
  simp [rowSupport, and_assoc]

omit [Fintype V] in
theorem rowTargets_erase (G : WeightedGraph V) (u v : V) (T : Finset V)
    (xs : List (V × Finset V)) (hv : v ∈ rowSupport G u T) :
    rowTargets G ((u, T) :: xs) =
      insert (u, v) (rowTargets G ((u, T.erase v) :: xs)) := by
  have hs : rowSupport G u T = insert v (rowSupport G u (T.erase v)) := by
    rw [rowSupport_erase, insert_erase hv]
  change (rowSupport G u T).image (Prod.mk u) ∪ rowTargets G xs =
    insert (u, v) ((rowSupport G u (T.erase v)).image (Prod.mk u) ∪ rowTargets G xs)
  rw [hs, image_insert, insert_union]

omit [Fintype V] in
theorem rowWork_erase (G : WeightedGraph V) (u v : V) (T : Finset V)
    (xs : List (V × Finset V)) (hv : v ∈ rowSupport G u T) :
    rowWork G ((u, T) :: xs) = rowWork G ((u, T.erase v) :: xs) + 1 := by
  have hp : 0 < (rowSupport G u T).card := card_pos.mpr ⟨v, hv⟩
  simp only [rowWork, rowSupport_erase, card_erase_of_mem hv]
  omega

/-- One global fuel counter, shared by all vertex rows. -/
def recoverRows (k : ℕ) : (fuel : ℕ) → List (V × Finset V) →
    DTree (Finset V) ℝ (Finset (V × V)) (fuel * ((k + 1) * 3))
  | 0, _ => DTree.pure ∅
  | _ + 1, [] => DTree.pure ∅
  | fuel + 1, (u, T) :: xs =>
      ((findNeighbor k u T).bind fun answer => match answer with
        | none => recoverRows k fuel xs
        | some v => (recoverRows k fuel ((u, T.erase v) :: xs)).map (insert (u, v))).cast
        (by ring)

/-- A successful discovery spends one unit of positive support; an empty row
spends its row marker. No per-row worst-case edge bound is assumed. -/
theorem recoverRows_correct (G : WeightedGraph V) (k : ℕ)
    (hn : Fintype.card V ≤ 2 ^ k) (fuel : ℕ) (xs : List (V × Finset V))
    (hfuel : rowWork G xs ≤ fuel) :
    (recoverRows k fuel xs).eval G.cut = rowTargets G xs := by
  induction fuel generalizing xs with
  | zero =>
      cases xs with
      | nil => simp [recoverRows, rowTargets]
      | cons a xs =>
          rcases a with ⟨u, T⟩
          simp only [rowWork] at hfuel
          omega
  | succ fuel ih =>
      cases xs with
      | nil => simp [recoverRows, rowTargets]
      | cons a xs =>
          rcases a with ⟨u, T⟩
          have hsearch := findNeighbor_correct G k u T hn
          simp only [recoverRows, DTree.eval_cast, DTree.eval_bind]
          cases hanswer : (findNeighbor k u T).eval G.cut with
          | none =>
              simp only [hanswer, PositiveResult] at hsearch
              have hz : rowSupport G u T = ∅ := by
                apply Finset.eq_empty_iff_forall_notMem.mpr
                intro v hv
                obtain ⟨hvT, hpos⟩ := mem_filter.mp hv
                have hzero := hsearch v (mem_univ v)
                simp only [restrictWeight, hvT, ↓reduceIte] at hzero
                linarith
              have hsmall : rowWork G xs ≤ fuel := by
                simp only [rowWork, hz, card_empty] at hfuel
                omega
              simpa [rowTargets, hz] using ih xs hsmall
          | some v =>
              simp only [hanswer, PositiveResult] at hsearch
              have hv := (restrictWeight_pos (G.w u) T v).mp hsearch.2
              have hs : v ∈ rowSupport G u T := mem_filter.mpr hv
              have hsmall : rowWork G ((u, T.erase v) :: xs) ≤ fuel := by
                have hw := rowWork_erase G u v T xs hs
                omega
              rw [DTree.eval_map, ih _ hsmall]
              exact (rowTargets_erase G u v T xs hs).symm

omit [Fintype V] in
theorem mem_rowTargets (G : WeightedGraph V) (xs : List (V × Finset V)) (u v : V) :
    (u, v) ∈ rowTargets G xs ↔ ∃ T, (u, T) ∈ xs ∧ v ∈ rowSupport G u T := by
  induction xs with
  | nil => simp [rowTargets]
  | cons a xs ih =>
      rcases a with ⟨a, A⟩
      rw [rowTargets, mem_union, ih]
      constructor
      · rintro (h | ⟨T, hT, hv⟩)
        · obtain ⟨b, hb, he⟩ := mem_image.mp h
          have ha : a = u := congrArg Prod.fst he
          have hv : b = v := congrArg Prod.snd he
          subst a b
          exact ⟨A, by simp, hb⟩
        · exact ⟨T, List.mem_cons_of_mem _ hT, hv⟩
      · rintro ⟨T, hT, hv⟩
        rcases List.mem_cons.mp hT with he | he
        · have ha : u = a := congrArg Prod.fst he
          have hA : T = A := congrArg Prod.snd he
          subst u T
          exact Or.inl (mem_image.mpr ⟨v, hv, rfl⟩)
        · exact Or.inr ⟨T, he, hv⟩

def outsideBlock (p : V → V) (u : V) : Finset V :=
  univ.filter fun v => p u ≠ p v

def recoveryRows (p : V → V) : List (V × Finset V) :=
  univ.toList.map fun u => (u, outsideBlock p u)

theorem mem_recoveryTargets (G : WeightedGraph V) (p : V → V) (u v : V) :
    (u, v) ∈ rowTargets G (recoveryRows p) ↔ p u ≠ p v ∧ 0 < G.w u v := by
  rw [mem_rowTargets]
  constructor
  · rintro ⟨T, hT, hv⟩
    obtain ⟨a, _, he⟩ := List.mem_map.mp hT
    have ha : a = u := congrArg Prod.fst he
    subst a
    have hT : outsideBlock p u = T := congrArg Prod.snd he
    subst T
    simpa [rowSupport, outsideBlock] using hv
  · intro h
    refine ⟨outsideBlock p u, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨u, by simp, rfl⟩
    · simpa [rowSupport, outsideBlock] using h

theorem rowWork_map (G : WeightedGraph V) (p : V → V) (xs : List V) :
    rowWork G (xs.map fun u => (u, outsideBlock p u)) =
      xs.length + (xs.map fun u => (rowSupport G u (outsideBlock p u)).card).sum := by
  induction xs with
  | nil => simp [rowWork]
  | cons u xs ih => simp only [List.map_cons, rowWork, ih, List.length_cons, List.sum_cons]; omega

theorem recovery_work (G : WeightedGraph V) (p : V → V) :
    rowWork G (recoveryRows p) =
      Fintype.card V + ∑ u, (rowSupport G u (outsideBlock p u)).card := by
  simp [recoveryRows, rowWork_map]

theorem rowSupport_card (G : WeightedGraph V) (hG : AllPairsAudit.Unweighted G)
    (p : V → V) (u : V) :
    ((rowSupport G u (outsideBlock p u)).card : ℝ) =
      ∑ v, (G.residual p).w u v := by
  rw [card_eq_sum_ones, Nat.cast_sum]
  simp only [Nat.cast_one]
  rw [rowSupport, sum_filter, outsideBlock, sum_filter]
  apply sum_congr rfl
  intro v hv
  rcases hG u v with hz | ho
  · simp [WeightedGraph.residual, hz]
  · by_cases he : p u = p v <;> simp [WeightedGraph.residual, ho, he]

/-- All cached block cuts count precisely the positive ordered interblock
pairs. This is the observed quantity used to justify the global fuel. -/
theorem recovery_work_cast (G : WeightedGraph V) (hG : AllPairsAudit.Unweighted G)
    (p : V → V) :
    (rowWork G (recoveryRows p) : ℝ) =
      Fintype.card V + ∑ b, G.cut (WeightedGraph.fiber p b) := by
  have hm := G.residual_internalMass p (univ : Finset V)
  have hf := G.residual_mass_formula p (univ : Finset V)
  have hp : WeightedGraph.pull p (univ : Finset V) = univ := by ext; simp [WeightedGraph.pull]
  rw [hp] at hm hf
  rw [G.cut_univ, sub_zero] at hf
  have hsum : (∑ u, ∑ v, (G.residual p).w u v) = ∑ b, G.cut (WeightedGraph.fiber p b) := by
    rw [← hm] at hf
    change (∑ u, ∑ v, (G.residual p).w u v) / 2 = _ at hf
    linarith
  rw [recovery_work, Nat.cast_add, Nat.cast_sum]
  simp_rw [rowSupport_card G hG]
  rw [hsum]

/-- A total explicit graph decoder, including transcripts from arbitrary
oracles. On a promised run it is exactly the interblock residual graph. -/
def decodeRecovered (E : Finset (V × V)) : WeightedGraph V where
  w u v := if u = v then 0 else if (u, v) ∈ E ∨ (v, u) ∈ E then 1 else 0
  symm u v := by
    by_cases h : u = v
    · subst v; rfl
    · simp [h, Ne.symm h, or_comm]
  nonneg u v := by split <;> (try split) <;> norm_num
  diag u := by simp

theorem decodeRecovered_correct (G : WeightedGraph V) (hG : AllPairsAudit.Unweighted G)
    (p : V → V) :
    decodeRecovered (rowTargets G (recoveryRows p)) = G.residual p := by
  ext u v
  change (if u = v then 0 else
    if (u, v) ∈ rowTargets G (recoveryRows p) ∨ (v, u) ∈ rowTargets G (recoveryRows p)
    then 1 else 0) = _
  by_cases huv : u = v
  · subst v
    simp [WeightedGraph.residual]
  · simp only [huv, ↓reduceIte, mem_recoveryTargets]
    rw [G.symm v u]
    by_cases hp : p u = p v
    · simp [WeightedGraph.residual, hp]
    · rcases hG u v with hz | ho
      · simp [WeightedGraph.residual, hp, Ne.symm hp, hz]
      · simp [WeightedGraph.residual, hp, Ne.symm hp, ho]

abbrev recoveryBudget (V : Type) [Fintype V] (M : ℕ) : ℕ :=
  Fintype.card V + (Fintype.card V + 2 * M) * ((searchDepth V + 1) * 3)

/-- Query the surviving-edge count and abort before expensive enumeration
when it is too large. The type supplies a cap on every execution. -/
def recoverCapped (p : V → V) (M : ℕ) :
    DTree (Finset V) ℝ (Option (WeightedGraph V)) (recoveryBudget V M) :=
  (cacheBlockCuts p).bind fun cache =>
    if (∑ b, cache b) ≤ 2 * (M : ℝ) then
      (recoverRows (searchDepth V) (Fintype.card V + 2 * M) (recoveryRows p)).map
        (fun E => some (decodeRecovered E))
    else DTree.pure none

theorem recoverCapped_cost (p : V → V) (M : ℕ) (oracle : Finset V → ℝ) :
    (recoverCapped p M).cost oracle ≤ recoveryBudget V M := DTree.cost_le _ _

/-- Exact recovery whenever the measured cap holds. The promise is discharged
later by the partition/shaving edge bound; it is never assumed by the program. -/
theorem recoverCapped_correct (G : WeightedGraph V) (hG : AllPairsAudit.Unweighted G)
    (p : V → V) (M : ℕ)
    (hM : (∑ b, G.cut (WeightedGraph.fiber p b)) ≤ 2 * (M : ℝ)) :
    (recoverCapped p M).eval G.cut = some (G.residual p) := by
  have hcache : (cacheBlockCuts p).eval G.cut = fun b => G.cut (WeightedGraph.fiber p b) := by
    rw [DTree.eval, cacheBlockCuts_run]
  have hwork : rowWork G (recoveryRows p) ≤ Fintype.card V + 2 * M := by
    have hr : (rowWork G (recoveryRows p) : ℝ) ≤ (Fintype.card V + 2 * M : ℕ) := by
      rw [recovery_work_cast G hG]
      push_cast
      linarith
    exact_mod_cast hr
  simp only [recoverCapped, DTree.eval_bind, hcache, hM, ↓reduceIte, DTree.eval_map]
  rw [recoverRows_correct G (searchDepth V) (Nat.le_pow_clog (by norm_num) _) _ _ hwork,
    decodeRecovered_correct G hG]

/-- The abort branch itself is determined only by already measured cuts. -/
theorem recoverCapped_abort (G : WeightedGraph V) (p : V → V) (M : ℕ)
    (hM : 2 * (M : ℝ) < ∑ b, G.cut (WeightedGraph.fiber p b)) :
    (recoverCapped p M).eval G.cut = none := by
  have hcache : (cacheBlockCuts p).eval G.cut = fun b => G.cut (WeightedGraph.fiber p b) := by
    rw [DTree.eval, cacheBlockCuts_run]
  simp [recoverCapped, hcache, not_le.mpr hM]

end
end CutQueryComplexity.AllPairs

#print axioms CutQueryComplexity.AllPairs.recoverCapped_correct
#print axioms CutQueryComplexity.AllPairs.recoverCapped_cost
