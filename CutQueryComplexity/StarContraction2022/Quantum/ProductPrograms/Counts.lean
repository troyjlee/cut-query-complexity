import CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Actual scalar queries, original-value verification, and public deletions

A product vector is a finite public answer. Summing and clipping it gives a
total scalar decoder; on honest input clipping is inactive and the scalar is
the original cut value. Learned-edge subtraction is likewise public and total.
The hidden residual graph occurs only in the semantic theorems, never in a
query-tree constructor or its cost index.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms

noncomputable section
open scoped Classical

variable {n q : ℕ}

/-- Malformed vectors still produce a legal finite scalar answer. -/
def cutLetterOfProduct (y : ProductAnswer n 1) : CutAnswer n 1 :=
  ⟨min (∑ v, (y v).val) (n * n), by
    simpa only [Nat.one_mul] using
      Nat.lt_succ_of_le (Nat.min_le_right (∑ v, (y v).val) (n * n))⟩

theorem cutLetterOfProduct_le (y : ProductAnswer n 1) :
    (cutLetterOfProduct y : ℕ) ≤ n * n := Nat.min_le_right _ _

/-- This is one original cut, not one query per recovered coordinate. -/
@[simp] theorem cutLetterOfProduct_honest (G : CapacityGraph (Fin n) 1)
    (S : Finset (Fin n)) : cutLetterOfProduct (productRead G S) = capacityRead G S := by
  apply Fin.ext
  change min (∑ v, (productRead G S v).val) (n * n) = G.cut S
  rw [productRead_sum]
  exact min_eq_left (by simpa only [Fintype.card_fin, Nat.one_mul] using G.cut_le S)

theorem cutLetterOfProduct_read (G : CapacityGraph (Fin n) 1) :
    cutLetterOfProduct ∘ productRead G = capacityRead G := by
  funext S
  exact cutLetterOfProduct_honest G S

def productScalarRead (read : Finset (Fin n) → ProductAnswer n 1) :
    Finset (Fin n) → ℝ := fun S => decodeCutAnswer (cutLetterOfProduct (read S))

theorem productScalarRead_honest (G : CapacityGraph (Fin n) 1) :
    productScalarRead (productRead G) = G.toWeighted.cut := by
  funext S
  simp only [productScalarRead, cutLetterOfProduct_honest, decode_capacityRead]

/-- Encode an actual real-answer cut tree, then simulate each scalar query by
one product query. The source tree is supplied before every hidden graph. -/
def cutTreeToProduct (T : OptionalCutTree n q) : ProductTree n (Candidate n) q :=
  mapAnswers cutLetterOfProduct (finiteCutTree 1 T)

theorem cutTreeToProduct_run (T : OptionalCutTree n q)
    (read : Finset (Fin n) → ProductAnswer n 1) :
    RTree.run read (cutTreeToProduct T) =
      (RTree.run (productScalarRead read) T).map
        (fun p => (encodeOptionalCutResult 1 p.1, p.2)) := by
  rw [cutTreeToProduct, run_mapAnswers, finiteCutTree_run]
  rfl

theorem cutTreeToProduct_count_law (T : OptionalCutTree n q)
    (read : Finset (Fin n) → ProductAnswer n 1) :
    (RTree.run read (cutTreeToProduct T)).map Prod.snd =
      (RTree.run (productScalarRead read) T).map Prod.snd := by
  rw [cutTreeToProduct_run, PMF.map_comp]
  rfl

theorem cutTreeToProduct_run_honest (T : OptionalCutTree n q)
    (G : CapacityGraph (Fin n) 1) :
    RTree.run (productRead G) (cutTreeToProduct T) =
      (RTree.run G.toWeighted.cut T).map
        (fun p => (encodeOptionalCutResult 1 p.1, p.2)) := by
  rw [cutTreeToProduct_run, productScalarRead_honest]

/-- Finite validation is lossless for a source that always reports exact cuts. -/
theorem cutTreeToProduct_decoded_run (T : OptionalCutTree n q)
    (G : CapacityGraph (Fin n) 1) (h : CutTreeSound T G.toWeighted) :
    (RTree.run (productRead G) (cutTreeToProduct T)).map
      (fun p => (decodeFiniteCutResult p.1, p.2)) = RTree.run G.toWeighted.cut T := by
  rw [cutTreeToProduct, run_mapAnswers, cutLetterOfProduct_read]
  exact finiteCutTree_decoded_run T G h

theorem cutTreeToProduct_successProb (T : OptionalCutTree n q)
    (G : CapacityGraph (Fin n) 1) (h : CutTreeSound T G.toWeighted)
    (Good : Option (CutResult (Fin n)) → Prop) :
    (cutTreeToProduct T).successProb (productRead G)
      (fun e => Good (decodeFiniteCutResult e)) = T.successProb G.toWeighted.cut Good := by
  have he := congrArg
    (fun p : PMF (Option (CutResult (Fin n)) × ℕ) =>
      (p.toOuterMeasure {out | Good out.1}).toReal)
    (cutTreeToProduct_decoded_run T G h)
  rw [PMF.toOuterMeasure_map_apply] at he
  exact he

theorem cutTreeToProduct_sound (T : OptionalCutTree n q)
    (G : CapacityGraph (Fin n) 1) (h : CutTreeSound T G.toWeighted) :
    ProductTreeSound (cutTreeToProduct T) G := by
  intro out hout
  cases out with
  | none => trivial
  | some e =>
      unfold RTree.eval at hout
      rw [cutTreeToProduct_run_honest, PMF.map_comp] at hout
      obtain ⟨⟨o, c⟩, hoc, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
      change encodeOptionalCutResult 1 o = some e at he
      cases o with
      | none => simp [encodeOptionalCutResult_none] at he
      | some r =>
          have hs := h r c hoc
          have he' : encodeCutResult 1 r = some e := by
            simpa only [encodeOptionalCutResult_some] using he
          obtain ⟨hshore, hvalue⟩ := encodeCutResult_spec he'
          change ProperShore e.1 ∧ decodeCutAnswer e.2 = G.toWeighted.cut e.1
          rw [hshore, hvalue]
          exact hs

theorem cutTreeToProduct_cost (T : OptionalCutTree n q)
    (read : Finset (Fin n) → ProductAnswer n 1) {out : Candidate n × ℕ}
    (h : out ∈ (RTree.run read (cutTreeToProduct T)).support) : out.2 ≤ q :=
  RTree.cost_le _ read h

/-- Check the shore publicly and execute exactly one product query if proper. -/
def verifyCandidate (S : Finset (Fin n)) : ProductTree n (Candidate n) 1 :=
  if ProperShore S then
    RTree.query S fun y => RTree.pure (q := 0) (PMF.pure (some (S, cutLetterOfProduct y)))
  else RTree.pure (PMF.pure none)

theorem verifyCandidate_run (S : Finset (Fin n))
    (read : Finset (Fin n) → ProductAnswer n 1) :
    RTree.run read (verifyCandidate S) =
      if ProperShore S then PMF.pure (some (S, cutLetterOfProduct (read S)), 1)
      else PMF.pure (none, 0) := by
  by_cases h : ProperShore S <;> simp [verifyCandidate, h, PMF.pure_map]

theorem verifyCandidate_eval (S : Finset (Fin n))
    (read : Finset (Fin n) → ProductAnswer n 1) :
    (verifyCandidate S).eval read =
      PMF.pure (if ProperShore S then some (S, cutLetterOfProduct (read S)) else none) := by
  by_cases h : ProperShore S <;> simp [verifyCandidate, h]

theorem verifyCandidate_eval_honest (S : Finset (Fin n))
    (G : CapacityGraph (Fin n) 1) :
    (verifyCandidate S).eval (productRead G) =
      PMF.pure (if ProperShore S then some (S, capacityRead G S) else none) := by
  rw [verifyCandidate_eval, cutLetterOfProduct_honest]

theorem verifyCandidate_sound (S : Finset (Fin n)) (G : CapacityGraph (Fin n) 1) :
    ProductTreeSound (verifyCandidate S) G := by
  intro out hout
  rw [verifyCandidate_eval_honest] at hout
  have he := (PMF.mem_support_pure_iff _ _).mp hout
  subst out
  split_ifs with hS
  · change ProperShore S ∧ decodeCutAnswer (capacityRead G S) = G.toWeighted.cut S
    exact ⟨hS, decode_capacityRead G S⟩
  · trivial

theorem verifyCandidate_cost (S : Finset (Fin n))
    (read : Finset (Fin n) → ProductAnswer n 1) {out : Candidate n × ℕ}
    (h : out ∈ (RTree.run read (verifyCandidate S)).support) : out.2 ≤ 1 :=
  RTree.cost_le _ read h

/-! A finite public deleted-edge set. Diagonal entries are ignored by the
counter, so all malformed public data still has a defined interpretation. -/

abbrev LearnedEdges (n : ℕ) := Finset (Sym2 (Fin n))

def knownWeight (E : LearnedEdges n) (v u : Fin n) : ℕ :=
  if v ≠ u ∧ s(v, u) ∈ E then 1 else 0

@[simp] theorem knownWeight_self (E : LearnedEdges n) (v : Fin n) :
    knownWeight E v v = 0 := by simp [knownWeight]

theorem knownWeight_symm (E : LearnedEdges n) (v u : Fin n) :
    knownWeight E v u = knownWeight E u v := by
  by_cases h : v = u
  · subst u
    rfl
  · simp [knownWeight, h, Ne.symm h, Sym2.eq_swap (a := v) (b := u)]

theorem knownWeight_le_one (E : LearnedEdges n) (v u : Fin n) :
    knownWeight E v u ≤ 1 := by
  unfold knownWeight
  split_ifs <;> omega

def knownCount (E : LearnedEdges n) (S : Finset (Fin n)) (v : Fin n) : ℕ :=
  ∑ u ∈ S, knownWeight E v u

def residualCount (E : LearnedEdges n) (S : Finset (Fin n))
    (answer : ProductAnswer n 1) (v : Fin n) : ℕ :=
  if v ∈ S then 0 else (answer v).val - knownCount E S v

@[simp] theorem residualCount_inside (E : LearnedEdges n) (S : Finset (Fin n))
    (answer : ProductAnswer n 1) {v : Fin n} (hv : v ∈ S) :
    residualCount E S answer v = 0 := by simp [residualCount, hv]

theorem residualCount_le_answer (E : LearnedEdges n) (S : Finset (Fin n))
    (answer : ProductAnswer n 1) (v : Fin n) :
    residualCount E S answer v ≤ (answer v).val := by
  unfold residualCount
  split_ifs
  · exact Nat.zero_le _
  · exact Nat.sub_le _ _

/-- Proof-side realization of public learned edges; absent from every decoder. -/
def KnownSubgraph (E : LearnedEdges n) (G : CapacityGraph (Fin n) 1) : Prop :=
  ∀ v u, knownWeight E v u ≤ (G.w v u : ℕ)

theorem knownSubgraph_of_edges {E : LearnedEdges n} {G : CapacityGraph (Fin n) 1}
    (h : ∀ v u, v ≠ u → s(v, u) ∈ E → (G.w v u : ℕ) = 1) : KnownSubgraph E G := by
  intro v u
  by_cases he : v ≠ u ∧ s(v, u) ∈ E
  · simp [knownWeight, he, h v u he.1 he.2]
  · simp [knownWeight, he]

theorem knownCount_le_observed {E : LearnedEdges n} {G : CapacityGraph (Fin n) 1}
    (hE : KnownSubgraph E G) (S : Finset (Fin n)) {v : Fin n} (hv : v ∉ S) :
    knownCount E S v ≤ (productRead G S v).val := by
  rw [productRead_val, productNat_of_not_mem G S hv]
  exact Finset.sum_le_sum fun u _ => hE v u

/-- Semantic residual only: no public algorithm takes G as an argument. -/
def residualGraph (G : CapacityGraph (Fin n) 1) (E : LearnedEdges n) :
    CapacityGraph (Fin n) 1 where
  w v u := ⟨(G.w v u : ℕ) - knownWeight E v u,
    (Nat.sub_le _ _).trans_lt (G.w v u).isLt⟩
  symm v u := by
    apply Fin.ext
    change (G.w v u : ℕ) - knownWeight E v u = (G.w u v : ℕ) - knownWeight E u v
    rw [G.symm v u, knownWeight_symm]
  diag v := by
    apply Fin.ext
    change (G.w v v : ℕ) - knownWeight E v v = 0
    rw [G.diag]
    simp

@[simp] theorem residualGraph_w (G : CapacityGraph (Fin n) 1) (E : LearnedEdges n)
    (v u : Fin n) : ((residualGraph G E).w v u : ℕ) =
      (G.w v u : ℕ) - knownWeight E v u := rfl

theorem residualGraph_le (G : CapacityGraph (Fin n) 1) (E : LearnedEdges n)
    (v u : Fin n) : ((residualGraph G E).w v u : ℕ) ≤ (G.w v u : ℕ) :=
  Nat.sub_le _ _

/-- The public subtracted vector is the exact hidden residual product. -/
theorem residualCount_honest {E : LearnedEdges n} {G : CapacityGraph (Fin n) 1}
    (hE : KnownSubgraph E G) (S : Finset (Fin n)) (v : Fin n) :
    residualCount E S (productRead G S) v = productNat (residualGraph G E) S v := by
  by_cases hv : v ∈ S
  · rw [residualCount_inside E S _ hv, productNat_of_mem _ S hv]
  · rw [residualCount, if_neg hv, productRead_val, productNat_of_not_mem G S hv,
      productNat_of_not_mem (residualGraph G E) S hv, knownCount]
    simpa only [residualGraph_w] using
      (Finset.sum_tsub_distrib S (f := fun u => (G.w v u : ℕ))
        (g := fun u => knownWeight E v u) (fun u _ => hE v u)).symm

def ResidualNeighbor (G : CapacityGraph (Fin n) 1) (E : LearnedEdges n)
    (v u : Fin n) : Prop := (G.w v u : ℕ) = 1 ∧ s(v, u) ∉ E

theorem residualGraph_w_eq_indicator (G : CapacityGraph (Fin n) 1)
    (E : LearnedEdges n) (v u : Fin n) :
    ((residualGraph G E).w v u : ℕ) = if ResidualNeighbor G E v u then 1 else 0 := by
  rw [residualGraph_w]
  by_cases hvu : v = u
  · subst u
    simp [ResidualNeighbor, G.diag]
  · have hw : (G.w v u : ℕ) ≤ 1 := Nat.le_of_lt_succ (G.w v u).isLt
    by_cases he : s(v, u) ∈ E
    · have hk : knownWeight E v u = 1 := by simp [knownWeight, hvu, he]
      have hr : ¬ ResidualNeighbor G E v u := by simp [ResidualNeighbor, he]
      rw [hk, if_neg hr]
      omega
    · by_cases hw1 : (G.w v u : ℕ) = 1
      · simp [knownWeight, ResidualNeighbor, hvu, he, hw1]
      · have hw0 : (G.w v u : ℕ) = 0 := by omega
        simp [knownWeight, ResidualNeighbor, hvu, he, hw0]

theorem residualCount_eq_card {E : LearnedEdges n} {G : CapacityGraph (Fin n) 1}
    (hE : KnownSubgraph E G) (S : Finset (Fin n)) {v : Fin n} (hv : v ∉ S) :
    residualCount E S (productRead G S) v =
      (S.filter (ResidualNeighbor G E v)).card := by
  rw [residualCount_honest hE S v, productNat_of_not_mem _ S hv]
  simp_rw [residualGraph_w_eq_indicator]
  simpa using (Finset.sum_boole (R := ℕ) (ResidualNeighbor G E v) S)

theorem residualCount_pos_iff {E : LearnedEdges n} {G : CapacityGraph (Fin n) 1}
    (hE : KnownSubgraph E G) (S : Finset (Fin n)) {v : Fin n} (hv : v ∉ S) :
    0 < residualCount E S (productRead G S) v ↔ ∃ u ∈ S, ResidualNeighbor G E v u := by
  rw [residualCount_eq_card hE S hv, Finset.card_pos]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, (Finset.mem_filter.mp hu).1, (Finset.mem_filter.mp hu).2⟩
  · rintro ⟨u, hu, hres⟩
    exact ⟨u, Finset.mem_filter.mpr ⟨hu, hres⟩⟩

#print axioms cutLetterOfProduct_honest
#print axioms cutTreeToProduct_run
#print axioms cutTreeToProduct_count_law
#print axioms cutTreeToProduct_decoded_run
#print axioms cutTreeToProduct_successProb
#print axioms cutTreeToProduct_sound
#print axioms verifyCandidate_run
#print axioms verifyCandidate_sound
#print axioms knownSubgraph_of_edges
#print axioms knownCount_le_observed
#print axioms residualGraph_le
#print axioms residualCount_honest
#print axioms residualGraph_w_eq_indicator
#print axioms residualCount_eq_card
#print axioms residualCount_pos_iff

end
end CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms
