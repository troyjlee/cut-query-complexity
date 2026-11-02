import CutQueryComplexity.CanonicalST.Basic
import CutQueryComplexity.CanonicalST.Rows
import CutQueryComplexity.CanonicalST.Extension

/-!
# Degree peeling and seed discovery as public query programs

The graph is not an argument to any program or choice rule. Degree answers
initialize a cache; each removed vertex changes it using the discovered row.
Both loops have fixed finite fuel, including on arbitrary answer sequences.
-/

set_option autoImplicit false

namespace CutQueryComplexity.CanonicalST

open Finset WeightedGraph
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

structure PeelState (V : Type) where
  C : Finset V
  edges : Finset (V × V)
  coreDegrees : V → ℝ

def initialPeel (degrees : V → ℝ) : PeelState V := ⟨univ, ∅, degrees⟩

def lowVertices (D : ℕ) (P : PeelState V) : Finset V :=
  P.C.filter fun v => P.coreDegrees v < D

def peelStep (P : PeelState V) (v : V) (neighbors : Finset V) : PeelState V where
  C := P.C.erase v
  edges := P.edges ∪ neighbors.image (Prod.mk v)
  coreDegrees u := if u = v then 0 else P.coreDegrees u - if u ∈ neighbors then 1 else 0

def peelProgram (k D : ℕ) : (fuel : ℕ) → PeelState V →
    DTree (Finset V) ℝ (PeelState V) (fuel * D * ((k + 1) * 3))
  | 0, P => DTree.pure P
  | fuel + 1, P =>
      if h : (lowVertices D P).Nonempty then
        ((rowPrefix k D h.choose P.C).bind fun neighbors =>
          peelProgram k D fuel (peelStep P h.choose neighbors)).cast (by ring)
      else DTree.pure P

def assembleCore (P : PeelState V) (E : Finset (V × V)) : CoreData V where
  C := P.C
  K := AllPairs.decodeRecovered P.edges
  J := AllPairs.decodeRecovered E
  K_unit := decodeRecovered_unit _
  J_unit := decodeRecovered_unit _
  coreDegrees := P.coreDegrees

def seedProgram (k D : ℕ) (P : PeelState V) :
    DTree (Finset V) ℝ (CoreData V) (Fintype.card V * D * ((k + 1) * 3)) :=
  ((seedRows k D P.C.toList P.C).weaken (by
    simp only [length_toList]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right D (card_le_univ P.C)))).map
      (assembleCore P)

def coreBudget (V : Type) [Fintype V] (D : ℕ) : ℕ :=
  Fintype.card V + 6 * Fintype.card V * D * (searchDepth V + 1)

/-- Read degrees, peel for at most `n` steps, then take seed incidences.
Only public state and prior query replies select continuations. -/
def coreProgram (D : ℕ) : DTree (Finset V) ℝ (CoreData V) (coreBudget V D) :=
  ((cacheBlockCuts (id : V → V)).bind fun degrees =>
    (peelProgram (searchDepth V) D (Fintype.card V) (initialPeel degrees)).bind
      (seedProgram (searchDepth V) D)).cast (by unfold coreBudget; ring)

theorem coreProgram_cost (D : ℕ) (oracle : Finset V → ℝ) :
    (coreProgram (V := V) D).cost oracle ≤
      Fintype.card V + 6 * Fintype.card V * D * (Nat.clog 2 (Fintype.card V) + 1) :=
  DTree.cost_le _ _

/-- Proof-only loop invariant; no hidden graph is carried by the public state. -/
structure PeelInvariant (G : WeightedGraph V) (D : ℕ) (P : PeelState V) : Prop where
  outside_exact : ∀ u v, (AllPairs.decodeRecovered P.edges).w u v =
    if u ∈ P.C ∧ v ∈ P.C then 0 else G.w u v
  degrees_eq : ∀ v, P.coreDegrees v = (G.induce P.C).degree v
  edge_count : P.edges.card ≤ (Fintype.card V - P.C.card) * (D - 1)

theorem initialPeel_invariant (G : WeightedGraph V) (D : ℕ) :
    PeelInvariant G D (initialPeel G.degree) := by
  constructor
  · intro u v
    simp [initialPeel, AllPairs.decodeRecovered]
  · intro v
    simp [initialPeel, WeightedGraph.induce, WeightedGraph.degree]
  · simp [initialPeel]

omit [Fintype V] in
private theorem mem_row_image (R : Finset V) (v u w : V) :
    (u, w) ∈ R.image (Prod.mk v) ↔ u = v ∧ w ∈ R := by
  constructor
  · intro h
    obtain ⟨z, hz, he⟩ := mem_image.mp h
    have hu : v = u := congrArg Prod.fst he
    have hw : z = w := congrArg Prod.snd he
    subst u w
    exact ⟨rfl, hz⟩
  · rintro ⟨rfl, hw⟩
    exact mem_image.mpr ⟨w, hw, rfl⟩

omit [Fintype V] in
private theorem decode_union_w (E F : Finset (V × V)) (u w : V) :
    (AllPairs.decodeRecovered (E ∪ F)).w u w =
      max ((AllPairs.decodeRecovered E).w u w) ((AllPairs.decodeRecovered F).w u w) := by
  by_cases huw : u = w <;> by_cases he : (u, w) ∈ E <;> by_cases he' : (w, u) ∈ E <;>
    by_cases hf : (u, w) ∈ F <;> by_cases hf' : (w, u) ∈ F <;>
    simp [AllPairs.decodeRecovered, huw, he, he', hf, hf']

omit [Fintype V] in
private theorem decode_support_row_w (G : WeightedGraph V) (hG : AllPairsAudit.Unweighted G)
    (C : Finset V) (v u w : V) :
    (AllPairs.decodeRecovered ((AllPairs.rowSupport G v C).image (Prod.mk v))).w u w =
      if (u = v ∧ w ∈ C) ∨ (w = v ∧ u ∈ C) then G.w u w else 0 := by
  by_cases huw : u = w
  · subst w
    simp [AllPairs.decodeRecovered, G.diag]
  · by_cases hu : u = v
    · subst u
      rcases hG v w with hg | hg <;> by_cases hwC : w ∈ C <;>
        simp [AllPairs.decodeRecovered, AllPairs.rowSupport,
          huw, Ne.symm huw, hwC, hg]
    · by_cases hw : w = v
      · subst w
        rcases hG u v with hg | hg <;> by_cases huC : u ∈ C <;>
          simp [AllPairs.decodeRecovered, AllPairs.rowSupport,
            huw, Ne.symm huw, huC, G.symm v u, hg]
      · simp [AllPairs.decodeRecovered, huw, hu, hw, Ne.symm hu, Ne.symm hw]

private theorem induce_degree_eq (G : WeightedGraph V) (C : Finset V) (u : V) :
    (G.induce C).degree u = if u ∈ C then ∑ w ∈ C, G.w u w else 0 := by
  by_cases hu : u ∈ C <;> simp [WeightedGraph.degree, WeightedGraph.induce, hu]

private theorem induce_degree_erase (G : WeightedGraph V) (C : Finset V)
    {v : V} (hv : v ∈ C) (u : V) :
    (G.induce (C.erase v)).degree u =
      if u = v then 0 else (G.induce C).degree u - if u ∈ C then G.w u v else 0 := by
  by_cases huv : u = v
  · subst u
    simp [induce_degree_eq]
  · by_cases hu : u ∈ C
    · have hue : u ∈ C.erase v := mem_erase.mpr ⟨huv, hu⟩
      simp only [induce_degree_eq, hue, huv, hu, ↓reduceIte]
      have h := sum_erase_add (s := C) (f := fun w => G.w u w) hv
      linarith
    · have hue : u ∉ C.erase v := fun h => hu (mem_of_mem_erase h)
      simp [induce_degree_eq, huv, hu, hue]

omit [Fintype V] in
private theorem row_indicator (G : WeightedGraph V) (hG : AllPairsAudit.Unweighted G)
    (C : Finset V) (v u : V) :
    (if u ∈ AllPairs.rowSupport G v C then (1 : ℝ) else 0) =
      if u ∈ C then G.w u v else 0 := by
  rcases hG u v with h | h <;> by_cases hu : u ∈ C <;>
    simp [AllPairs.rowSupport, hu, G.symm v u, h]

/-- Exposing an actual low-degree row preserves exact outside edges and every
cached induced degree, and charges fewer than `D` new incidences. -/
theorem peelStep_invariant (G : WeightedGraph V) (hG : AllPairsAudit.Unweighted G)
    {D : ℕ} {P : PeelState V} (hP : PeelInvariant G D P) {v : V}
    (hv : v ∈ P.C) (hlow : P.coreDegrees v < D) :
    PeelInvariant G D (peelStep P v (AllPairs.rowSupport G v P.C)) := by
  have hrow : (AllPairs.rowSupport G v P.C).card < D := by
    have h := hlow
    rw [hP.degrees_eq, ← rowSupport_card_induce_degree G hG P.C hv] at h
    exact_mod_cast h
  constructor
  · intro u w
    change (AllPairs.decodeRecovered
      (P.edges ∪ (AllPairs.rowSupport G v P.C).image (Prod.mk v))).w u w = _
    rw [decode_union_w, hP.outside_exact, decode_support_row_w G hG]
    have hnonneg := G.nonneg u w
    change max (if u ∈ P.C ∧ w ∈ P.C then 0 else G.w u w)
      (if (u = v ∧ w ∈ P.C) ∨ (w = v ∧ u ∈ P.C) then G.w u w else 0) =
        if u ∈ P.C.erase v ∧ w ∈ P.C.erase v then 0 else G.w u w
    by_cases hu : u = v <;> by_cases hw : w = v <;>
      by_cases huC : u ∈ P.C <;> by_cases hwC : w ∈ P.C <;>
      simp_all [mem_erase]
  · intro u
    change (if u = v then 0 else P.coreDegrees u -
      if u ∈ AllPairs.rowSupport G v P.C then 1 else 0) = _
    rw [hP.degrees_eq, row_indicator G hG]
    exact (induce_degree_erase G P.C hv u).symm
  · have hcount : Fintype.card V - (P.C.erase v).card =
        Fintype.card V - P.C.card + 1 := by
      rw [card_erase_of_mem hv]
      have hcard := card_le_univ P.C
      have hpos := card_pos.mpr ⟨v, hv⟩
      omega
    change (P.edges ∪ (AllPairs.rowSupport G v P.C).image (Prod.mk v)).card ≤
      (Fintype.card V - (P.C.erase v).card) * (D - 1)
    calc
      _ ≤ P.edges.card + ((AllPairs.rowSupport G v P.C).image (Prod.mk v)).card :=
        card_union_le _ _
      _ ≤ (Fintype.card V - P.C.card) * (D - 1) + (D - 1) :=
        Nat.add_le_add hP.edge_count (card_image_le.trans (by omega))
      _ = _ := by rw [hcount]; ring

theorem no_low_min_degree {G : WeightedGraph V} {D : ℕ} {P : PeelState V}
    (hP : PeelInvariant G D P) (hstop : ¬ (lowVertices D P).Nonempty) :
    ∀ v ∈ P.C, (D : ℝ) ≤ (G.induce P.C).degree v := by
  intro v hv
  rw [← hP.degrees_eq]
  by_contra h
  exact hstop ⟨v, mem_filter.mpr ⟨hv, lt_of_not_ge h⟩⟩

/-- The actual bounded peeling loop terminates with its invariant and a
minimum-degree core. Its fuel decreases with the public active-vertex count. -/
theorem peelProgram_correct (G : WeightedGraph V) (hG : AllPairsAudit.Unweighted G)
    (k D : ℕ) (hn : Fintype.card V ≤ 2 ^ k) (fuel : ℕ) (P : PeelState V)
    (hP : PeelInvariant G D P) (hfuel : P.C.card ≤ fuel) :
    PeelInvariant G D ((peelProgram k D fuel P).eval G.cut) ∧
      ∀ v ∈ ((peelProgram k D fuel P).eval G.cut).C,
        (D : ℝ) ≤ (G.induce ((peelProgram k D fuel P).eval G.cut).C).degree v := by
  induction fuel generalizing P with
  | zero =>
      have hc : P.C = ∅ := card_eq_zero.mp (by omega)
      simp only [peelProgram, DTree.eval_pure]
      refine ⟨hP, ?_⟩
      simp [hc]
  | succ fuel ih =>
      by_cases hlo : (lowVertices D P).Nonempty
      · obtain ⟨hv, hl⟩ := mem_filter.mp hlo.choose_spec
        have hrow : (AllPairs.rowSupport G hlo.choose P.C).card ≤ D := by
          have h := hl
          rw [hP.degrees_eq, ← rowSupport_card_induce_degree G hG P.C hv] at h
          exact_mod_cast h.le
        simp only [peelProgram, dite_eq_left hlo, DTree.eval_cast, DTree.eval_bind]
        rw [rowPrefix_complete G k hn D hlo.choose P.C hrow]
        apply ih _ (peelStep_invariant G hG hP hv hl)
        change (P.C.erase hlo.choose).card ≤ fuel
        rw [card_erase_of_mem hv]
        have hpos := card_pos.mpr ⟨hlo.choose, hv⟩
        omega
      · simp only [peelProgram, dite_eq_right hlo, DTree.eval_pure]
        exact ⟨hP, no_low_min_degree hP hlo⟩

theorem seedProgram_eval (oracle : Finset V → ℝ) (k D : ℕ) (P : PeelState V) :
    (seedProgram k D P).eval oracle =
      assembleCore P ((seedRows k D P.C.toList P.C).eval oracle) := by
  simp [seedProgram, DTree.eval]

/-- The actual seed-query loop turns a fully peeled state into the required
core data. All seed incidence and size facts come from Rows' programs. -/
theorem seedProgram_spec (G : WeightedGraph V) (hG : AllPairsAudit.Unweighted G)
    (k D : ℕ) (hn : Fintype.card V ≤ 2 ^ k) (hn1 : 1 ≤ Fintype.card V)
    (hD : 1 ≤ D) (P : PeelState V) (hP : PeelInvariant G D P)
    (hdegree : ∀ v ∈ P.C, (D : ℝ) ≤ (G.induce P.C).degree v) :
    CoreSpec G D ((seedProgram k D P).eval G.cut) := by
  rw [seedProgram_eval]
  constructor
  · exact hP.outside_exact
  · exact seedRows_subgraph G hG k D hn P.C.toList P.C
  · exact seedRows_supported G k D hn P.C.toList P.C (fun _ hu => mem_toList.mp hu)
  · exact hP.degrees_eq
  · exact seedRows_min_degree G hG k D hn P.C hdegree
  · have he : P.edges.card < Fintype.card V * D := by
      calc
        P.edges.card ≤ (Fintype.card V - P.C.card) * (D - 1) := hP.edge_count
        _ ≤ Fintype.card V * (D - 1) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
        _ < Fintype.card V * D := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    have heR : (P.edges.card : ℝ) < (Fintype.card V : ℝ) * D := by exact_mod_cast he
    exact (decodeRecovered_mass_le P.edges).trans_lt heR
  · exact seedRows_mass_le G.cut k D P.C

private theorem degreeCache_eval (G : WeightedGraph V) :
    (cacheBlockCuts (id : V → V)).eval G.cut = G.degree := by
  rw [DTree.eval, cacheBlockCuts_run]
  funext v
  have hf : WeightedGraph.fiber (id : V → V) v = {v} := by
    ext u
    simp [WeightedGraph.fiber, WeightedGraph.pull]
  simp only [hf, G.cut_singleton]

/-- Correctness of the full public preprocessing program. The invariant and
both graph-size bounds are derived from the actual measured execution. -/
theorem coreProgram_correct (G : WeightedGraph V) (hG : AllPairsAudit.Unweighted G)
    (D : ℕ) (hn : 1 ≤ Fintype.card V) (hD : 1 ≤ D) :
    CoreSpec G D ((coreProgram (V := V) D).eval G.cut) := by
  have hdepth : Fintype.card V ≤ 2 ^ searchDepth V := Nat.le_pow_clog (by decide) _
  obtain ⟨hP, hdeg⟩ := peelProgram_correct G hG (searchDepth V) D hdepth
    (Fintype.card V) (initialPeel G.degree) (initialPeel_invariant G D) (by simp [initialPeel])
  simp only [coreProgram, DTree.eval_cast, DTree.eval_bind, degreeCache_eval]
  exact seedProgram_spec G hG (searchDepth V) D hdepth hn hD _ hP hdeg

/-- The same public program works for every unit input and every answer
sequence obeys the cap. The input graph is quantified after the program. -/
theorem coreProgram_spec (D : ℕ) (hn : 1 ≤ Fintype.card V) (hD : 1 ≤ D) :
    (∀ oracle : Finset V → ℝ, (coreProgram (V := V) D).cost oracle ≤
      Fintype.card V + 6 * Fintype.card V * D * (Nat.clog 2 (Fintype.card V) + 1)) ∧
    ∀ G : WeightedGraph V, AllPairsAudit.Unweighted G →
      CoreSpec G D ((coreProgram (V := V) D).eval G.cut) :=
  ⟨coreProgram_cost D, fun G hG => coreProgram_correct G hG D hn hD⟩

/-- On the genuine public preprocessing output, the fixed canonical family
contains an optimum of the original graph, in the paper's target orientation. -/
theorem coreProgram_canonical_optimum (G : WeightedGraph V)
    (hG : AllPairsAudit.Unweighted G) (D : ℕ) (hn : 1 ≤ Fintype.card V) (hD : 1 ≤ D)
    {s t : V} (hst : s ≠ t) :
    let A := (coreProgram (V := V) D).eval G.cut
    ∃ S ∈ canonicalFamily A.C A.K s t, IsSTMinCut G t s S := by
  let A := (coreProgram (V := V) D).eval G.cut
  have hA : CoreSpec G D A := coreProgram_correct G hG D hn hD
  have hsupp : ∀ u v, u ∉ A.C ∨ v ∉ A.C → (G.induce A.C).w u v = 0 := by
    intro u v h
    rcases h with hu | hv <;> simp [WeightedGraph.induce, *]
  obtain ⟨S, hS, hmin⟩ := canonicalFamily_contains_optimum A.C A.K (G.induce A.C) hst hsupp
  exact ⟨S, hS, by simpa only [hA.K_add_induce_eq] using hmin⟩

end
end CutQueryComplexity.CanonicalST

#print axioms CutQueryComplexity.CanonicalST.coreProgram_cost
#print axioms CutQueryComplexity.CanonicalST.initialPeel_invariant
#print axioms CutQueryComplexity.CanonicalST.seedProgram_spec
#print axioms CutQueryComplexity.CanonicalST.peelStep_invariant
#print axioms CutQueryComplexity.CanonicalST.peelProgram_correct
#print axioms CutQueryComplexity.CanonicalST.coreProgram_correct
#print axioms CutQueryComplexity.CanonicalST.coreProgram_spec
#print axioms CutQueryComplexity.CanonicalST.coreProgram_canonical_optimum
