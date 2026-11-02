import CutQueryComplexity.DirectedCertificate.Orientation
import CutQueryComplexity.DirectedCertificate.SparseBranching

/-! # An implicit graph of small total capacity (W5; `lem:prune`)

Inside the cut-equivalent orientation `G° = O.toGraph G` (`lem:orientation`) take the sparse
minimum-total in-packing `y = load a` and out-packing `z = outLoad b` (W3) of value
`λ = G.minValue`, rooted at an arbitrary `r`, and set `H_{uv} = max (y_{uv}) (z_{uv})`.

* `H ≤ G°` arcwise, `H` has global mincut exactly `λ`, total capacity `≤ 2 (n-1) λ`, and every
  arc of `H` is at most `λ` (`H_le`, `lam_le_out_H`, `isGlobalMinCut_H`, `minValue_H`,
  `total_H_le`, `H_le_lam`).
* Exceptional unordered pairs `exc = O.E ∪ freeArcs y ∪ freeArcs z`, `|exc| ≤ 5 n`. Off them a
  positive arc of `H` is the prescribed arc of `G°` and carries `G.sym.w` (`ord_arc`).
* Queries `O.queries ∪` pair queries of the new exceptional pairs, `≤ 30 n`.
* Competitor graph `H' = P.toGraph G'` (exceptional arcs: constants; retained ordinary arcs:
  `G'.sym.w`; else `0`); `H' ≤ G°′` arcwise and `F_{H'} ≤ F_{G'}` for consistent `G'`.
* Restricted compiler: directed out/in partial stars, symmetrized partial stars, degrees and
  pair capacities of `H'` each cost `≤ 3` original queries (`outStarC`, ...).
-/

namespace CutQueryComplexity.DirectedCertificate

open Finset WeightedDiGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Small facts -/

theorem WeightedDiGraph.minValue_nonneg (G : WeightedDiGraph V) : 0 ≤ G.minValue := by
  unfold minValue
  split_ifs with h
  · exact Finset.le_inf' _ _ fun S _ => G.out_nonneg S
  · exact le_rfl

theorem load_nonneg' {r : V} {a : InArb r → ℝ} (ha : ∀ T, 0 ≤ a T) (u v : V) :
    0 ≤ load a u v :=
  sum_nonneg fun T _ => mul_nonneg (ha T) (by split_ifs <;> norm_num)

theorem load_self {r : V} (a : InArb r → ℝ) (v : V) : load a v v = 0 :=
  sum_eq_zero fun T _ => by simp [(mem_inArbs.1 T.2).irrefl v]

theorem load_le_sum {r : V} {a : InArb r → ℝ} (ha : ∀ T, 0 ≤ a T) (u v : V) :
    load a u v ≤ ∑ T, a T :=
  sum_le_sum fun T _ => by
    split_ifs
    · rw [mul_one]
    · rw [mul_zero]; exact ha T

omit [DecidableEq V] in
theorem properShore_of_not_mem {S : Finset V} {r : V} (hS : S.Nonempty) (hr : r ∉ S) :
    ProperShore S :=
  ⟨hS, fun h => hr (h ▸ mem_univ r)⟩

/-! ## The pruning data -/

/-- The actual-input choices of `lem:prune`: an orientation certificate, a root, and sparse
minimum-total in- and out-arborescence packings of value `λ = G.minValue` in `G°`. -/
structure PruningData (G : WeightedDiGraph V) where
  O : OrientationCert G
  r : V
  /-- In-arborescence packing toward `r` (arc loads `load a`). -/
  a : InArb r → ℝ
  a_nonneg : ∀ T, 0 ≤ a T
  a_sum : ∑ T, a T = G.minValue
  a_le : ∀ u v, load a u v ≤ (O.toGraph G).c u v
  a_total : total (load a) = G.minValue * ((Fintype.card V : ℝ) - 1)
  a_free : (freeArcs (O.toGraph G) (load a)).card ≤ 2 * (Fintype.card V - 1)
  /-- Out-arborescence packing from `r` (arc loads `outLoad b`). -/
  b : InArb r → ℝ
  b_nonneg : ∀ T, 0 ≤ b T
  b_sum : ∑ T, b T = G.minValue
  b_le : ∀ u v, outLoad b u v ≤ (O.toGraph G).c u v
  b_total : total (outLoad b) = G.minValue * ((Fintype.card V : ℝ) - 1)
  b_free : (freeArcs (O.toGraph G) (outLoad b)).card ≤ 2 * (Fintype.card V - 1)

/-- Every input admits pruning data (for every root). -/
theorem exists_pruningData (G : WeightedDiGraph V) (r : V) : Nonempty (PruningData G) := by
  obtain ⟨O⟩ := exists_orientationCert G
  have hlam := G.minValue_nonneg
  have hin : ∀ S : Finset V, S.Nonempty → r ∉ S → G.minValue ≤ (O.toGraph G).out S :=
    fun S hS hr => by
      rw [O.out_toGraph_self]; exact G.minValue_le (properShore_of_not_mem hS hr)
  have hout : ∀ S : Finset V, S.Nonempty → r ∉ S → G.minValue ≤ (O.toGraph G).out Sᶜ :=
    fun S hS hr => by
      rw [O.out_toGraph_self]
      refine G.minValue_le ⟨⟨r, mem_compl.2 hr⟩, fun h => ?_⟩
      obtain ⟨x, hx⟩ := hS
      exact (mem_compl.1 (h ▸ mem_univ x)) hx
  obtain ⟨a, ha, hsa, hla, hta, hfa⟩ := exists_sparse_inArb_packing (O.toGraph G) r _ hlam hin
  obtain ⟨b, hb, hsb, hlb, htb, hfb⟩ := exists_sparse_outArb_packing (O.toGraph G) r _ hlam hout
  exact ⟨⟨O, r, a, ha, hsa, hla, hta, hfa, b, hb, hsb, hlb, htb, hfb⟩⟩

namespace PruningData
variable {G : WeightedDiGraph V} (P : PruningData G)

noncomputable section

/-! ### The graph `H` -/

/-- `H_{uv} = max (y_{uv}) (z_{uv})`. -/
def H : WeightedDiGraph V where
  c u v := max (load P.a u v) (outLoad P.b u v)
  nonneg u v := le_max_of_le_left (load_nonneg' P.a_nonneg u v)
  diag v := by rw [outLoad_eq_load, load_self, load_self, max_self]

theorem H_c (u v : V) : P.H.c u v = max (load P.a u v) (outLoad P.b u v) := rfl

theorem outLoad_nonneg (u v : V) : 0 ≤ outLoad P.b u v := load_nonneg' P.b_nonneg v u

/-- `H ≤ G°` arcwise. -/
theorem H_le (u v : V) : P.H.c u v ≤ (P.O.toGraph G).c u v := max_le (P.a_le u v) (P.b_le u v)

/-- Every arc of `H` is at most `λ`. -/
theorem H_le_lam (u v : V) : P.H.c u v ≤ G.minValue :=
  max_le (P.a_sum ▸ load_le_sum P.a_nonneg u v)
    (by rw [outLoad_eq_load, ← P.b_sum]; exact load_le_sum P.b_nonneg v u)

/-- Every proper shore of `H` has outgoing capacity at least `λ`: shores avoiding `r` by the
in-packing, shores containing `r` (complement avoids `r`) by the out-packing. -/
theorem lam_le_out_H {S : Finset V} (hS : ProperShore S) : G.minValue ≤ P.H.out S := by
  by_cases hr : P.r ∈ S
  · have h := cut_of_outArb_packing P.H P.r G.minValue P.b P.b_nonneg P.b_sum
      (fun u v => le_max_right _ _) Sᶜ ?_ (fun h => mem_compl.1 h hr)
    · rwa [compl_compl] at h
    · obtain ⟨S1, S2⟩ := hS
      by_contra h
      rw [not_nonempty_iff_eq_empty, compl_eq_empty_iff] at h
      exact S2 h
  · exact cut_of_inArb_packing P.H P.r G.minValue P.a P.a_nonneg P.a_sum
      (fun u v => le_max_left _ _) S hS.1 hr

theorem out_H_le (S : Finset V) : P.H.out S ≤ G.out S := by
  rw [← P.O.out_toGraph_self S]
  exact sum_le_sum fun u _ => sum_le_sum fun v _ => P.H_le u v

/-- An optimal shore of `G` is an optimal shore of `H`, of the same value. -/
theorem isGlobalMinCut_H {S : Finset V} (hS : IsGlobalMinCut G S) :
    IsGlobalMinCut P.H S ∧ P.H.out S = G.minValue := by
  have h1 : P.H.out S = G.minValue :=
    le_antisymm ((P.out_H_le S).trans hS.out_eq_minValue.le) (P.lam_le_out_H hS.1)
  exact ⟨⟨hS.1, fun T hT => h1 ▸ P.lam_le_out_H hT⟩, h1⟩

/-- `H` has global mincut exactly `λ`. -/
theorem minValue_H (hn : 2 ≤ Fintype.card V) : P.H.minValue = G.minValue := by
  obtain ⟨S, hS⟩ := exists_isGlobalMinCut G hn
  obtain ⟨h1, h2⟩ := P.isGlobalMinCut_H hS
  rw [← h1.out_eq_minValue, h2]

/-- Total capacity of `H` is at most `2 (n-1) λ`. -/
theorem total_H_le : total P.H.c ≤ 2 * (((Fintype.card V : ℝ) - 1) * G.minValue) := by
  have h : total P.H.c ≤ total (load P.a) + total (outLoad P.b) := by
    unfold total
    rw [← sum_add_distrib]
    refine sum_le_sum fun u _ => ?_
    rw [← sum_add_distrib]
    refine sum_le_sum fun v _ => max_le ?_ ?_
    · linarith [P.outLoad_nonneg u v]
    · linarith [load_nonneg' P.a_nonneg u v]
  rw [P.a_total, P.b_total] at h
  linarith

/-! ### Exceptional pairs and the shape of `H` off them -/

/-- The new exceptional arcs: free arcs of either packing. -/
def newPairs : Finset (V × V) :=
  freeArcs (P.O.toGraph G) (load P.a) ∪ freeArcs (P.O.toGraph G) (outLoad P.b)

/-- Exceptional unordered pairs of `H` (read through `IsExc`). -/
def exc : Finset (V × V) := P.O.E ∪ P.newPairs

theorem card_newPairs : P.newPairs.card ≤ 4 * (Fintype.card V - 1) :=
  (card_union_le _ _).trans (by have := P.a_free; have := P.b_free; omega)

theorem card_exc : P.exc.card ≤ 5 * Fintype.card V :=
  (card_union_le _ _).trans (by have := P.O.card_E; have := P.card_newPairs; omega)

theorem isExc_of_O {u v : V} (h : IsExc P.O.E u v) : IsExc P.exc u v :=
  h.imp (fun h => mem_union_left _ h) (fun h => mem_union_left _ h)

theorem isExc_of_new {u v : V} (h : (u, v) ∈ P.newPairs) : IsExc P.exc u v :=
  Or.inl (mem_union_right _ h)

/-- **Off the exceptional pairs, a positive arc of `H` is a saturated packing arc**: it is the
prescribed arc of `G°` (`sgn = 1`), carrying the original symmetrized weight. -/
theorem ord_arc {u v : V} (hE : ¬ IsExc P.exc u v) (hpos : 0 < P.H.c u v) :
    P.O.sgn u v = 1 ∧ P.H.c u v = G.sym.w u v ∧ (P.O.toGraph G).c u v = G.sym.w u v ∧
      P.H.c v u = 0 := by
  have hO : ¬ IsExc P.O.E u v := fun h => hE (P.isExc_of_O h)
  have hy : ¬ (u, v) ∈ freeArcs (P.O.toGraph G) (load P.a) :=
    fun h => hE (P.isExc_of_new (mem_union_left _ h))
  have hz : ¬ (u, v) ∈ freeArcs (P.O.toGraph G) (outLoad P.b) :=
    fun h => hE (P.isExc_of_new (mem_union_right _ h))
  rw [mem_freeArcs] at hy hz
  have hya := P.a_le u v
  have hzb := P.b_le u v
  -- `H u v = G°.c u v`
  have hHg : P.H.c u v = (P.O.toGraph G).c u v := by
    rw [H_c] at hpos ⊢
    rcases lt_max_iff.1 hpos with h | h
    · have : load P.a u v = (P.O.toGraph G).c u v := le_antisymm hya (not_lt.1 fun h' => hy ⟨h, h'⟩)
      rw [this]; exact max_eq_left (this ▸ hzb)
    · have : outLoad P.b u v = (P.O.toGraph G).c u v :=
        le_antisymm hzb (not_lt.1 fun h' => hz ⟨h, h'⟩)
      rw [this]; exact max_eq_right (this ▸ hya)
  have hgpos : 0 < (P.O.toGraph G).c u v := hHg ▸ hpos
  have hwpos : 0 < G.sym.w u v := by
    rcases (G.sym.nonneg u v).lt_or_eq with h | h
    · exact h
    · rw [P.O.toGraph_c_zero G h.symm, ← h, zero_div] at hgpos; exact absurd hgpos (lt_irrefl 0)
  have hs : P.O.sgn u v = 1 := by
    rcases P.O.sgn_ord u v hO hwpos with h | h
    · exact h
    · rw [P.O.toGraph_c_neg G hO h] at hgpos; exact absurd hgpos (lt_irrefl 0)
  have hg : (P.O.toGraph G).c u v = G.sym.w u v := P.O.toGraph_c_pos G hO hs
  refine ⟨hs, hHg.trans hg, hg, le_antisymm ?_ (P.H.nonneg v u)⟩
  rw [← P.O.toGraph_c_neg G (fun h => hO h.symm) (by rw [P.O.sgn_antisymm, hs])]
  exact P.H_le v u

/-- Retained ordinary arcs: non-exceptional arcs of positive `H`-capacity. A mask fixed by
the actual input. -/
def R (u v : V) : Prop := ¬ IsExc P.exc u v ∧ 0 < P.H.c u v

instance (u v : V) : Decidable (P.R u v) := by unfold R; infer_instance

theorem R_H {u v : V} (h : P.R u v) : P.H.c u v = G.sym.w u v := (P.ord_arc h.1 h.2).2.1

theorem R_sgn {u v : V} (h : P.R u v) : P.O.sgn u v = 1 := (P.ord_arc h.1 h.2).1

/-- A retained pair is retained in one direction only. -/
theorem R_rev {u v : V} (h : P.R u v) : ¬ P.R v u := fun h' => by
  have := (P.ord_arc h.1 h.2).2.2.2; linarith [h'.2]

theorem H_eq_zero {u v : V} (hE : ¬ IsExc P.exc u v) (hR : ¬ P.R u v) : P.H.c u v = 0 :=
  le_antisymm (not_lt.1 fun h => hR ⟨hE, h⟩) (P.H.nonneg u v)

/-! ### Queries -/

/-- `Q_H`: the orientation queries plus the pair queries of the new exceptional pairs. -/
def queries : Finset (Finset V) :=
  P.O.queries ∪ P.newPairs.biUnion fun p => (Measurement.pair p.1 p.2).shores

theorem card_queries : P.queries.card ≤ 30 * Fintype.card V := by
  have h1 : (P.newPairs.biUnion fun p => (Measurement.pair p.1 p.2).shores).card ≤
      3 * P.newPairs.card := by
    refine card_biUnion_le.trans ?_
    calc ∑ p ∈ P.newPairs, (Measurement.pair p.1 p.2).shores.card
        ≤ ∑ _p ∈ P.newPairs, 3 := sum_le_sum fun p _ => Measurement.card_shores_le _
      _ = 3 * P.newPairs.card := by rw [sum_const, smul_eq_mul, mul_comm]
  refine (card_union_le _ _).trans ?_
  have := P.O.card_queries
  have := P.card_newPairs
  omega

theorem consistent_O {G' : WeightedDiGraph V} (hG' : Consistent G G' P.queries) :
    Consistent G G' P.O.queries := hG'.mono subset_union_left

/-- The queries fix the symmetrized capacity of every exceptional pair. -/
theorem exc_w {G' : WeightedDiGraph V} (hG' : Consistent G G' P.queries) {u v : V}
    (h : IsExc P.exc u v) : G'.sym.w u v = G.sym.w u v := by
  have hp : ∀ p ∈ P.newPairs, G'.sym.w p.1 p.2 = G.sym.w p.1 p.2 := fun p hp =>
    Consistent.sym_w_eq (hG'.mono (subset_union_right.trans' (subset_biUnion_of_mem
      (fun p : V × V => (Measurement.pair p.1 p.2).shores) hp)))
  rcases h with h | h <;> rcases mem_union.1 h with h | h
  · exact P.O.exc_w G' (P.consistent_O hG') u v (Or.inl h)
  · exact hp _ h
  · exact P.O.exc_w G' (P.consistent_O hG') u v (Or.inr h)
  · rw [G'.sym.symm, G.sym.symm]; exact hp _ h

/-- On an exceptional pair, `G°′` has the same arcs as `G°`. -/
theorem toGraph_O_exc {G' : WeightedDiGraph V} (hG' : Consistent G G' P.queries) {u v : V}
    (h : IsExc P.exc u v) : (P.O.toGraph G').c u v = (P.O.toGraph G).c u v := by
  by_cases hO : IsExc P.O.E u v
  · rw [P.O.toGraph_c_exc G' hO, P.O.toGraph_c_exc G hO]
  · simp only [P.O.toGraph_c, hO, ↓reduceIte, P.exc_w hG' h]

/-! ### The competitor graph `H'` -/

/-- Capacities of the induced competitor graph. -/
def cap (G' : WeightedDiGraph V) (u v : V) : ℝ :=
  if IsExc P.exc u v then P.H.c u v else if P.R u v then G'.sym.w u v else 0

/-- **The induced graph `H'` of a competitor `G'`** (same masks and constants for every
`G'`). Pairs absent from the actual input are ignored. -/
def toGraph (G' : WeightedDiGraph V) : WeightedDiGraph V where
  c := P.cap G'
  nonneg u v := by
    unfold cap
    split_ifs
    · exact P.H.nonneg u v
    · exact G'.sym.nonneg u v
    · exact le_rfl
  diag v := by
    unfold cap
    split_ifs with h1 h2
    · exact P.H.diag v
    · exact absurd (P.H.diag v ▸ h2.2) (lt_irrefl 0)
    · rfl

theorem toGraph_c (G' : WeightedDiGraph V) (u v : V) :
    (P.toGraph G').c u v =
      if IsExc P.exc u v then P.H.c u v else if P.R u v then G'.sym.w u v else 0 := rfl

theorem toGraph_c_exc (G' : WeightedDiGraph V) {u v : V} (h : IsExc P.exc u v) :
    (P.toGraph G').c u v = P.H.c u v := by simp only [toGraph_c, h, ↓reduceIte]

theorem toGraph_c_R (G' : WeightedDiGraph V) {u v : V} (h : P.R u v) :
    (P.toGraph G').c u v = G'.sym.w u v := by simp only [toGraph_c, h.1, h, ↓reduceIte]

theorem toGraph_c_other (G' : WeightedDiGraph V) {u v : V} (hE : ¬ IsExc P.exc u v)
    (hR : ¬ P.R u v) : (P.toGraph G').c u v = 0 := by simp only [toGraph_c, hE, hR, ↓reduceIte]

/-- On the actual input the construction returns `H` (only there). -/
theorem toGraph_self (u v : V) : (P.toGraph G).c u v = P.H.c u v := by
  by_cases hE : IsExc P.exc u v
  · exact P.toGraph_c_exc G hE
  by_cases hR : P.R u v
  · rw [P.toGraph_c_R G hR, P.R_H hR]
  · rw [P.toGraph_c_other G hE hR, P.H_eq_zero hE hR]

/-- **Arcwise domination** `H' ≤ G°′` for every consistent competitor. -/
theorem toGraph_le {G' : WeightedDiGraph V} (hG' : Consistent G G' P.queries) (u v : V) :
    (P.toGraph G').c u v ≤ (P.O.toGraph G').c u v := by
  by_cases hE : IsExc P.exc u v
  · rw [P.toGraph_c_exc G' hE, P.toGraph_O_exc hG' hE]; exact P.H_le u v
  by_cases hR : P.R u v
  · rw [P.toGraph_c_R G' hR, P.O.toGraph_c_pos G' (fun h => hE (P.isExc_of_O h)) (P.R_sgn hR)]
  · rw [P.toGraph_c_other G' hE hR]; exact (P.O.toGraph G').nonneg u v

/-- **Cutwise domination** `F_{H'}(S) ≤ F_{G'}(S)` for every consistent competitor. -/
theorem out_toGraph_le {G' : WeightedDiGraph V} (hG' : Consistent G G' P.queries)
    (S : Finset V) : (P.toGraph G').out S ≤ G'.out S := by
  rw [← P.O.out_eq G' (P.consistent_O hG') S]
  exact sum_le_sum fun u _ => sum_le_sum fun v _ => P.toGraph_le hG' u v

/-! ### The restricted measurement compiler -/

/-- Retained ordinary out-neighbours of `v` in `T`. -/
def outSet (v : V) (T : Finset V) : Finset V := T.filter fun u => P.R v u

/-- Retained ordinary in-neighbours of `v` in `T`. -/
def inSet (v : V) (T : Finset V) : Finset V := T.filter fun u => P.R u v

/-- Known exceptional contribution to the directed out-star of `v` over `T`. -/
def outConst (v : V) (T : Finset V) : ℝ := ∑ u ∈ T.filter fun u => IsExc P.exc v u, P.H.c v u

/-- Known exceptional contribution to the directed in-star of `v` over `T`. -/
def inConst (v : V) (T : Finset V) : ℝ := ∑ u ∈ T.filter fun u => IsExc P.exc u v, P.H.c u v

theorem cap_split (G' : WeightedDiGraph V) (u v : V) :
    (P.toGraph G').c u v = (if IsExc P.exc u v then P.H.c u v else 0) +
      (if P.R u v then G'.sym.w u v else 0) := by
  rw [toGraph_c]
  by_cases hE : IsExc P.exc u v
  · have hR : ¬ P.R u v := fun h => h.1 hE
    simp [hE, hR]
  · simp [hE]

/-- Directed out-star of `H'`: a known constant plus a symmetrized partial star of `G'`. -/
theorem outStar_eq (G' : WeightedDiGraph V) (v : V) (T : Finset V) :
    ∑ u ∈ T, (P.toGraph G').c v u = P.outConst v T + G'.symStar v (P.outSet v T) := by
  simp only [cap_split, sum_add_distrib, outConst, outSet, symStar, sum_filter]

/-- Directed in-star of `H'`: a known constant plus a symmetrized partial star of `G'`. -/
theorem inStar_eq (G' : WeightedDiGraph V) (v : V) (T : Finset V) :
    ∑ u ∈ T, (P.toGraph G').c u v = P.inConst v T + G'.symStar v (P.inSet v T) := by
  simp only [cap_split, sum_add_distrib, inConst, inSet, symStar, sum_filter]
  congr 1
  exact sum_congr rfl fun u _ => by rw [G'.sym.symm]

theorem disjoint_out_in (v : V) (T : Finset V) : Disjoint (P.outSet v T) (P.inSet v T) := by
  rw [disjoint_left]
  intro u h1 h2
  exact P.R_rev (mem_filter.1 h1).2 (mem_filter.1 h2).2

/-- Symmetrized partial star of `H'`: a known constant plus one symmetrized partial star of
`G'` (over the retained ordinary neighbours of `v` in `T`). -/
theorem symStar_eq (G' : WeightedDiGraph V) (v : V) (T : Finset V) :
    (P.toGraph G').symStar v T =
      (P.outConst v T + P.inConst v T) + G'.symStar v (P.outSet v T ∪ P.inSet v T) := by
  have h : (P.toGraph G').symStar v T =
      ∑ u ∈ T, (P.toGraph G').c v u + ∑ u ∈ T, (P.toGraph G').c u v := by
    rw [WeightedDiGraph.symStar, ← sum_add_distrib]; rfl
  rw [h, outStar_eq, inStar_eq, symStar, symStar, symStar, sum_union (P.disjoint_out_in v T)]
  ring

/-- Compiled directed out-star `Σ_{u ∈ T} H'_{vu}`: `≤ 3` original queries. -/
def outStarC (v : V) (T : Finset V) :
    Compiled G (fun G' => ∑ u ∈ T, (P.toGraph G').c v u) :=
  ((Measurement.compile G (.star v (P.outSet v T))).map (P.outConst v T + ·)).congr
    fun G' => (P.outStar_eq G' v T).symm

/-- Compiled directed in-star `Σ_{u ∈ T} H'_{uv}`: `≤ 3` original queries. -/
def inStarC (v : V) (T : Finset V) :
    Compiled G (fun G' => ∑ u ∈ T, (P.toGraph G').c u v) :=
  ((Measurement.compile G (.star v (P.inSet v T))).map (P.inConst v T + ·)).congr
    fun G' => (P.inStar_eq G' v T).symm

/-- Compiled symmetrized partial star `Σ_{u ∈ T} u_{H'}(v,u)`: `≤ 3` original queries. -/
def symStarC (v : V) (T : Finset V) :
    Compiled G (fun G' => (P.toGraph G').symStar v T) :=
  ((Measurement.compile G (.star v (P.outSet v T ∪ P.inSet v T))).map
    (P.outConst v T + P.inConst v T + ·)).congr fun G' => (P.symStar_eq G' v T).symm

theorem outStarC_cost (v : V) (T : Finset V) : (P.outStarC v T).cost ≤ 3 :=
  Measurement.compile_cost_le G _

theorem inStarC_cost (v : V) (T : Finset V) : (P.inStarC v T).cost ≤ 3 :=
  Measurement.compile_cost_le G _

theorem symStarC_cost (v : V) (T : Finset V) : (P.symStarC v T).cost ≤ 3 :=
  Measurement.compile_cost_le G _

/-- Out-degree of `H'`. -/
def outdegC (v : V) : Compiled G (fun G' => (P.toGraph G').outdeg v) :=
  (P.outStarC v univ).congr fun _ => rfl

/-- In-degree of `H'`. -/
def indegC (v : V) : Compiled G (fun G' => (P.toGraph G').indeg v) :=
  (P.inStarC v univ).congr fun _ => rfl

/-- Directed arc `H'_{vw}` (determined because the masks are fixed). -/
def arcC (v w : V) : Compiled G (fun G' => (P.toGraph G').c v w) :=
  (P.outStarC v {w}).congr fun _ => sum_singleton _ _

/-- Pair capacity `u_{H'}(v,w)`. -/
def pairC (v w : V) : Compiled G (fun G' => (P.toGraph G').sym.w v w) :=
  (P.symStarC v {w}).congr fun _ => by simp [WeightedDiGraph.symStar]

theorem outdegC_cost (v : V) : (P.outdegC v).cost ≤ 3 := P.outStarC_cost v univ
theorem indegC_cost (v : V) : (P.indegC v).cost ≤ 3 := P.inStarC_cost v univ
theorem arcC_cost (v w : V) : (P.arcC v w).cost ≤ 3 := P.outStarC_cost v {w}
theorem pairC_cost (v w : V) : (P.pairC v w).cost ≤ 3 := P.symStarC_cost v {w}

/-- The compiled value is that of `H` itself: a competitor consistent on the measurement's
shores has the same directed out-star in `H'` as `H` has. -/
theorem outStar_fixed {G' : WeightedDiGraph V} (v : V) (T : Finset V)
    (h : Consistent G G' (P.outStarC v T).shores) :
    ∑ u ∈ T, (P.toGraph G').c v u = ∑ u ∈ T, P.H.c v u := by
  rw [(P.outStarC v T).fixes G' h]
  exact sum_congr rfl fun u _ => P.toGraph_self v u

theorem inStar_fixed {G' : WeightedDiGraph V} (v : V) (T : Finset V)
    (h : Consistent G G' (P.inStarC v T).shores) :
    ∑ u ∈ T, (P.toGraph G').c u v = ∑ u ∈ T, P.H.c u v := by
  rw [(P.inStarC v T).fixes G' h]
  exact sum_congr rfl fun u _ => P.toGraph_self u v

theorem symStar_fixed {G' : WeightedDiGraph V} (v : V) (T : Finset V)
    (h : Consistent G G' (P.symStarC v T).shores) :
    (P.toGraph G').symStar v T = P.H.symStar v T := by
  rw [(P.symStarC v T).fixes G' h]
  exact sum_congr rfl fun u _ => by rw [sym_w, sym_w, P.toGraph_self, P.toGraph_self]

/-! ### The retained mask as a finset, and the support bound -/

/-- The retained ordinary arcs, as a finset of ordered pairs. -/
def ret : Finset (V × V) := univ.filter fun p => P.R p.1 p.2

theorem mem_ret {u v : V} : (u, v) ∈ P.ret ↔ P.R u v := by simp [ret]

/-- Number of unordered pairs of `G` with `0 < u_e < t` (the TeX's `q(t)`). -/
def q (G : WeightedDiGraph V) (t : ℝ) : ℕ :=
  ((univ.filter fun p : V × V => 0 < G.sym.w p.1 p.2 ∧ G.sym.w p.1 p.2 < t).image
    fun p => s(p.1, p.2)).card

/-- Ordinary retained arcs of weight at least `t` are at most `2 (n-1) λ / t` many. -/
theorem card_heavy_le (t : ℝ) :
    t * ((P.ret.filter fun p => t ≤ G.sym.w p.1 p.2).card : ℝ) ≤
      2 * (((Fintype.card V : ℝ) - 1) * G.minValue) := by
  refine le_trans ?_ P.total_H_le
  set F := P.ret.filter fun p => t ≤ G.sym.w p.1 p.2
  have h1 : t * (F.card : ℝ) ≤ ∑ p ∈ F, P.H.c p.1 p.2 := by
    rw [mul_comm, ← nsmul_eq_mul, ← sum_const]
    refine sum_le_sum fun p hp => ?_
    obtain ⟨hp1, hp2⟩ := mem_filter.1 hp
    rw [P.R_H ((mem_filter.1 hp1).2)]; exact hp2
  refine h1.trans ?_
  have h2 : total P.H.c = ∑ p : V × V, P.H.c p.1 p.2 := by
    rw [total, ← univ_product_univ, sum_product]
  rw [h2]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun p _ _ => P.H.nonneg _ _

/-- Ordinary retained light arcs inject into the unordered light pairs of `G`. -/
theorem card_light_le (t : ℝ) :
    (P.ret.filter fun p => G.sym.w p.1 p.2 < t).card ≤ q G t := by
  unfold q
  rw [← card_image_of_injOn (f := fun p : V × V => s(p.1, p.2))]
  · refine card_le_card fun s hs => ?_
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hs
    obtain ⟨hp1, hp2⟩ := mem_filter.1 hp
    have hR := (mem_filter.1 hp1).2
    refine mem_image.2 ⟨p, mem_filter.2 ⟨mem_univ _, ?_, hp2⟩, rfl⟩
    rw [← P.R_H hR]; exact hR.2
  · rintro ⟨u, v⟩ hp ⟨u', v'⟩ hp' h
    have hR := (mem_filter.1 (mem_filter.1 hp).1).2
    have hR' := (mem_filter.1 (mem_filter.1 hp').1).2
    rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact absurd hR' (P.R_rev hR)

/-- Arcs on exceptional pairs. -/
def excArcs : Finset (V × V) := P.exc ∪ P.exc.image Prod.swap

/-- **Support bound** `|supp H| ≤ 2 |exc| + q(t) + 2 (n-1) λ / t` (with `|exc| ≤ 5 n`). -/
theorem card_supp_le {t : ℝ} (ht : 0 < t) :
    ((univ.filter fun p : V × V => 0 < P.H.c p.1 p.2).card : ℝ) ≤
      2 * P.exc.card + q G t + 2 * (((Fintype.card V : ℝ) - 1) * G.minValue) / t := by
  have hsub : (univ.filter fun p : V × V => 0 < P.H.c p.1 p.2) ⊆
      P.excArcs ∪ ((P.ret.filter fun p => G.sym.w p.1 p.2 < t) ∪
        P.ret.filter fun p => t ≤ G.sym.w p.1 p.2) := by
    rintro ⟨u, v⟩ hp
    have hpos := (mem_filter.1 hp).2
    by_cases hE : IsExc P.exc u v
    · refine mem_union_left _ ?_
      rcases hE with h | h
      · exact mem_union_left _ h
      · exact mem_union_right _ (mem_image.2 ⟨(v, u), h, rfl⟩)
    · have hr : (u, v) ∈ P.ret := P.mem_ret.2 ⟨hE, hpos⟩
      refine mem_union_right _ ?_
      by_cases hl : G.sym.w u v < t
      · exact mem_union_left _ (mem_filter.2 ⟨hr, hl⟩)
      · exact mem_union_right _ (mem_filter.2 ⟨hr, not_lt.1 hl⟩)
  have hc := card_le_card hsub
  have h1 : P.excArcs.card ≤ 2 * P.exc.card :=
    (card_union_le _ _).trans (by have := card_image_le (s := P.exc) (f := Prod.swap); omega)
  have h2 := P.card_light_le t
  have h3 := P.card_heavy_le t
  have hu1 := card_union_le P.excArcs ((P.ret.filter fun p => G.sym.w p.1 p.2 < t) ∪
        P.ret.filter fun p => t ≤ G.sym.w p.1 p.2)
  have hu2 := card_union_le (P.ret.filter fun p => G.sym.w p.1 p.2 < t)
        (P.ret.filter fun p => t ≤ G.sym.w p.1 p.2)
  have hc'' : ((univ.filter fun p : V × V => 0 < P.H.c p.1 p.2).card : ℝ) ≤
      P.excArcs.card + (P.ret.filter fun p => G.sym.w p.1 p.2 < t).card +
        (P.ret.filter fun p => t ≤ G.sym.w p.1 p.2).card := by exact_mod_cast (by omega)
  have h3' : ((P.ret.filter fun p => t ≤ G.sym.w p.1 p.2).card : ℝ) ≤
      2 * (((Fintype.card V : ℝ) - 1) * G.minValue) / t := by
    rw [le_div_iff₀ ht, mul_comm]; exact h3
  have h1' : (P.excArcs.card : ℝ) ≤ 2 * P.exc.card := by exact_mod_cast h1
  have h2' : ((P.ret.filter fun p => G.sym.w p.1 p.2 < t).card : ℝ) ≤ q G t := by
    exact_mod_cast h2
  linarith

end

end PruningData

/-! ## The packaged pruning certificate -/

/-- **`lem:prune` package.** The masks (`E`, `ret`), constants (`H` on exceptional pairs) and
queries are chosen from the actual input `G` and held fixed. `toGraph G'` is the induced
competitor graph `H'`; it is dominated by `G'` cutwise, and its degrees, pairs and partial
stars compile to `≤ 3` original queries each. Arbitrary cuts of `H'` are *not* claimed to be
known, nor `H' = H` (except at `G' = G`). -/
structure PruningCert (G : WeightedDiGraph V) where
  O : OrientationCert G
  queries : Finset (Finset V)
  card_queries : queries.card ≤ 30 * Fintype.card V
  O_queries_sub : O.queries ⊆ queries
  /-- Exceptional unordered pairs. -/
  E : Finset (V × V)
  card_E : E.card ≤ 5 * Fintype.card V
  O_E_sub : O.E ⊆ E
  /-- Retained ordinary arcs (prescribed directions). -/
  ret : Finset (V × V)
  ret_not_exc : ∀ u v, (u, v) ∈ ret → ¬ IsExc E u v
  ret_sgn : ∀ u v, (u, v) ∈ ret → O.sgn u v = 1
  ret_rev : ∀ u v, (u, v) ∈ ret → (v, u) ∉ ret
  /-- The implicit graph of the actual input. -/
  H : WeightedDiGraph V
  H_le : ∀ u v, H.c u v ≤ (O.toGraph G).c u v
  H_le_lam : ∀ u v, H.c u v ≤ G.minValue
  lam_le_out : ∀ S, ProperShore S → G.minValue ≤ H.out S
  isGlobalMinCut : ∀ S, IsGlobalMinCut G S → IsGlobalMinCut H S ∧ H.out S = G.minValue
  total_le : total H.c ≤ 2 * (((Fintype.card V : ℝ) - 1) * G.minValue)
  ret_H : ∀ u v, (u, v) ∈ ret → H.c u v = G.sym.w u v
  H_zero : ∀ u v, ¬ IsExc E u v → (u, v) ∉ ret → H.c u v = 0
  exc_w : ∀ G' : WeightedDiGraph V, Consistent G G' queries →
    ∀ u v, IsExc E u v → G'.sym.w u v = G.sym.w u v
  /-- The induced competitor graph `H'`. -/
  toGraph : WeightedDiGraph V → WeightedDiGraph V
  toGraph_c : ∀ G' u v, (toGraph G').c u v =
    if IsExc E u v then H.c u v else if (u, v) ∈ ret then G'.sym.w u v else 0
  toGraph_self : ∀ u v, (toGraph G).c u v = H.c u v
  toGraph_le : ∀ G' : WeightedDiGraph V, Consistent G G' queries →
    ∀ u v, (toGraph G').c u v ≤ (O.toGraph G').c u v
  out_le : ∀ G' : WeightedDiGraph V, Consistent G G' queries →
    ∀ S, (toGraph G').out S ≤ G'.out S
  /-- Restricted compiler. -/
  outStar : ∀ v T, Compiled G (fun G' => ∑ u ∈ T, (toGraph G').c v u)
  outStar_cost : ∀ v T, (outStar v T).cost ≤ 3
  inStar : ∀ v T, Compiled G (fun G' => ∑ u ∈ T, (toGraph G').c u v)
  inStar_cost : ∀ v T, (inStar v T).cost ≤ 3
  symStar : ∀ v T, Compiled G (fun G' => (toGraph G').symStar v T)
  symStar_cost : ∀ v T, (symStar v T).cost ≤ 3
  /-- Explicit formulas: known constant plus one symmetrized partial star of `G'`. -/
  outStar_formula : ∀ v T, ∃ c : ℝ, ∃ T' ⊆ T, ∀ G' : WeightedDiGraph V,
    ∑ u ∈ T, (toGraph G').c v u = c + G'.symStar v T'
  inStar_formula : ∀ v T, ∃ c : ℝ, ∃ T' ⊆ T, ∀ G' : WeightedDiGraph V,
    ∑ u ∈ T, (toGraph G').c u v = c + G'.symStar v T'
  symStar_formula : ∀ v T, ∃ c : ℝ, ∃ T' ⊆ T, ∀ G' : WeightedDiGraph V,
    (toGraph G').symStar v T = c + G'.symStar v T'
  /-- Support bound, for every threshold `t > 0`. -/
  card_supp_le : ∀ t : ℝ, 0 < t →
    ((univ.filter fun p : V × V => 0 < H.c p.1 p.2).card : ℝ) ≤
      10 * Fintype.card V + PruningData.q G t +
        2 * (((Fintype.card V : ℝ) - 1) * G.minValue) / t

namespace PruningData
variable {G : WeightedDiGraph V} (P : PruningData G)

/-- Package pruning data as a certificate. -/
noncomputable def toCert : PruningCert G where
  O := P.O
  queries := P.queries
  card_queries := P.card_queries
  O_queries_sub := subset_union_left
  E := P.exc
  card_E := P.card_exc
  O_E_sub := subset_union_left
  ret := P.ret
  ret_not_exc u v h := (P.mem_ret.1 h).1
  ret_sgn u v h := P.R_sgn (P.mem_ret.1 h)
  ret_rev u v h h' := P.R_rev (P.mem_ret.1 h) (P.mem_ret.1 h')
  H := P.H
  H_le := P.H_le
  H_le_lam := P.H_le_lam
  lam_le_out _ hS := P.lam_le_out_H hS
  isGlobalMinCut _ hS := P.isGlobalMinCut_H hS
  total_le := P.total_H_le
  ret_H u v h := P.R_H (P.mem_ret.1 h)
  H_zero u v hE h := P.H_eq_zero hE fun h' => h (P.mem_ret.2 h')
  exc_w _ hG' _ _ h := P.exc_w hG' h
  toGraph := P.toGraph
  toGraph_c G' u v := by
    rw [P.toGraph_c]
    by_cases h : P.R u v <;> simp [h, P.mem_ret]
  toGraph_self := P.toGraph_self
  toGraph_le _ hG' := P.toGraph_le hG'
  out_le _ hG' := P.out_toGraph_le hG'
  outStar := P.outStarC
  outStar_cost := P.outStarC_cost
  inStar := P.inStarC
  inStar_cost := P.inStarC_cost
  symStar := P.symStarC
  symStar_cost := P.symStarC_cost
  outStar_formula v T := ⟨_, _, filter_subset _ _, fun G' => P.outStar_eq G' v T⟩
  inStar_formula v T := ⟨_, _, filter_subset _ _, fun G' => P.inStar_eq G' v T⟩
  symStar_formula v T := ⟨_, _, union_subset (filter_subset _ _) (filter_subset _ _),
    fun G' => P.symStar_eq G' v T⟩
  card_supp_le t ht := by
    have h := P.card_supp_le ht
    have : (2 * P.exc.card : ℝ) ≤ 10 * Fintype.card V := by
      have := P.card_exc; exact_mod_cast (by omega : 2 * P.exc.card ≤ 10 * Fintype.card V)
    linarith

end PruningData

/-- **`lem:prune`**: every input has a pruning certificate (any root may be used). -/
theorem exists_pruningCert (G : WeightedDiGraph V) [Nonempty V] :
    Nonempty (PruningCert G) := by
  obtain ⟨P⟩ := exists_pruningData G (Classical.arbitrary V)
  exact ⟨P.toCert⟩

namespace PruningCert
variable {G : WeightedDiGraph V} (C : PruningCert G)

/-- `H` has global mincut exactly `λ` (`n ≥ 2`). -/
theorem minValue_H (hn : 2 ≤ Fintype.card V) : C.H.minValue = G.minValue := by
  obtain ⟨S, hS⟩ := exists_isGlobalMinCut G hn
  obtain ⟨h1, h2⟩ := C.isGlobalMinCut S hS
  rw [← h1.out_eq_minValue, h2]

/-- Nonnegativity of the induced graph is built in (`toGraph G'` is a `WeightedDiGraph`). -/
theorem toGraph_nonneg (G' : WeightedDiGraph V) (u v : V) : 0 ≤ (C.toGraph G').c u v :=
  (C.toGraph G').nonneg u v

end PruningCert

end CutQueryComplexity.DirectedCertificate
