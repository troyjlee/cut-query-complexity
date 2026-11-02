import CutQueryComplexity.AllPairs.Recovery
import CutQueryComplexity.Graph.Integral
import Mathlib.Tactic

/-!
# Public bounded row discovery and seed incidences

The row program takes only a vertex, a public candidate set, and integer fuel.
It discovers exactly the smaller of its fuel and the row's positive support.
The same primitive completely exposes a low-degree row or takes a prescribed
number of distinct seed incidences. The hidden graph occurs only in proofs.
-/

set_option autoImplicit false

namespace CutQueryComplexity.CanonicalST

open Finset WeightedGraph
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

def rowPrefix (k : ℕ) : (fuel : ℕ) → V → Finset V →
    DTree (Finset V) ℝ (Finset V) (fuel * ((k + 1) * 3))
  | 0, _, _ => DTree.pure ∅
  | fuel + 1, u, T =>
      ((findNeighbor k u T).bind fun answer => match answer with
        | none => DTree.pure ∅
        | some v => (rowPrefix k fuel u (T.erase v)).map (insert v)).cast (by ring)

theorem rowPrefix_cost (k fuel : ℕ) (u : V) (T : Finset V) (oracle : Finset V → ℝ) :
    (rowPrefix k fuel u T).cost oracle ≤ fuel * ((k + 1) * 3) := DTree.cost_le _ _

/-- Even a non-graph answer sequence returns at most the public fuel many names. -/
theorem rowPrefix_card_le (oracle : Finset V → ℝ) (k fuel : ℕ) (u : V) (T : Finset V) :
    ((rowPrefix k fuel u T).eval oracle).card ≤ fuel := by
  induction fuel generalizing T with
  | zero => simp [rowPrefix]
  | succ fuel ih =>
      simp only [rowPrefix, DTree.eval_cast, DTree.eval_bind]
      cases h : (findNeighbor k u T).eval oracle with
      | none => simp
      | some v =>
          simp only [DTree.eval_map]
          exact (card_insert_le _ _).trans (Nat.add_le_add_right (ih (T.erase v)) 1)

theorem rowPrefix_correct (G : WeightedGraph V) (k : ℕ)
    (hn : Fintype.card V ≤ 2 ^ k) (fuel : ℕ) (u : V) (T : Finset V) :
    (rowPrefix k fuel u T).eval G.cut ⊆ AllPairs.rowSupport G u T ∧
      ((rowPrefix k fuel u T).eval G.cut).card = min fuel (AllPairs.rowSupport G u T).card := by
  induction fuel generalizing T with
  | zero => simp [rowPrefix]
  | succ fuel ih =>
      have hsearch := findNeighbor_correct G k u T hn
      simp only [rowPrefix, DTree.eval_cast, DTree.eval_bind]
      cases hanswer : (findNeighbor k u T).eval G.cut with
      | none =>
          simp only [hanswer, PositiveResult] at hsearch
          have hz : AllPairs.rowSupport G u T = ∅ := by
            apply eq_empty_iff_forall_notMem.mpr
            intro v hv
            obtain ⟨hvT, hpos⟩ := mem_filter.mp hv
            have hzero := hsearch v (mem_univ v)
            simp only [restrictWeight, hvT, ↓reduceIte] at hzero
            linarith
          simp [hz]
      | some v =>
          simp only [hanswer, PositiveResult] at hsearch
          have hv : v ∈ AllPairs.rowSupport G u T :=
            mem_filter.mpr ((restrictWeight_pos (G.w u) T v).mp hsearch.2)
          have hi := ih (T.erase v)
          rw [AllPairs.rowSupport_erase] at hi
          have hnot : v ∉ (rowPrefix k fuel u (T.erase v)).eval G.cut := by
            intro hv'
            exact (mem_erase.mp (hi.1 hv')).1 rfl
          simp only [DTree.eval_map]
          constructor
          · intro x hx
            rcases mem_insert.mp hx with rfl | hx
            · exact hv
            · exact mem_of_mem_erase (hi.1 hx)
          · rw [card_insert_of_notMem hnot, hi.2, card_erase_of_mem hv]
            have hp := card_pos.mpr ⟨v, hv⟩
            omega

theorem rowPrefix_complete (G : WeightedGraph V) (k : ℕ)
    (hn : Fintype.card V ≤ 2 ^ k) (fuel : ℕ) (u : V) (T : Finset V)
    (hsmall : (AllPairs.rowSupport G u T).card ≤ fuel) :
    (rowPrefix k fuel u T).eval G.cut = AllPairs.rowSupport G u T := by
  obtain ⟨hsub, hcard⟩ := rowPrefix_correct G k hn fuel u T
  apply eq_of_subset_of_card_le hsub
  rw [hcard, Nat.min_eq_right hsmall]

theorem rowPrefix_full_card (G : WeightedGraph V) (k : ℕ)
    (hn : Fintype.card V ≤ 2 ^ k) (fuel : ℕ) (u : V) (T : Finset V)
    (hlarge : fuel ≤ (AllPairs.rowSupport G u T).card) :
    ((rowPrefix k fuel u T).eval G.cut).card = fuel := by
  rw [(rowPrefix_correct G k hn fuel u T).2, Nat.min_eq_left hlarge]

omit [Fintype V] [DecidableEq V] in
theorem rowSupport_card_eq_sum (G : WeightedGraph V) (hG : AllPairsAudit.Unweighted G)
    (u : V) (T : Finset V) :
    ((AllPairs.rowSupport G u T).card : ℝ) = ∑ v ∈ T, G.w u v := by
  rw [card_eq_sum_ones, Nat.cast_sum]
  simp only [Nat.cast_one]
  rw [AllPairs.rowSupport, sum_filter]
  apply sum_congr rfl
  intro v _
  rcases hG u v with h | h <;> simp [h]

theorem rowSupport_card_induce_degree (G : WeightedGraph V)
    (hG : AllPairsAudit.Unweighted G) (C : Finset V) {u : V} (hu : u ∈ C) :
    ((AllPairs.rowSupport G u C).card : ℝ) = (G.induce C).degree u := by
  rw [rowSupport_card_eq_sum G hG]
  simp [WeightedGraph.degree, WeightedGraph.induce, hu]

def seedRows (k D : ℕ) : (xs : List V) → Finset V →
    DTree (Finset V) ℝ (Finset (V × V)) (xs.length * D * ((k + 1) * 3))
  | [], _ => DTree.pure ∅
  | u :: xs, C =>
      ((rowPrefix k D u C).bind fun T =>
        (seedRows k D xs C).map fun E => T.image (Prod.mk u) ∪ E).cast (by
          simp only [List.length_cons]
          ring)

theorem seedRows_cost (oracle : Finset V → ℝ) (k D : ℕ) (xs : List V) (C : Finset V) :
    (seedRows k D xs C).cost oracle ≤ xs.length * D * ((k + 1) * 3) :=
  DTree.cost_le _ _

theorem seedRows_eval (oracle : Finset V → ℝ) (k D : ℕ) (xs : List V) (C : Finset V) :
    (seedRows k D xs C).eval oracle =
      xs.toFinset.biUnion (fun u => ((rowPrefix k D u C).eval oracle).image (Prod.mk u)) := by
  induction xs with
  | nil => simp [seedRows]
  | cons u xs ih => simp [seedRows, DTree.eval_bind, ih]

theorem seedRows_card_le (oracle : Finset V → ℝ) (k D : ℕ) (xs : List V) (C : Finset V) :
    ((seedRows k D xs C).eval oracle).card ≤ xs.length * D := by
  rw [seedRows_eval]
  calc
    _ ≤ ∑ u ∈ xs.toFinset, (((rowPrefix k D u C).eval oracle).image (Prod.mk u)).card :=
      card_biUnion_le
    _ ≤ ∑ _u ∈ xs.toFinset, D := sum_le_sum fun u _ =>
      card_image_le.trans (rowPrefix_card_le oracle k D u C)
    _ = xs.toFinset.card * D := by simp
    _ ≤ xs.length * D := Nat.mul_le_mul_right D xs.toFinset_card_le

theorem seedRows_contains_row (oracle : Finset V → ℝ) (k D : ℕ) (xs : List V)
    (C : Finset V) {u v : V} (hu : u ∈ xs) (hv : v ∈ (rowPrefix k D u C).eval oracle) :
    (u, v) ∈ (seedRows k D xs C).eval oracle := by
  rw [seedRows_eval]
  exact mem_biUnion.mpr ⟨u, List.mem_toFinset.mpr hu, mem_image.mpr ⟨v, hv, rfl⟩⟩

theorem seedRows_sound (G : WeightedGraph V) (k D : ℕ)
    (hn : Fintype.card V ≤ 2 ^ k) (xs : List V) (C : Finset V) {u v : V}
    (he : (u, v) ∈ (seedRows k D xs C).eval G.cut) :
    u ∈ xs ∧ v ∈ C ∧ 0 < G.w u v := by
  rw [seedRows_eval] at he
  obtain ⟨a, ha, he⟩ := mem_biUnion.mp he
  obtain ⟨b, hb, he⟩ := mem_image.mp he
  have ha' : a = u := congrArg Prod.fst he
  have hb' : b = v := congrArg Prod.snd he
  subst a b
  exact ⟨List.mem_toFinset.mp ha,
    mem_filter.mp ((rowPrefix_correct G k hn D u C).1 hb)⟩

omit [Fintype V] in
theorem decodeRecovered_unit (E : Finset (V × V)) :
    AllPairsAudit.Unweighted (AllPairs.decodeRecovered E) := by
  intro u v
  simp only [AllPairs.decodeRecovered]
  split_ifs <;> simp

/-- Each listed ordered incidence adds at most one undirected edge. -/
theorem decodeRecovered_mass_le (E : Finset (V × V)) :
    (AllPairs.decodeRecovered E).edgeMass ≤ E.card := by
  have hp (u v : V) : (AllPairs.decodeRecovered E).w u v ≤
      (if (u, v) ∈ E then (1 : ℝ) else 0) + (if (v, u) ∈ E then (1 : ℝ) else 0) := by
    by_cases huv : u = v
    · subst v
      simp only [AllPairs.decodeRecovered, ↓reduceIte]
      split_ifs <;> norm_num
    · by_cases h₁ : (u, v) ∈ E <;> by_cases h₂ : (v, u) ∈ E <;>
        simp [AllPairs.decodeRecovered, huv, h₁, h₂]
  have hm : (∑ u : V, ∑ v : V, if (u, v) ∈ E then (1 : ℝ) else 0) = E.card := by
    rw [← Fintype.sum_prod_type']
    simp
  have hr : (∑ u : V, ∑ v : V, if (v, u) ∈ E then (1 : ℝ) else 0) = E.card := by
    rw [sum_comm]
    exact hm
  have h := sum_le_sum fun u (_ : u ∈ univ) => sum_le_sum fun v (_ : v ∈ univ) => hp u v
  simp only [sum_add_distrib, hm, hr] at h
  unfold WeightedGraph.edgeMass
  linarith

omit [Fintype V] in
theorem decodeRecovered_le (G : WeightedGraph V) (hG : AllPairsAudit.Unweighted G)
    (E : Finset (V × V)) (hE : ∀ u v, (u, v) ∈ E → 0 < G.w u v) :
    (AllPairs.decodeRecovered E).IsSubgraph G := by
  intro u v
  by_cases huv : u = v
  · simp [AllPairs.decodeRecovered, huv, G.diag]
  · by_cases he : (u, v) ∈ E ∨ (v, u) ∈ E
    · have hp : 0 < G.w u v := by
        rcases he with he | he
        · exact hE u v he
        · simpa only [G.symm v u] using hE v u he
      rcases hG u v with hz | ho
      · simp [hz] at hp
      · simp [AllPairs.decodeRecovered, huv, he, ho]
    · simpa [AllPairs.decodeRecovered, huv, he] using G.nonneg u v

theorem decodeRecovered_degree_lower (E : Finset (V × V)) (u : V) (R : Finset V)
    (hno : u ∉ R) (hE : ∀ v ∈ R, (u, v) ∈ E) :
    (R.card : ℝ) ≤ (AllPairs.decodeRecovered E).degree u := by
  calc
    (R.card : ℝ) = ∑ _v ∈ R, (1 : ℝ) := by simp
    _ = ∑ v ∈ R, (AllPairs.decodeRecovered E).w u v := by
      apply sum_congr rfl
      intro v hv
      have huv : u ≠ v := fun h => hno (h.symm ▸ hv)
      simp [AllPairs.decodeRecovered, huv, hE v hv]
    _ ≤ ∑ v : V, (AllPairs.decodeRecovered E).w u v :=
      sum_le_sum_of_subset_of_nonneg (subset_univ R)
        (fun v _ _ => (AllPairs.decodeRecovered E).nonneg u v)

theorem seedRows_subgraph (G : WeightedGraph V) (hG : AllPairsAudit.Unweighted G)
    (k D : ℕ) (hn : Fintype.card V ≤ 2 ^ k) (xs : List V) (C : Finset V) :
    (AllPairs.decodeRecovered ((seedRows k D xs C).eval G.cut)).IsSubgraph G :=
  decodeRecovered_le G hG _ (fun _ _ he => (seedRows_sound G k D hn xs C he).2.2)

theorem seedRows_supported (G : WeightedGraph V) (k D : ℕ)
    (hn : Fintype.card V ≤ 2 ^ k) (xs : List V) (C : Finset V)
    (hxs : ∀ u ∈ xs, u ∈ C) :
    ∀ u v, u ∉ C ∨ v ∉ C →
      (AllPairs.decodeRecovered ((seedRows k D xs C).eval G.cut)).w u v = 0 := by
  intro u v hout
  have hforward : (u, v) ∉ (seedRows k D xs C).eval G.cut := by
    intro he
    obtain ⟨hu, hv, -⟩ := seedRows_sound G k D hn xs C he
    rcases hout with hout | hout
    · exact hout (hxs u hu)
    · exact hout hv
  have hreverse : (v, u) ∉ (seedRows k D xs C).eval G.cut := by
    intro he
    obtain ⟨hv, hu, -⟩ := seedRows_sound G k D hn xs C he
    rcases hout with hout | hout
    · exact hout hu
    · exact hout (hxs v hv)
  simp [AllPairs.decodeRecovered, hforward, hreverse]

theorem seedRows_min_degree (G : WeightedGraph V) (hG : AllPairsAudit.Unweighted G)
    (k D : ℕ) (hn : Fintype.card V ≤ 2 ^ k) (C : Finset V)
    (hdegree : ∀ u ∈ C, (D : ℝ) ≤ (G.induce C).degree u) :
    ∀ u ∈ C, (D : ℝ) ≤
      (AllPairs.decodeRecovered ((seedRows k D C.toList C).eval G.cut)).degree u := by
  intro u hu
  have hcard : D ≤ (AllPairs.rowSupport G u C).card := by
    have h := hdegree u hu
    rw [← rowSupport_card_induce_degree G hG C hu] at h
    exact_mod_cast h
  have he := rowPrefix_full_card G k hn D u C hcard
  have hno : u ∉ (rowPrefix k D u C).eval G.cut := by
    intro h
    have hp := (mem_filter.mp ((rowPrefix_correct G k hn D u C).1 h)).2
    simp only [G.diag, lt_self_iff_false] at hp
  have hd := decodeRecovered_degree_lower
    ((seedRows k D C.toList C).eval G.cut) u ((rowPrefix k D u C).eval G.cut) hno
    (fun v hv => seedRows_contains_row G.cut k D C.toList C (mem_toList.mpr hu) hv)
  simpa only [he] using hd

theorem seedRows_mass_le (oracle : Finset V → ℝ) (k D : ℕ) (C : Finset V) :
    (AllPairs.decodeRecovered ((seedRows k D C.toList C).eval oracle)).edgeMass ≤
      (C.card : ℝ) * D := by
  have hc : (((seedRows k D C.toList C).eval oracle).card : ℝ) ≤ (C.card : ℝ) * D := by
    exact_mod_cast (show ((seedRows k D C.toList C).eval oracle).card ≤ C.card * D from
      by simpa using seedRows_card_le oracle k D C.toList C)
  exact (decodeRecovered_mass_le _).trans hc

end
end CutQueryComplexity.CanonicalST

#print axioms CutQueryComplexity.CanonicalST.rowPrefix_correct
#print axioms CutQueryComplexity.CanonicalST.rowPrefix_cost
#print axioms CutQueryComplexity.CanonicalST.rowPrefix_complete
#print axioms CutQueryComplexity.CanonicalST.rowPrefix_card_le
#print axioms CutQueryComplexity.CanonicalST.seedRows_sound
#print axioms CutQueryComplexity.CanonicalST.seedRows_cost
#print axioms CutQueryComplexity.CanonicalST.seedRows_card_le
#print axioms CutQueryComplexity.CanonicalST.decodeRecovered_mass_le
#print axioms CutQueryComplexity.CanonicalST.decodeRecovered_le
#print axioms CutQueryComplexity.CanonicalST.seedRows_supported
#print axioms CutQueryComplexity.CanonicalST.seedRows_min_degree
#print axioms CutQueryComplexity.CanonicalST.seedRows_mass_le
