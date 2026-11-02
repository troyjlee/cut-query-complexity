import CutQueryComplexity.TwoRespecting.Respect

/-! # A rooted spanning tree inside a spanning edge set

An edge set `E` (ordered pairs, read as undirected) *spans* `V` if every proper
shore is crossed by an edge of `E`. Breadth-first layers from a root give a rooted
spanning tree `bfsTree` whose tree edges all belong to `E`. Hence a shore crosses
no more tree edges than edges of `E` (`card_crossedEdges_le`).
-/

namespace CutQueryComplexity
namespace TwoRespecting

open RootedTree

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The pair `e` has its endpoints on different sides of `S`. -/
def CrossesPair (S : Finset V) (e : V × V) : Prop :=
  (e.1 ∈ S ∧ e.2 ∉ S) ∨ (e.2 ∈ S ∧ e.1 ∉ S)

instance (S : Finset V) : DecidablePred (CrossesPair S) := fun _ => by
  unfold CrossesPair; infer_instance

/-- Number of pairs of `E` crossing `S`. -/
def crossCount (E : Finset (V × V)) (S : Finset V) : ℕ := (E.filter (CrossesPair S)).card

/-- Every proper shore is crossed by some pair of `E`. -/
def Spans (E : Finset (V × V)) : Prop :=
  ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ → ∃ e ∈ E, CrossesPair S e

/-- `a` and `b` are joined by a pair of `E`. -/
def EAdj (E : Finset (V × V)) (a b : V) : Prop := (a, b) ∈ E ∨ (b, a) ∈ E

instance (E : Finset (V × V)) (a b : V) : Decidable (EAdj E a b) := by
  unfold EAdj; infer_instance

/-- Breadth-first layers from `r`. -/
def reach (E : Finset (V × V)) (r : V) : ℕ → Finset V
  | 0 => {r}
  | k + 1 => reach E r k ∪ Finset.univ.filter fun v => ∃ u ∈ reach E r k, EAdj E u v

variable {E : Finset (V × V)} {r : V}

theorem reach_mono {k m : ℕ} (h : k ≤ m) : reach E r k ⊆ reach E r m := by
  induction m with
  | zero => rw [Nat.le_zero.mp h]
  | succ m ih =>
      rcases Nat.lt_or_ge k (m + 1) with hk | hk
      · exact (ih (by omega)).trans Finset.subset_union_left
      · rw [le_antisymm h hk]

theorem card_reach (hE : Spans E) : ∀ k, min (k + 1) (Fintype.card V) ≤ (reach E r k).card
  | 0 => by simp [reach]
  | k + 1 => by
      have ih := card_reach hE k
      by_cases hall : reach E r k = Finset.univ
      · have : reach E r (k + 1) = Finset.univ :=
          Finset.eq_univ_of_forall fun v => reach_mono (Nat.le_succ k) (hall ▸ Finset.mem_univ v)
        rw [this, Finset.card_univ]; omega
      · have hne : (reach E r k).Nonempty := ⟨r, reach_mono (Nat.zero_le k) (by simp [reach])⟩
        obtain ⟨e, he, hcross⟩ := hE _ hne hall
        -- the crossing pair adds a new vertex to the next layer
        obtain ⟨v, hvnew, hvnext⟩ : ∃ v, v ∉ reach E r k ∧ v ∈ reach E r (k + 1) := by
          rcases hcross with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact ⟨e.2, h2, Finset.mem_union_right _
              (Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.1, h1, Or.inl he⟩)⟩
          · exact ⟨e.1, h2, Finset.mem_union_right _
              (Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.2, h1, Or.inr he⟩)⟩
        have hss : reach E r k ⊂ reach E r (k + 1) :=
          Finset.ssubset_iff_subset_ne.mpr ⟨reach_mono (Nat.le_succ k),
            fun h => hvnew (h ▸ hvnext)⟩
        have := Finset.card_lt_card hss
        omega

theorem exists_mem_reach (hE : Spans E) (v : V) : ∃ k, v ∈ reach E r k := by
  refine ⟨Fintype.card V, ?_⟩
  have h := card_reach (r := r) hE (Fintype.card V)
  have : reach E r (Fintype.card V) = Finset.univ :=
    Finset.eq_univ_of_card _ (le_antisymm (Finset.card_le_univ _) (by omega))
  rw [this]; exact Finset.mem_univ v

open Classical in
/-- Breadth-first depth. -/
noncomputable def bfsDepth (r : V) (hE : Spans E) (v : V) : ℕ :=
  Nat.find (exists_mem_reach (r := r) hE v)

theorem mem_reach_bfsDepth (hE : Spans E) (v : V) : v ∈ reach E r (bfsDepth r hE v) := by
  classical
  exact Nat.find_spec (exists_mem_reach (r := r) hE v)

theorem bfsDepth_le (hE : Spans E) {v : V} {k : ℕ} (h : v ∈ reach E r k) :
    bfsDepth r hE v ≤ k := by
  classical
  exact Nat.find_min' _ h

theorem bfsDepth_eq_zero_iff (hE : Spans E) {v : V} : bfsDepth r hE v = 0 ↔ v = r := by
  constructor
  · intro h
    have := mem_reach_bfsDepth (r := r) hE v
    rw [h] at this
    simpa [reach] using this
  · rintro rfl
    exact Nat.le_zero.mp (bfsDepth_le hE (by simp [reach]))

theorem exists_bfsParent (hE : Spans E) {v : V} (hv : v ≠ r) :
    ∃ u, EAdj E u v ∧ bfsDepth r hE u + 1 = bfsDepth r hE v := by
  have hpos : bfsDepth r hE v ≠ 0 := fun h => hv ((bfsDepth_eq_zero_iff hE).mp h)
  obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero hpos
  have hmem := mem_reach_bfsDepth (r := r) hE v
  rw [hd] at hmem
  have hnot : v ∉ reach E r d := fun h => by
    have := bfsDepth_le (r := r) hE h; omega
  rcases Finset.mem_union.mp hmem with h | h
  · exact absurd h hnot
  · obtain ⟨-, u, hu, hadj⟩ := Finset.mem_filter.mp h
    refine ⟨u, hadj, ?_⟩
    have hle := bfsDepth_le (r := r) hE hu
    by_contra hne
    have hlt : bfsDepth r hE u + 1 ≤ d := by omega
    have : v ∈ reach E r (bfsDepth r hE u + 1) :=
      Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, u,
        mem_reach_bfsDepth (r := r) hE u, hadj⟩)
    exact hnot (reach_mono hlt this)

open Classical in
/-- Breadth-first parent. -/
noncomputable def bfsParent (r : V) (hE : Spans E) (v : V) : V :=
  if hv : v = r then r else Classical.choose (exists_bfsParent hE hv)

/-- The breadth-first rooted spanning tree of a spanning edge set. -/
noncomputable def bfsTree (E : Finset (V × V)) (r : V) (hE : Spans E) : RootedTree V where
  root := r
  parent := bfsParent r hE
  depth := bfsDepth r hE
  parent_root := by simp [bfsParent]
  depth_root := (bfsDepth_eq_zero_iff hE).mpr rfl
  depth_parent v hv := by
    rw [bfsParent, dite_eq_right_of_eq_false (eq_false hv)]
    exact (Classical.choose_spec (exists_bfsParent hE hv)).2

theorem bfsTree_adj (hE : Spans E) {v : V} (hv : v ≠ (bfsTree E r hE).root) :
    EAdj E ((bfsTree E r hE).parent v) v := by
  change v ≠ r at hv
  change EAdj E (bfsParent r hE v) v
  rw [bfsParent, dite_eq_right_of_eq_false (eq_false hv)]
  exact (Classical.choose_spec (exists_bfsParent hE hv)).1

/-- A shore crosses no more tree edges of `bfsTree` than pairs of `E`. -/
theorem card_crossedEdges_le [LinearOrder V] (hE : Spans E) (S : Finset V) :
    ((bfsTree E r hE).crossedEdges S).card ≤ crossCount E S := by
  set T := bfsTree E r hE
  classical
  let g : V → V × V := fun v => if (T.parent v, v) ∈ E then (T.parent v, v) else (v, T.parent v)
  unfold crossCount
  apply Finset.card_le_card_of_injOn g
  · intro v hv
    rw [Finset.mem_coe, mem_crossedEdges] at hv
    have hadj := bfsTree_adj hE hv.1
    rw [Finset.mem_coe, Finset.mem_filter]
    simp only [g]
    split_ifs with h
    · refine ⟨h, ?_⟩
      unfold CrossesPair; simp only; tauto
    · refine ⟨hadj.resolve_left h, ?_⟩
      unfold CrossesPair; simp only; tauto
  · intro v hv w hw hvw
    rw [Finset.mem_coe, mem_crossedEdges] at hv hw
    have hdv := T.depth_parent v hv.1
    have hdw := T.depth_parent w hw.1
    simp only [g] at hvw
    split_ifs at hvw with h1 h2 h2 <;> simp only [Prod.mk.injEq] at hvw
    · exact hvw.2
    · exfalso
      have e1 := congrArg T.depth hvw.1
      have e2 := congrArg T.depth hvw.2
      omega
    · exfalso
      have e1 := congrArg T.depth hvw.1
      have e2 := congrArg T.depth hvw.2
      omega
    · exact hvw.1

end TwoRespecting
end CutQueryComplexity
