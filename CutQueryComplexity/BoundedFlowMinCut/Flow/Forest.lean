import CutQueryComplexity.BoundedFlowMinCut.Flow.Basic

/-! # The sparse residual witness and offline path search (M3)

Let `K_f = usedGraph f` and `H_f = G \ K_f`, and let `T` be a maximal spanning
forest of `H_f` (any number of components). The public relation
`Witness T f u v := T.Adj u v ∨ f u v < 0` uses only `T` and the flow. Its arcs
are residual (`witness_res`), and its reachable sets are closed under residual
arcs (`witness_closed`, Karger–Levine Theorem 3.4), so residual and witness
reachability agree (`witness_reach_iff`).

Hence an augmenting path is found with no query: `witnessPath` picks a simple
witness path (`exists_simple_path`), which is a simple augmenting path
(`witnessPath_some`). If there is none, the witness-reachable set is an exact
minimum `s`–`t` shore of value the flow value (`witness_cut`, `witnessPath_none`).

`loopErase` erases the cycles of an explicit walk; it uses no oracle and no
relation, and keeps a walk along any relation a simple path along it with the
same ends (`loopErase_spec`).
-/

set_option autoImplicit false

namespace CutQueryComplexity.BoundedFlowMinCut
noncomputable section
open scoped Classical
open WeightedGraph Certificate CanonicalST DirectedUnitST.Repair

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The public witness relation: an edge of the maintained forest, or a reverse arc
of the flow. -/
def Witness (T : _root_.SimpleGraph V) (f : V → V → ℝ) (u v : V) : Prop := T.Adj u v ∨ f u v < 0

/-- The unused graph `G \ K_f`. -/
def unusedGraph (G : WeightedGraph V) (f : V → V → ℝ) : WeightedGraph V :=
  G.subtract (Reachability.usedGraph f)

/-- Witness arcs are residual arcs. -/
theorem witness_res {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G) {s t : V} {i : ℝ}
    {f : V → V → ℝ} (hf : Augmentation.FlowSpec G s t i f) {T : _root_.SimpleGraph V}
    (hT : T ≤ (unusedGraph G f).support) {u v : V} (h : Witness T f u v) : Res G f u v := by
  rw [Res, Reachability.residual_iff hG hf]
  rcases h with h | h
  · right
    have hne : (unusedGraph G f).w u v ≠ 0 := hT h
    exact lt_of_le_of_ne ((unusedGraph G f).nonneg u v) (Ne.symm hne)
  · exact Or.inl h

/-- The witness-reachable set is closed under residual arcs (Karger–Levine,
Theorem 3.4): a reverse arc is a witness arc, and an unused edge joins two vertices
of one tree of a maximal forest of the unused graph. -/
theorem witness_closed {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G) {s t : V} {i : ℝ}
    {f : V → V → ℝ} (hf : Augmentation.FlowSpec G s t i f) {T : _root_.SimpleGraph V}
    (hT : IsSpanningForest (unusedGraph G f) T) {a x y : V}
    (hx : Relation.ReflTransGen (Witness T f) a x) (hxy : Res G f x y) :
    Relation.ReflTransGen (Witness T f) a y := by
  rw [Res, Reachability.residual_iff hG hf] at hxy
  rcases hxy with h | h
  · exact hx.tail (Or.inr h)
  · have hadj : (unusedGraph G f).support.Adj x y := ne_of_gt h
    have hreach : T.Reachable x y := hT.2.2 x y hadj.reachable
    rw [_root_.SimpleGraph.reachable_iff_reflTransGen] at hreach
    exact hx.trans (Relation.ReflTransGen.mono (fun _ _ h => Or.inl h) _ _ hreach)

/-- **Exact cut extraction, with no query.** If the target is not witness-reachable,
the witness-reachable set is a minimum `s`–`t` shore whose value is the flow value. -/
theorem witness_cut {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G) {s t : V} {i : ℝ}
    {f : V → V → ℝ} (hf : Augmentation.FlowSpec G s t i f) {T : _root_.SimpleGraph V}
    (hT : IsSpanningForest (unusedGraph G f) T)
    (hno : ¬ Relation.ReflTransGen (Witness T f) s t) :
    let S := Finset.univ.filter (fun v => Relation.ReflTransGen (Witness T f) s v)
    G.cut S = i ∧ IsSTMinCut G s t S := by
  intro S
  have hs : s ∈ S := by simp [S, Relation.ReflTransGen.refl]
  have ht : t ∉ S := by simpa [S] using hno
  have hsat : ∀ u ∈ S, ∀ v ∈ Sᶜ, f u v = G.w u v := by
    intro u hu v hv
    have hu' : Relation.ReflTransGen (Witness T f) s u := by simpa [S] using hu
    have hv' : ¬ Relation.ReflTransGen (Witness T f) s v := by simpa [S] using hv
    have hnres : ¬ Res G f u v := fun h => hv' (witness_closed hG hf hT hu' h)
    exact le_antisymm ((le_abs_self _).trans (hf.1.2 u v)) (not_lt.mp hnres)
  have hcut : G.cut S = i := by
    rw [← hf.cut_flow hs ht]
    exact Finset.sum_congr rfl (fun u hu => Finset.sum_congr rfl (fun v hv => (hsat u hu v hv).symm))
  exact ⟨hcut, hs, ht, fun T' hsT htT => by rw [hcut]; exact hf.value_le_cut hsT htT⟩

omit [Fintype V] in
/-- Reachability along any relation is witnessed by a simple path. -/
theorem exists_simple_path {R : V → V → Prop} {a b : V} (h : Relation.ReflTransGen R a b) :
    ∃ p : List V, ∃ hp : p ≠ [], p.head hp = a ∧ p.getLast hp = b ∧ p.Nodup ∧ p.IsChain R := by
  induction h with
  | refl => exact ⟨[a], List.cons_ne_nil _ _, rfl, rfl, List.nodup_singleton a, List.isChain_singleton a⟩
  | @tail x y _ hxy ih =>
      obtain ⟨p, hp, hh, hl, hnd, hc⟩ := ih
      by_cases hy : y ∈ p
      · refine ⟨p.take (p.idxOf y + 1), ?_, ?_, ?_, hnd.sublist (List.take_sublist _ _),
          hc.take _⟩
        · simp [hp]
        · rw [List.head_take]
          exact hh
        · rw [List.getLast_take]
          simp [List.getElem_idxOf, List.idxOf_lt_length_iff.mpr hy]
      · refine ⟨p ++ [y], by simp, ?_, by simp, ?_, ?_⟩
        · rw [List.head_append_of_ne_nil hp]
          exact hh
        · exact List.nodup_append.mpr ⟨hnd, List.nodup_singleton y,
            fun a ha b hb => by simp only [List.mem_singleton] at hb; exact hb ▸ fun he => hy (he ▸ ha)⟩
        · apply List.IsChain.append hc (List.isChain_singleton y)
          intro u hu v hv
          rw [List.getLast?_eq_some_getLast hp] at hu
          simp only [Option.mem_def, Option.some.injEq, List.head?_cons] at hu hv
          rw [← hu, ← hv, hl]
          exact hxy

/-- Residual reachability and witness reachability agree. -/
theorem witness_reach_iff {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G) {s t : V}
    {i : ℝ} {f : V → V → ℝ} (hf : Augmentation.FlowSpec G s t i f) {T : _root_.SimpleGraph V}
    (hT : IsSpanningForest (unusedGraph G f) T) {a b : V} :
    Relation.ReflTransGen (Res G f) a b ↔ Relation.ReflTransGen (Witness T f) a b := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hxy ih => exact witness_closed hG hf hT ih hxy
  · exact fun h => Relation.ReflTransGen.mono (fun _ _ h => witness_res hG hf hT.1 h) _ _ h

/-- A simple witness path from `s` to `t`, chosen offline from the public forest and
flow; it uses no query. -/
def witnessPath (T : _root_.SimpleGraph V) (f : V → V → ℝ) (s t : V) : Option (List V) :=
  if h : Relation.ReflTransGen (Witness T f) s t then some (Classical.choose (exists_simple_path h))
  else none

/-- A returned witness path is a simple augmenting path. -/
theorem witnessPath_some {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G) {s t : V}
    {i : ℝ} {f : V → V → ℝ} (hf : Augmentation.FlowSpec G s t i f) {T : _root_.SimpleGraph V}
    (hT : T ≤ (unusedGraph G f).support) {π : List V} (h : witnessPath T f s t = some π) :
    IsAugPath G f s t π := by
  by_cases hr : Relation.ReflTransGen (Witness T f) s t
  · rw [witnessPath, dite_eq_left hr, Option.some.injEq] at h
    obtain ⟨hne, hh, hl, hnd, hc⟩ := Classical.choose_spec (exists_simple_path hr)
    subst h
    exact ⟨hne, hh, hl, hnd, hc.imp fun _ _ h => witness_res hG hf hT h⟩
  · rw [witnessPath, dite_eq_right hr] at h
    cases h

/-- With no witness path, the witness-reachable set is a minimum `s`–`t` shore of
value the flow value. -/
theorem witnessPath_none {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G) {s t : V}
    {i : ℝ} {f : V → V → ℝ} (hf : Augmentation.FlowSpec G s t i f) {T : _root_.SimpleGraph V}
    (hT : IsSpanningForest (unusedGraph G f) T) (h : witnessPath T f s t = none) :
    let S := Finset.univ.filter (fun v => Relation.ReflTransGen (Witness T f) s v)
    G.cut S = i ∧ IsSTMinCut G s t S := by
  have hr : ¬ Relation.ReflTransGen (Witness T f) s t := by
    intro hr
    rw [witnessPath, dite_eq_left hr] at h
    cases h
  exact witness_cut hG hf hT hr

end
end CutQueryComplexity.BoundedFlowMinCut

/-! ## Loop erasure (public) -/

namespace CutQueryComplexity.BoundedFlowMinCut
noncomputable section

variable {V : Type} [DecidableEq V]

/-- Append a vertex, cutting back to its first visit if it was seen. -/
def eraseStep (acc : List V) (x : V) : List V :=
  if x ∈ acc then acc.take (acc.idxOf x + 1) else acc ++ [x]

/-- Chronological loop erasure of a walk; it uses no oracle and no relation. -/
def loopErase (W : List V) : List V := W.foldl eraseStep []

theorem eraseStep_spec {R : V → V → Prop} {acc : List V} (hne : acc ≠ []) (hnd : acc.Nodup)
    (hc : acc.IsChain R) {x : V} (hx : R (acc.getLast hne) x) :
    ∃ h : eraseStep acc x ≠ [], (eraseStep acc x).head h = acc.head hne ∧
      (eraseStep acc x).getLast h = x ∧ (eraseStep acc x).Nodup ∧
      (eraseStep acc x).IsChain R ∧ (eraseStep acc x).length ≤ acc.length + 1 := by
  unfold eraseStep
  split_ifs with hmem
  · refine ⟨by simp [hne], ?_, ?_, hnd.sublist (List.take_sublist _ _), hc.take _, ?_⟩
    · rw [List.head_take]
    · rw [List.getLast_take]
      simp [List.getElem_idxOf, List.idxOf_lt_length_iff.mpr hmem]
    · simp only [List.length_take]
      omega
  · refine ⟨by simp, ?_, by simp, ?_, ?_, by simp⟩
    · rw [List.head_append_of_ne_nil hne]
    · exact List.nodup_append.mpr ⟨hnd, List.nodup_singleton x,
        fun a ha b hb => by simp only [List.mem_singleton] at hb; exact hb ▸ fun he => hmem (he ▸ ha)⟩
    · apply List.IsChain.append hc (List.isChain_singleton x)
      intro u hu v hv
      rw [List.getLast?_eq_some_getLast hne] at hu
      simp only [Option.mem_def, Option.some.injEq, List.head?_cons] at hu hv
      rw [← hu, ← hv]
      exact hx

/-- Loop erasure of a walk along `R` is a simple path along `R` with the same ends
and at most as many vertices. -/
theorem loopErase_spec {R : V → V → Prop} : ∀ (W : List V) (hW : W ≠ []), W.IsChain R →
    ∃ h : loopErase W ≠ [], (loopErase W).head h = W.head hW ∧
      (loopErase W).getLast h = W.getLast hW ∧ (loopErase W).Nodup ∧
      (loopErase W).IsChain R ∧ (loopErase W).length ≤ W.length := by
  intro W hW hc
  -- generalize the accumulator
  suffices key : ∀ (acc rest : List V) (hacc : acc ≠ []), acc.Nodup → acc.IsChain R →
      (acc ++ rest).IsChain R →
      ∃ h : rest.foldl eraseStep acc ≠ [], (rest.foldl eraseStep acc).head h = acc.head hacc ∧
        (rest.foldl eraseStep acc).getLast h = (acc ++ rest).getLast (by simp [hacc]) ∧
        (rest.foldl eraseStep acc).Nodup ∧ (rest.foldl eraseStep acc).IsChain R ∧
        (rest.foldl eraseStep acc).length ≤ acc.length + rest.length by
    obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hW
    have h1 := key [x] xs (by simp) (List.nodup_singleton x) (List.isChain_singleton x)
      (by simpa using hc)
    have hfold : loopErase (x :: xs) = xs.foldl eraseStep [x] := by
      simp [loopErase, eraseStep]
    rw [hfold]
    obtain ⟨h, hh, hl, hnd, hch, hlen⟩ := h1
    exact ⟨h, hh, by simpa using hl, hnd, hch, by simpa [Nat.add_comm] using hlen⟩
  intro acc rest
  induction rest generalizing acc with
  | nil =>
      intro hacc hnd hc _
      exact ⟨by simpa using hacc, rfl, by simp, hnd, hc, by simp⟩
  | cons y ys ih =>
      intro hacc hnd hc hall
      have hrel : R (acc.getLast hacc) y := by
        have := (List.isChain_append.mp hall).2.2
        exact this _ (by rw [List.getLast?_eq_some_getLast hacc]; rfl) _ rfl
      obtain ⟨h1, hh1, hl1, hnd1, hc1, hlen1⟩ := eraseStep_spec hacc hnd hc hrel
      have hall' : (eraseStep acc y ++ ys).IsChain R := by
        have hys : (y :: ys).IsChain R := (List.isChain_append.mp hall).2.1
        apply List.IsChain.append hc1 (hys.tail)
        intro u hu v hv
        rw [List.getLast?_eq_some_getLast h1, hl1] at hu
        simp only [Option.mem_def, Option.some.injEq] at hu
        subst hu
        rw [List.isChain_cons] at hys
        exact hys.1 v hv
      obtain ⟨h2, hh2, hl2, hnd2, hc2, hlen2⟩ := ih (eraseStep acc y) h1 hnd1 hc1 hall'
      refine ⟨h2, hh2.trans hh1, ?_, hnd2, hc2, ?_⟩
      · show (List.foldl eraseStep (eraseStep acc y) ys).getLast h2 = _
        rw [hl2]
        cases ys with
        | nil => simp [hl1]
        | cons z zs => simp [List.getLast_append_of_ne_nil]
      · simp only [List.foldl_cons, List.length_cons]
        omega

end
end CutQueryComplexity.BoundedFlowMinCut
