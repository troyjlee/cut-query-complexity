import CutQueryComplexity.BoundedFlowMinCut.Flow.Forest
import CutQueryComplexity.GHReduction.Programs
import CutQueryComplexity.Primitive.Forest

/-! # Repairing the maintained forest after an augmentation (M5)

Let `T` be a spanning forest of the unused graph `H_f = G \ K_f`, and let `π` be
the simple augmenting path. The new unused graph `H_{f'}` is the intermediate
graph `M = G \ (K_f ∪ E(π))` plus the path edges whose flow was cancelled.

* `T \ E(π)` is a forest inside `M`. An edge of `M` that it does not span joins
  two of its components, and the old tree path between its ends crosses a
  removed edge; so the component of its first end holds a vertex of `π`
  (`rootsCover_init`).
* `repairRoots` runs one crossing-edge search per vertex of `π`, on that
  vertex's current component in `M`; the cut oracle of `M` is `G.cut - X.cut`
  for the explicit `X = K_f ∪ E(π)` (`subtractAnswers`, no extra query). A
  search that finds an edge merges two components and hands the duty of the
  first to a root beyond the edge; a failed search proves the component is
  closed. After all roots, the forest spans `M` (`repairRoots_spec`).
* `reinsert` adds the cancelled path edges that join different components, with
  no query (`reinsert_spec`), and `M ∪ cancelled = H_{f'}`
  (`support_unused_augment`).

The cost is `|π|` crossing-edge searches, `6 (⌈log₂ n⌉ + 1)` queries each.
-/

set_option autoImplicit false

namespace CutQueryComplexity.BoundedFlowMinCut
noncomputable section
open scoped Classical
open WeightedGraph Certificate CanonicalST DirectedUnitST.Repair GHReduction

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Answers of a subtracted graph -/

/-- Run a program against `G \ X` for an explicit `X ≤ G`: the answer `a` to the
cut query `A` is replaced by `a - X.cut A`. Same queries, same count. -/
def subtractAnswers (X : WeightedGraph V) {O : Type} : Prog (Finset V) ℝ O → Prog (Finset V) ℝ O
  | .pure o => .pure o
  | .query A next => .query A (fun a => subtractAnswers X (next (a - X.cut A)))

theorem subtractAnswers_run (X : WeightedGraph V) {O : Type} (p : Prog (Finset V) ℝ O)
    (read : Finset V → ℝ) :
    Prog.run read (subtractAnswers X p) = Prog.run (fun A => read A - X.cut A) p := by
  induction p with
  | pure o => rfl
  | query A next ih => simp [subtractAnswers, ih]

theorem subtractAnswers_eval {G X : WeightedGraph V} (hX : ∀ u v, X.w u v ≤ G.w u v) {O : Type}
    (p : Prog (Finset V) ℝ O) :
    Prog.eval G.cut (subtractAnswers X p) = Prog.eval (G.subtract X).cut p := by
  have h : (fun A => G.cut A - X.cut A) = (G.subtract X).cut :=
    funext fun A => (cut_subtract G X hX A).symm
  simp only [Prog.eval, subtractAnswers_run, h]

theorem subtractAnswers_cost (X : WeightedGraph V) {O : Type} (p : Prog (Finset V) ℝ O)
    (read : Finset V → ℝ) :
    Prog.cost read (subtractAnswers X p) = Prog.cost (fun A => read A - X.cut A) p := by
  simp only [Prog.cost, subtractAnswers_run]

/-! ### Spanning a simple graph -/

/-- `F` is a spanning forest of the simple graph `S`. -/
def Spans (S F : _root_.SimpleGraph V) : Prop :=
  F ≤ S ∧ F.IsAcyclic ∧ ∀ x y, S.Adj x y → F.Reachable x y

omit [Fintype V] [DecidableEq V] in
theorem isSpanningForest_iff_spans (H : WeightedGraph V) (F : _root_.SimpleGraph V) :
    IsSpanningForest H F ↔ Spans H.support F := by
  constructor
  · exact fun ⟨h1, h2, h3⟩ => ⟨h1, h2, fun x y h => h3 x y h.reachable⟩
  · intro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun x y h => ?_⟩
    rw [_root_.SimpleGraph.reachable_iff_reflTransGen] at h ⊢
    exact Relation.ReflTransGen.lift' id (fun a b hab => by
      have := h3 a b hab
      rwa [_root_.SimpleGraph.reachable_iff_reflTransGen] at this) _ _ h

omit [Fintype V] [DecidableEq V] in
/-- Adding an edge to the graph: add it to the forest unless its ends are joined. -/
theorem spans_sup_edge {S F : _root_.SimpleGraph V} (h : Spans S F) (x y : V) :
    Spans (S ⊔ _root_.SimpleGraph.edge x y)
      (if F.Reachable x y then F else F ⊔ _root_.SimpleGraph.edge x y) := by
  obtain ⟨hsub, hacyc, hreach⟩ := h
  have hedge : ∀ a b, (_root_.SimpleGraph.edge x y).Adj a b → (a = x ∧ b = y) ∨ (a = y ∧ b = x) :=
    fun a b hab => ((_root_.SimpleGraph.edge_adj _ _ _ _).mp hab).1
  split_ifs with hxy
  · refine ⟨hsub.trans le_sup_left, hacyc, fun a b hab => ?_⟩
    rcases (_root_.SimpleGraph.sup_adj _ _ _ _).mp hab with hab | hab
    · exact hreach a b hab
    · rcases hedge a b hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hxy
      · exact hxy.symm
  · refine ⟨sup_le_sup_right hsub _, hacyc.sup_edge_of_not_reachable hxy, fun a b hab => ?_⟩
    rcases (_root_.SimpleGraph.sup_adj _ _ _ _).mp hab with hab | hab
    · exact (hreach a b hab).mono le_sup_left
    · exact ((_root_.SimpleGraph.sup_adj _ _ _ _).mpr (Or.inr hab)).reachable

/-! ### The path's edges and the intermediate graph -/

/-- The undirected edges of a vertex list. -/
def pathGraph (π : List V) : _root_.SimpleGraph V := _root_.SimpleGraph.fromRel (Consec π)

/-- `K ∪ E(π)` as a unit graph: a union of indicator graphs, not their sum. -/
def pathUnion (K : WeightedGraph V) (π : List V) : WeightedGraph V where
  w u v := if (pathGraph π).Adj u v then 1 else K.w u v
  symm u v := by
    by_cases h : (pathGraph π).Adj u v
    · simp [h, h.symm]
    · have h' : ¬ (pathGraph π).Adj v u := fun h' => h h'.symm
      simp [h, h', K.symm u v]
  nonneg u v := by by_cases h : (pathGraph π).Adj u v <;> simp [h, K.nonneg u v]
  diag v := by simp [K.diag]

/-! ### Repair from roots -/

/-- One crossing-edge search per root, on the root's current component, against
the supplied cut oracle; a found edge is added to the forest. -/
def repairRoots : List V → _root_.SimpleGraph V → Prog (Finset V) ℝ (_root_.SimpleGraph V)
  | [], F => .pure F
  | r :: rest, F =>
      (liftDTree (findCross (searchDepth V) (forestBlock F r) (forestBlock F r)ᶜ)).bind
        fun ans => match ans with
          | none => repairRoots rest F
          | some (u, v) => repairRoots rest (F ⊔ _root_.SimpleGraph.edge u v)

theorem repairRoots_cost_le (read : Finset V → ℝ) : ∀ (D : List V) (F : _root_.SimpleGraph V),
    Prog.cost read (repairRoots D F) ≤ D.length * (6 * (searchDepth V + 1))
  | [], F => by simp [repairRoots]
  | r :: rest, F => by
      have h1 := liftDTree_cost_le
        (findCross (searchDepth V) (forestBlock F r) (forestBlock F r)ᶜ) read
      have hmul : (rest.length + 1) * (6 * (searchDepth V + 1)) =
          rest.length * (6 * (searchDepth V + 1)) + 6 * (searchDepth V + 1) := Nat.succ_mul _ _
      rw [repairRoots, Prog.cost_bind, List.length_cons, hmul]
      cases Prog.eval read
        (liftDTree (findCross (searchDepth V) (forestBlock F r) (forestBlock F r)ᶜ)) with
      | none =>
          have := repairRoots_cost_le read rest F
          dsimp only
          omega
      | some e =>
          rcases e with ⟨u, v⟩
          have := repairRoots_cost_le read rest (F ⊔ _root_.SimpleGraph.edge u v)
          dsimp only
          omega

/-- Every edge of `S` that `F` does not span leaves a component holding a root. -/
def RootsCover (S F : _root_.SimpleGraph V) (D : List V) : Prop :=
  ∀ x y, S.Adj x y → ¬ F.Reachable x y → ∃ z ∈ D, F.Reachable x z

/-- **Repair.** On the oracle of `M`, a forest inside `M` whose unspanned edges are
covered by the roots is completed to a spanning forest of `M`. -/
theorem repairRoots_spec (M : WeightedGraph V) : ∀ (D : List V) (F : _root_.SimpleGraph V),
    F ≤ M.support → F.IsAcyclic → RootsCover M.support F D →
    Spans M.support (Prog.eval M.cut (repairRoots D F))
  | [], F, hsub, hacyc, hcov => by
      rw [repairRoots, Prog.eval_pure]
      refine ⟨hsub, hacyc, fun x y hxy => ?_⟩
      by_contra h
      obtain ⟨z, hz, -⟩ := hcov x y hxy h
      simp at hz
  | r :: rest, F, hsub, hacyc, hcov => by
      set B := forestBlock F r with hB
      have hsearch := findCross_logarithmic M (S := B) (T := Bᶜ) disjoint_compl_right
      rw [repairRoots, Prog.eval_bind, liftDTree_eval]
      cases he : (findCross (searchDepth V) B Bᶜ).eval M.cut with
      | none =>
          have hz : M.cross B Bᶜ = 0 := by simpa [he, CrossResult] using hsearch
          have hclosed : ∀ x ∈ B, ∀ y, M.support.Adj x y → y ∈ B := by
            intro x hx y hxy
            by_contra hy
            have h1 := (Finset.sum_eq_zero_iff_of_nonneg
              (fun a _ => Finset.sum_nonneg (fun b _ => M.nonneg a b))).mp hz x hx
            exact hxy ((Finset.sum_eq_zero_iff_of_nonneg (fun b _ => M.nonneg x b)).mp h1 y
              (Finset.mem_compl.mpr hy))
          apply repairRoots_spec M rest F hsub hacyc
          intro x y hxy hnr
          obtain ⟨z, hz, hxz⟩ := hcov x y hxy hnr
          rcases List.mem_cons.mp hz with rfl | hz
          · exfalso
            have hx : x ∈ B := (mem_forestBlock _ _ _).mpr hxz.symm
            have hy := hclosed x hx y hxy
            exact hnr (((mem_forestBlock _ _ _).mp hx).symm.trans ((mem_forestBlock _ _ _).mp hy))
          · exact ⟨z, hz, hxz⟩
      | some e =>
          rcases e with ⟨u, v⟩
          have hp : u ∈ B ∧ v ∈ Bᶜ ∧ 0 < M.w u v := by simpa [he, CrossResult] using hsearch
          have hnr : ¬F.Reachable u v :=
            not_reachable_across_block F r hp.1 (Finset.mem_compl.mp hp.2.1)
          have hne : u ≠ v := fun h => hnr (h ▸ _root_.SimpleGraph.Reachable.refl u)
          have hadj : M.support.Adj u v := ne_of_gt hp.2.2
          have hsub' : F ⊔ _root_.SimpleGraph.edge u v ≤ M.support :=
            sup_le hsub ((_root_.SimpleGraph.edge_le_iff M.support).mpr (Or.inr hadj))
          have hle : F ≤ F ⊔ _root_.SimpleGraph.edge u v := le_sup_left
          have huv : (F ⊔ _root_.SimpleGraph.edge u v).Adj u v := by
            rw [_root_.SimpleGraph.sup_adj, _root_.SimpleGraph.edge_adj]
            exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, hne⟩
          apply repairRoots_spec M rest _ hsub' (hacyc.sup_edge_of_not_reachable hnr)
          intro x y hxy hnr'
          have hnrF : ¬F.Reachable x y := fun h => hnr' (h.mono hle)
          obtain ⟨z, hz, hxz⟩ := hcov x y hxy hnrF
          rcases List.mem_cons.mp hz with rfl | hz
          · -- `x` is in the searched component: hand over to a root beyond the edge
            obtain ⟨z', hz', hvz'⟩ := hcov v u hadj.symm (fun h => hnr h.symm)
            rcases List.mem_cons.mp hz' with rfl | hz'
            · exact absurd ((mem_forestBlock _ _ _).mpr hvz'.symm) (Finset.mem_compl.mp hp.2.1)
            · refine ⟨z', hz', ?_⟩
              have hzu : F.Reachable z u := (mem_forestBlock _ _ _).mp hp.1
              exact ((hxz.trans hzu).mono hle).trans (huv.reachable.trans (hvz'.mono hle))
          · exact ⟨z, hz, hxz.mono hle⟩

omit [Fintype V] [DecidableEq V] in
/-- Deleting the path's edges from a forest that spans `S`: every unspanned edge of
`S` leaves a component holding a vertex of the path. -/
theorem rootsCover_init {S T : _root_.SimpleGraph V} (hspan : ∀ x y, S.Adj x y → T.Reachable x y)
    (π : List V) : RootsCover S (T \ pathGraph π) π := by
  intro x y hxy hnr
  have hT := hspan x y hxy
  rw [_root_.SimpleGraph.reachable_iff_reflTransGen] at hT
  suffices key : ∀ b, Relation.ReflTransGen T.Adj x b →
      (T \ pathGraph π).Reachable x b ∨ ∃ a ∈ π, (T \ pathGraph π).Reachable x a by
    rcases key y hT with h | h
    · exact absurd h hnr
    · exact h
  intro b hb
  induction hb with
  | refl => exact Or.inl (_root_.SimpleGraph.Reachable.refl _)
  | @tail b c _ hbc ih =>
      rcases ih with h | h
      · by_cases hp : (pathGraph π).Adj b c
        · right
          rw [pathGraph, _root_.SimpleGraph.fromRel_adj] at hp
          rcases hp.2 with h' | h'
          · exact ⟨b, (consec_mem h').1, h⟩
          · exact ⟨b, (consec_mem h').2, h⟩
        · left
          exact h.trans ((_root_.SimpleGraph.sdiff_adj _ _ _ _).mpr ⟨hbc, hp⟩).reachable
      · exact Or.inr h

/-! ### Reinserting cancelled edges -/

/-- The path edges whose new flow is zero. -/
def cancelEdges (g : V → V → ℝ) : List V → _root_.SimpleGraph V
  | x :: y :: rest =>
      (if g x y = 0 then _root_.SimpleGraph.edge x y else ⊥) ⊔ cancelEdges g (y :: rest)
  | _ => ⊥

/-- Add each path edge of zero new flow unless its ends are already joined; no query. -/
def reinsert (g : V → V → ℝ) : List V → _root_.SimpleGraph V → _root_.SimpleGraph V
  | x :: y :: rest, F =>
      reinsert g (y :: rest)
        (if g x y = 0 then (if F.Reachable x y then F else F ⊔ _root_.SimpleGraph.edge x y) else F)
  | _, F => F

omit [Fintype V] [DecidableEq V] in
theorem reinsert_spec (g : V → V → ℝ) : ∀ (π : List V) (S F : _root_.SimpleGraph V),
    Spans S F → Spans (S ⊔ cancelEdges g π) (reinsert g π F)
  | x :: y :: rest, S, F, h => by
      rw [reinsert, cancelEdges, ← sup_assoc]
      apply reinsert_spec g (y :: rest)
      by_cases hg : g x y = 0
      · rw [ite_eq_left hg, ite_eq_left hg]
        exact spans_sup_edge h x y
      · rw [ite_eq_right hg, ite_eq_right hg, sup_bot_eq]
        exact h
  | [], S, F, h => by simpa [reinsert, cancelEdges] using h
  | [_], S, F, h => by simpa [reinsert, cancelEdges] using h

omit [Fintype V] [DecidableEq V] in
theorem cancelEdges_adj {g : V → V → ℝ} (hanti : ∀ u v, g v u = -g u v) :
    ∀ (π : List V) (a b : V),
      (cancelEdges g π).Adj a b ↔ a ≠ b ∧ (Consec π a b ∨ Consec π b a) ∧ g a b = 0
  | x :: y :: rest, a, b => by
      have ih := cancelEdges_adj hanti (y :: rest) a b
      have hyx : g y x = 0 ↔ g x y = 0 := by rw [hanti x y]; exact neg_eq_zero
      rw [cancelEdges, _root_.SimpleGraph.sup_adj, ih]
      simp only [Consec]
      by_cases hg : g x y = 0
      · rw [ite_eq_left hg, _root_.SimpleGraph.edge_adj]
        constructor
        · rintro (⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, hne⟩ | ⟨hne, hc, h0⟩)
          · exact ⟨hne, Or.inl (Or.inl ⟨rfl, rfl⟩), hg⟩
          · exact ⟨hne, Or.inr (Or.inl ⟨rfl, rfl⟩), hyx.mpr hg⟩
          · exact ⟨hne, hc.imp Or.inr Or.inr, h0⟩
        · rintro ⟨hne, (⟨rfl, rfl⟩ | hc) | (⟨rfl, rfl⟩ | hc), h0⟩
          · exact Or.inl ⟨Or.inl ⟨rfl, rfl⟩, hne⟩
          · exact Or.inr ⟨hne, Or.inl hc, h0⟩
          · exact Or.inl ⟨Or.inr ⟨rfl, rfl⟩, hne⟩
          · exact Or.inr ⟨hne, Or.inr hc, h0⟩
      · rw [ite_eq_right hg, _root_.SimpleGraph.bot_adj, false_or]
        constructor
        · rintro ⟨hne, hc, h0⟩
          exact ⟨hne, hc.imp Or.inr Or.inr, h0⟩
        · rintro ⟨hne, (⟨rfl, rfl⟩ | hc) | (⟨rfl, rfl⟩ | hc), h0⟩
          · exact absurd h0 hg
          · exact ⟨hne, Or.inl hc, h0⟩
          · exact absurd (hyx.mp h0) hg
          · exact ⟨hne, Or.inr hc, h0⟩
  | [], a, b => by simp [cancelEdges, Consec]
  | [_], a, b => by simp [cancelEdges, Consec]

/-! ### The repair program -/

/-- **Forest repair.** Delete the path's edges from `T`, complete the forest in
`G \ (K_f ∪ E(π))` with one crossing-edge search per path vertex (on the
subtracted oracle), then reinsert the cancelled path edges with no query. -/
def repairForest (T : _root_.SimpleGraph V) (f : V → V → ℝ) (π : List V) :
    Prog (Finset V) ℝ (_root_.SimpleGraph V) :=
  (subtractAnswers (pathUnion (Reachability.usedGraph f) π)
    (repairRoots π (T \ pathGraph π))).map (reinsert (fun u v => f u v + pathFlow π u v) π)

/-- On every oracle, the repair costs `|π|` crossing-edge searches. -/
theorem repairForest_cost_le (T : _root_.SimpleGraph V) (f : V → V → ℝ) (π : List V)
    (read : Finset V → ℝ) :
    Prog.cost read (repairForest T f π) ≤ π.length * (6 * (searchDepth V + 1)) := by
  rw [repairForest, Prog.cost_map, subtractAnswers_cost]
  exact repairRoots_cost_le _ π _

/-- A path edge is an edge of `G`. -/
theorem path_edge_weight {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G) {s t : V}
    {i : ℝ} {f : V → V → ℝ} (hf : Augmentation.FlowSpec G s t i f) {π : List V}
    (hπ : IsAugPath G f s t π) {a b : V} (h : (pathGraph π).Adj a b) : G.w a b = 1 := by
  have hres : ∀ {u v : V}, Res G f u v → G.w u v = 1 := by
    intro u v huv
    rcases hG u v with h0 | h1
    · have : |f u v| ≤ 0 := h0 ▸ hf.1.2 u v
      have : f u v = 0 := abs_nonpos_iff.mp this
      unfold Res at huv
      linarith
    · exact h1
  rw [pathGraph, _root_.SimpleGraph.fromRel_adj] at h
  rcases h.2 with hc | hc
  · exact hres (consec_rel hπ.chain hc)
  · rw [G.symm]
    exact hres (consec_rel hπ.chain hc)

/-- The intermediate graph `M = G \ (K_f ∪ E(π))`: no path edge, and the unused
graph elsewhere. -/
theorem subtract_pathUnion_w {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G) {s t : V}
    {i : ℝ} {f : V → V → ℝ} (hf : Augmentation.FlowSpec G s t i f) {π : List V}
    (hπ : IsAugPath G f s t π) (a b : V) :
    (G.subtract (pathUnion (Reachability.usedGraph f) π)).w a b =
      if (pathGraph π).Adj a b then 0 else (unusedGraph G f).w a b := by
  by_cases h : (pathGraph π).Adj a b
  · rw [ite_eq_left h]
    change max 0 (G.w a b - (if (pathGraph π).Adj a b then 1 else _)) = 0
    rw [ite_eq_left h, path_edge_weight hG hf hπ h]
    norm_num
  · rw [ite_eq_right h]
    change max 0 (G.w a b - (if (pathGraph π).Adj a b then 1 else _)) = _
    rw [ite_eq_right h]
    rfl

/-- `G \ K_{f'} = M ∪ (cancelled path edges)`. -/
theorem support_unused_augment {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G) {s t : V}
    {i : ℝ} {f : V → V → ℝ} (hf : Augmentation.FlowSpec G s t i f) {π : List V}
    (hπ : IsAugPath G f s t π) :
    (unusedGraph G (fun u v => f u v + pathFlow π u v)).support =
      (G.subtract (pathUnion (Reachability.usedGraph f) π)).support ⊔
        cancelEdges (fun u v => f u v + pathFlow π u v) π := by
  have hf' := augment_flowSpec hG hf hπ
  have hanti : ∀ u v, f v u + pathFlow π v u = -(f u v + pathFlow π u v) := by
    intro u v
    rw [hf.1.1 u v, (pathFlow_isFlow π) u v]
    ring
  ext a b
  rw [_root_.SimpleGraph.sup_adj, cancelEdges_adj hanti]
  change (G.subtract (Reachability.usedGraph _)).w a b ≠ 0 ↔
    (G.subtract (pathUnion (Reachability.usedGraph f) π)).w a b ≠ 0 ∨ _
  rw [subtract_pathUnion_w hG hf hπ]
  change max 0 (G.w a b - (Reachability.usedGraph _).w a b) ≠ 0 ↔
    (if (pathGraph π).Adj a b then 0 else max 0 (G.w a b - (Reachability.usedGraph f).w a b)) ≠ 0 ∨ _
  rw [Reachability.usedGraph_weight hG hf', Reachability.usedGraph_weight hG hf]
  have hP : (pathGraph π).Adj a b ↔ a ≠ b ∧ (Consec π a b ∨ Consec π b a) := by
    rw [pathGraph, _root_.SimpleGraph.fromRel_adj]
  by_cases h : (pathGraph π).Adj a b
  · rw [ite_eq_left h, path_edge_weight hG hf hπ h]
    have hp := hP.mp h
    rcases hf'.unit_values hG a b with h1 | h1 | h1 <;> simp [h1, hp.1, hp.2]
  · rw [ite_eq_right h]
    have hzero : pathFlow π a b = 0 := by
      rw [pathFlow_eq hπ.nodup]
      by_cases hab : a = b
      · subst hab; ring
      · have hn := fun hc => h (hP.mpr ⟨hab, hc⟩)
        rw [ite_eq_right (fun hc => hn (Or.inl hc)), ite_eq_right (fun hc => hn (Or.inr hc))]
        ring
    rw [hzero, add_zero]
    constructor
    · exact Or.inl
    · rintro (h1 | ⟨hne, hc, -⟩)
      · exact h1
      · exact absurd (hP.mpr ⟨hne, hc⟩) h

/-- **Forest repair.** If `T` is a spanning forest of `G \ K_f` and `π` is a simple
augmenting path, the repaired forest is a spanning forest of `G \ K_{f'}` for the
augmented flow `f' = f + pathFlow π`. -/
theorem repairForest_spec {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G) {s t : V}
    {i : ℝ} {f : V → V → ℝ} (hf : Augmentation.FlowSpec G s t i f) {T : _root_.SimpleGraph V}
    (hT : IsSpanningForest (unusedGraph G f) T) {π : List V} (hπ : IsAugPath G f s t π) :
    IsSpanningForest (unusedGraph G (fun u v => f u v + pathFlow π u v))
      (Prog.eval G.cut (repairForest T f π)) := by
  set X := pathUnion (Reachability.usedGraph f) π
  set M := G.subtract X
  have hK := Reachability.usedGraph_le hG hf
  have hX : ∀ u v, X.w u v ≤ G.w u v := by
    intro u v
    change (if (pathGraph π).Adj u v then 1 else _) ≤ _
    split_ifs with h
    · rw [path_edge_weight hG hf hπ h]
    · exact hK u v
  have hM : ∀ a b, M.w a b = if (pathGraph π).Adj a b then 0 else (unusedGraph G f).w a b :=
    subtract_pathUnion_w hG hf hπ
  rw [repairForest, Prog.eval_map, subtractAnswers_eval hX, isSpanningForest_iff_spans,
    support_unused_augment hG hf hπ]
  apply reinsert_spec
  apply repairRoots_spec M π
  · intro a b hab
    rw [_root_.SimpleGraph.sdiff_adj] at hab
    change M.w a b ≠ 0
    rw [hM, ite_eq_right hab.2]
    exact hT.1 hab.1
  · exact hT.2.1.anti sdiff_le
  · apply rootsCover_init
    intro x y hxy
    have hxy' : M.w x y ≠ 0 := hxy
    rw [hM] at hxy'
    by_cases h : (pathGraph π).Adj x y
    · exact absurd (ite_eq_left h) hxy'
    · rw [ite_eq_right h] at hxy'
      exact hT.2.2 x y (_root_.SimpleGraph.Adj.reachable hxy')

end
end CutQueryComplexity.BoundedFlowMinCut
