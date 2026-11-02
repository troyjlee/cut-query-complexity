import CutQueryComplexity.SupportForest.Rectangle
import CutQueryComplexity.SupportForest.Support
import CutQueryComplexity.DetMinCut.Normalize

/-! # One round of the forest routine, the invariant and the potential

The state is a representative map `r` whose fibers are the current components, the set `done`
of representatives whose fiber has been tested and has cut zero, and the forest edges learned
so far, each stored with its weight. The invariant `Inv` says that `r` is idempotent, that
vertices with the same representative are joined in the support, that finished fibers have
cut zero and are represented by their own representative, that every stored edge is a positive
edge with its exact weight, that the stored edges form a forest, and that two vertices have the
same representative exactly when the stored edges connect them.

One round (`testRound st x₀`) tests the fiber `A` of the representative `c = r x₀`, which must be
unfinished. If `cut A = 0`, `c` is marked finished. Otherwise the inside search returns `u ∈ A`
with `cross {u} Aᶜ > 0`, one query gives the degree of `u`, the outside search returns `v ∉ A`
with `w u v > 0`, the class of `v` is merged into the class of `u`, and the edge `(u, v, w u v)`
is recorded. The potential `Φ = #fibers + #unfinished fibers` drops by at least one per round,
and the cost accounting `cost + Φ' + K N' ≤ Φ + K N` with `K = 4 ⌈log₂ n⌉ + 1` and `N` the
number of fibers charges each merge to the fiber it removes.

The loop `loop fuel st` repeats the round on the least unfinished vertex until all
representatives are finished; `loop_spec` proves that fuel `Φ st` suffices.
-/

namespace CutQueryComplexity
namespace SupportForest

open WeightedGraph Search Search.Comp Finset DetMinCut

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## State, stored forest, fibers -/

/-- The state of the forest routine. -/
structure St (V : Type) where
  r : V → V
  done : Finset V
  edges : List (V × V × ℝ)

/-- The simple graph of a list of weighted edges. -/
def edgeGraph : List (V × V × ℝ) → SimpleGraph V
  | [] => ⊥
  | e :: L => edgeGraph L ⊔ SimpleGraph.edge e.1 e.2.1

omit [Fintype V] [DecidableEq V] in
@[simp] theorem edgeGraph_nil : edgeGraph ([] : List (V × V × ℝ)) = ⊥ := rfl

omit [Fintype V] [DecidableEq V] in
@[simp] theorem edgeGraph_cons (e : V × V × ℝ) (L : List (V × V × ℝ)) :
    edgeGraph (e :: L) = edgeGraph L ⊔ SimpleGraph.edge e.1 e.2.1 := rfl

omit [Fintype V] [DecidableEq V] in
/-- A list of positive edges spans a subgraph of the support. -/
theorem edgeGraph_le_support (G : WeightedGraph V) :
    ∀ L : List (V × V × ℝ), (∀ e ∈ L, 0 < G.w e.1 e.2.1) → edgeGraph L ≤ G.support
  | [], _ => bot_le
  | e :: L, h =>
      sup_le (edgeGraph_le_support G L fun e' he' => h e' (List.mem_cons_of_mem _ he'))
        ((SimpleGraph.edge_le_iff _).mpr (Or.inr ((support_adj_iff G _ _).mpr (h e (by simp)))))

/-- The vertices represented by `c`. -/
def classOf (r : V → V) (c : V) : Finset V := univ.filter fun x => r x = c

@[simp] theorem mem_classOf (r : V → V) (c x : V) : x ∈ classOf r c ↔ r x = c := by
  simp [classOf]

/-- The invariant of the forest routine. -/
structure Inv (G : WeightedGraph V) (st : St V) : Prop where
  idem : ∀ x, st.r (st.r x) = st.r x
  fiber_le : ∀ u v, st.r u = st.r v → G.support.Reachable u v
  done_zero : ∀ c ∈ st.done, G.cut (classOf st.r c) = 0
  done_rep : ∀ c ∈ st.done, st.r c = c
  edges_ok : ∀ e ∈ st.edges, 0 < G.w e.1 e.2.1 ∧ e.2.2 = G.w e.1 e.2.1
  acyclic : (edgeGraph st.edges).IsAcyclic
  spanning : ∀ u v, st.r u = st.r v ↔ (edgeGraph st.edges).Reachable u v

/-- The number of fibers. -/
def N (st : St V) : ℕ := (univ.image st.r).card

/-- The potential: fibers plus unfinished fibers. -/
def Φ (st : St V) : ℕ := N st + (univ.image st.r \ st.done).card

/-- The charge per fiber in the cost accounting. -/
def K (V : Type) [Fintype V] : ℕ := 4 * Nat.clog 2 (Fintype.card V) + 1

/-! ## One round -/

variable [LinearOrder V]

/-- One round on the fiber of the representative of `x₀`. -/
noncomputable def testRound (st : St V) (x₀ : V) : Comp (Finset V) ℝ (St V) :=
  (ask (classOf st.r (st.r x₀))).bind fun m =>
    if 0 < m then
      (insideSearch x₀ (classOf st.r (st.r x₀)) m).bind fun p =>
        (ask {p.1}).bind fun d =>
          (outsideSearch x₀ p.1 d (classOf st.r (st.r x₀))ᶜ p.2).bind fun q =>
            Comp.pure ⟨mergeR st.r (st.r q.1) (st.r p.1), st.done, (p.1, q.1, q.2) :: st.edges⟩
    else Comp.pure ⟨st.r, insert (st.r x₀) st.done, st.edges⟩

omit [LinearOrder V] in
/-- A finished fiber has no positive edge leaving it. -/
theorem notMem_done_of_edge {G : WeightedGraph V} {st : St V} (hI : Inv G st) {u v : V}
    (huv : 0 < G.w u v) (hne : st.r u ≠ st.r v) : st.r v ∉ st.done := by
  intro hv
  have hz := hI.done_zero _ hv
  have hmem : v ∈ classOf st.r (st.r v) := by simp
  have hadj : G.support.Adj v u := (support_adj_iff G v u).mpr (G.symm u v ▸ huv)
  have := adj_mem_of_cut_zero G _ hz hmem hadj
  rw [mem_classOf] at this
  exact hne this

omit [LinearOrder V] in
/-- Merging the class of `v` into the class of `u` along a positive edge `u v` between distinct
classes preserves the invariant. -/
theorem inv_merge (G : WeightedGraph V) {st : St V} (hI : Inv G st) {u v : V}
    (huv : 0 < G.w u v) (hne : st.r u ≠ st.r v) :
    Inv G ⟨mergeR st.r (st.r v) (st.r u), st.done, (u, v, G.w u v) :: st.edges⟩ := by
  have hvd : st.r v ∉ st.done := notMem_done_of_edge hI huv hne
  have hud : st.r u ∉ st.done := notMem_done_of_edge hI (G.symm u v ▸ huv) hne.symm
  have huv' : u ≠ v := fun h => hne (h ▸ rfl)
  -- the merged map on the two classes
  have hr' : ∀ x, mergeR st.r (st.r v) (st.r u) x = if st.r x = st.r v then st.r u else st.r x :=
    fun x => rfl
  have hr'u : mergeR st.r (st.r v) (st.r u) u = st.r u := by
    rw [hr', ite_eq_right hne]
  have hr'v : mergeR st.r (st.r v) (st.r u) v = st.r u := by
    rw [hr', ite_eq_left rfl]
  have hnr : ¬ (edgeGraph st.edges).Reachable u v := fun h => hne ((hI.spanning u v).mpr h)
  have hadj : (edgeGraph st.edges ⊔ SimpleGraph.edge u v).Adj u v := by
    rw [SimpleGraph.sup_adj, SimpleGraph.edge_adj]
    exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, huv'⟩
  -- same new representative implies joined in the support
  have hjoin : ∀ x y, mergeR st.r (st.r v) (st.r u) x = mergeR st.r (st.r v) (st.r u) y →
      (edgeGraph st.edges ⊔ SimpleGraph.edge u v).Reachable x y := by
    intro x y hxy
    rw [hr', hr'] at hxy
    have hF : ∀ a b, st.r a = st.r b →
        (edgeGraph st.edges ⊔ SimpleGraph.edge u v).Reachable a b :=
      fun a b h => ((hI.spanning a b).mp h).mono le_sup_left
    by_cases hx : st.r x = st.r v <;> by_cases hy : st.r y = st.r v <;>
      simp only [hx, hy, ite_true, ite_false] at hxy
    · exact hF x y (hx.trans hy.symm)
    · exact ((hF x v hx).trans hadj.symm.reachable).trans (hF u y hxy)
    · exact ((hF x u hxy).trans hadj.reachable).trans (hF v y hy.symm)
    · exact hF x y hxy
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simp only [hr']
    by_cases hx : st.r x = st.r v
    · simp [hx, hI.idem]
    · simp [hx, hI.idem]
  · intro x y hxy
    refine (hjoin x y hxy).mono (sup_le (edgeGraph_le_support G _ fun e he => (hI.edges_ok e he).1) ?_)
    exact (SimpleGraph.edge_le_iff _).mpr (Or.inr ((support_adj_iff G _ _).mpr huv))
  · intro c hc
    have hcv : c ≠ st.r v := fun h => hvd (h ▸ hc)
    have hcu : c ≠ st.r u := fun h => hud (h ▸ hc)
    show G.cut (univ.filter fun x => mergeR st.r (st.r v) (st.r u) x = c) = 0
    rw [filter_mergeR_ne hcv hcu]
    exact hI.done_zero c hc
  · intro c hc
    have hcv : c ≠ st.r v := fun h => hvd (h ▸ hc)
    show (if st.r c = st.r v then st.r u else st.r c) = c
    rw [hI.done_rep c hc, ite_eq_right hcv]
  · intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨huv, rfl⟩
    · exact hI.edges_ok e he
  · exact hI.acyclic.sup_edge_of_not_reachable hnr
  · intro x y
    refine ⟨hjoin x y, fun h => ?_⟩
    have hclosed : ∀ a ∈ (univ.filter fun z => mergeR st.r (st.r v) (st.r u) z =
        mergeR st.r (st.r v) (st.r u) x), ∀ b,
        (edgeGraph st.edges ⊔ SimpleGraph.edge u v).Adj a b →
        b ∈ (univ.filter fun z => mergeR st.r (st.r v) (st.r u) z =
          mergeR st.r (st.r v) (st.r u) x) := by
      intro a ha b hab
      rw [mem_filter] at ha ⊢
      refine ⟨mem_univ _, ?_⟩
      rw [← ha.2]
      rw [SimpleGraph.sup_adj] at hab
      rcases hab with hab | hab
      · exact (mergeR_of_eq ((hI.spanning a b).mpr hab.reachable)).symm
      · rw [SimpleGraph.edge_adj] at hab
        rcases hab.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [hr'u, hr'v]
        · rw [hr'u, hr'v]
    have := reachable_mem_of_closed _ _ hclosed (by simp) h
    rw [mem_filter] at this
    exact this.2.symm

omit [LinearOrder V] in
/-- Marking an unfinished fiber of cut zero as finished preserves the invariant. -/
theorem inv_finish (G : WeightedGraph V) {st : St V} (hI : Inv G st) (x₀ : V)
    (h0 : G.cut (classOf st.r (st.r x₀)) = 0) :
    Inv G ⟨st.r, insert (st.r x₀) st.done, st.edges⟩ := by
  refine ⟨hI.idem, hI.fiber_le, ?_, ?_, hI.edges_ok, hI.acyclic, hI.spanning⟩
  · intro c hc
    rcases mem_insert.mp hc with rfl | hc
    · exact h0
    · exact hI.done_zero c hc
  · intro c hc
    rcases mem_insert.mp hc with rfl | hc
    · exact hI.idem x₀
    · exact hI.done_rep c hc

omit [LinearOrder V] in
theorem N_pos_of_nonempty [Nonempty V] (st : St V) : 1 ≤ N st :=
  Finset.card_pos.mpr (univ_nonempty.image st.r)

/-- One round on an unfinished representative preserves the invariant, lowers the potential,
and obeys the cost accounting `cost + Φ' + K N' ≤ Φ + K N`. -/
theorem round_spec (G : WeightedGraph V) {st : St V} (hI : Inv G st) (x₀ : V)
    (hx₀ : st.r x₀ ∉ st.done) :
    Inv G ((testRound st x₀).eval G.cut) ∧
    Φ ((testRound st x₀).eval G.cut) + 1 ≤ Φ st ∧
    (testRound st x₀).cost G.cut + Φ ((testRound st x₀).eval G.cut) + K V * N ((testRound st x₀).eval G.cut) ≤
      Φ st + K V * N st := by
  set c := st.r x₀ with hc
  set A := classOf st.r c with hA
  have hcimg : c ∈ univ.image st.r := mem_image_of_mem _ (mem_univ x₀)
  have hcU : c ∈ univ.image st.r \ st.done := mem_sdiff.mpr ⟨hcimg, hx₀⟩
  by_cases hpos : 0 < G.cut A
  · -- the merging round
    simp only [testRound, eval_bind, cost_bind, eval_ask, cost_ask, ← hc, ← hA, hpos, ↓reduceIte]
    obtain ⟨hu, hcross, hp2, hcin⟩ := insideSearch_spec G x₀ A hpos
    set p := (insideSearch x₀ A (G.cut A)).eval G.cut
    rw [cut_singleton, hp2]
    obtain ⟨hv, hw, hq2, hcout⟩ := outsideSearch_spec G x₀ p.1 Aᶜ hcross
    set q := (outsideSearch x₀ p.1 (G.degree p.1) Aᶜ (G.cross {p.1} Aᶜ)).eval G.cut
    simp only [eval_pure, cost_pure, add_zero]
    rw [mem_classOf] at hu
    rw [mem_compl, mem_classOf] at hv
    have hne : st.r p.1 ≠ st.r q.1 := by rw [hu]; exact Ne.symm hv
    have hI' := inv_merge G hI hw hne
    rw [hq2]
    -- the potential and the cost
    have hvimg : st.r q.1 ∈ univ.image st.r := mem_image_of_mem _ (mem_univ _)
    have huimg : st.r p.1 ∈ univ.image st.r := mem_image_of_mem _ (mem_univ _)
    have hvd : st.r q.1 ∉ st.done := notMem_done_of_edge hI hw hne
    have himg : univ.image (mergeR st.r (st.r q.1) (st.r p.1)) =
        (univ.image st.r).erase (st.r q.1) := image_mergeR hvimg huimg hne.symm
    have hN : N ⟨mergeR st.r (st.r q.1) (st.r p.1), st.done, (p.1, q.1, G.w p.1 q.1) :: st.edges⟩ + 1 =
        N st := by
      simp only [N, himg]
      rw [card_erase_of_mem hvimg]
      have := card_pos.mpr ⟨_, hvimg⟩
      omega
    have hU : (univ.image (mergeR st.r (st.r q.1) (st.r p.1)) \ st.done).card + 1 =
        (univ.image st.r \ st.done).card := by
      rw [himg, erase_sdiff_comm, card_erase_of_mem (mem_sdiff.mpr ⟨hvimg, hvd⟩)]
      have := card_pos.mpr ⟨_, mem_sdiff.mpr ⟨hvimg, hvd⟩⟩
      omega
    have hΦ : Φ ⟨mergeR st.r (st.r q.1) (st.r p.1), st.done, (p.1, q.1, G.w p.1 q.1) :: st.edges⟩ + 2 =
        Φ st := by
      simp only [Φ]; omega
    have hAn : Nat.clog 2 A.card ≤ Nat.clog 2 (Fintype.card V) :=
      Nat.clog_mono_right 2 (card_le_univ A)
    have hAcn : Nat.clog 2 Aᶜ.card ≤ Nat.clog 2 (Fintype.card V) :=
      Nat.clog_mono_right 2 (card_le_univ Aᶜ)
    refine ⟨hI', by omega, ?_⟩
    rw [← hN, Nat.mul_succ]
    simp only [K]
    omega
  · -- the finishing round
    have h0 : G.cut A = 0 := le_antisymm (not_lt.mp hpos) (G.cut_nonneg A)
    simp only [testRound, eval_bind, cost_bind, eval_ask, cost_ask, ← hc, ← hA, hpos, ↓reduceIte,
      eval_pure, cost_pure, add_zero]
    refine ⟨inv_finish G hI x₀ h0, ?_, ?_⟩ <;>
    · have hU : (univ.image st.r \ insert c st.done).card + 1 = (univ.image st.r \ st.done).card := by
        rw [sdiff_insert, card_erase_of_mem hcU]
        have := card_pos.mpr ⟨_, hcU⟩
        omega
      simp only [Φ, N]
      omega

/-! ## The loop -/

/-- The vertices whose representative is unfinished. -/
def unfinished (st : St V) : Finset V := univ.filter fun x => st.r x ∉ st.done

/-- The loop: repeat the round on the least unfinished vertex. -/
noncomputable def loop : ℕ → St V → Comp (Finset V) ℝ (St V)
  | 0, st => Comp.pure st
  | fuel + 1, st =>
    if h : (unfinished st).Nonempty then (testRound st ((unfinished st).min' h)).bind (loop fuel)
    else Comp.pure st

/-- With fuel at least the potential, the loop keeps the invariant, finishes every
representative, and obeys the cost accounting. -/
theorem loop_spec (G : WeightedGraph V) :
    ∀ (fuel : ℕ) (st : St V), Inv G st → Φ st ≤ fuel →
      Inv G ((loop fuel st).eval G.cut) ∧
      (∀ x, ((loop fuel st).eval G.cut).r x ∈ ((loop fuel st).eval G.cut).done) ∧
      (loop fuel st).cost G.cut + Φ ((loop fuel st).eval G.cut) +
          K V * N ((loop fuel st).eval G.cut) ≤ Φ st + K V * N st := by
  intro fuel
  induction fuel with
  | zero =>
      intro st hI hΦ
      simp only [loop, eval_pure, cost_pure, zero_add]
      refine ⟨hI, fun x => ?_, le_rfl⟩
      exfalso
      have hN : N st = 0 := by simp only [Φ] at hΦ; omega
      have : univ.image st.r = ∅ := card_eq_zero.mp hN
      have hx : st.r x ∈ univ.image st.r := mem_image_of_mem _ (mem_univ x)
      rw [this] at hx
      exact notMem_empty _ hx
  | succ fuel ih =>
      intro st hI hΦ
      by_cases h : (unfinished st).Nonempty
      · simp only [loop, dite_eq_left h, eval_bind, cost_bind]
        have hx₀ : st.r ((unfinished st).min' h) ∉ st.done := by
          have := min'_mem _ h
          simpa [unfinished] using this
        obtain ⟨hI₁, hΦ₁, hcost₁⟩ := round_spec G hI _ hx₀
        obtain ⟨hI₂, hdone₂, hcost₂⟩ := ih _ hI₁ (by omega)
        exact ⟨hI₂, hdone₂, by omega⟩
      · simp only [loop, dite_eq_right h, eval_pure, cost_pure, zero_add]
        refine ⟨hI, fun x => ?_, le_rfl⟩
        rw [not_nonempty_iff_eq_empty, unfinished, filter_eq_empty_iff] at h
        by_contra hx
        exact h (mem_univ x) hx

end SupportForest
end CutQueryComplexity
