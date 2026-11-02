import CutQueryComplexity.GHReduction.FrontierRoundState
import CutQueryComplexity.GHReduction.FrontierCutSafety

/-! # Correct auxiliary outputs pass the public refinement guards

The original vertices of a block are in bijection with the terminal labels
actually given to its auxiliary source-pivot program. This transfers trace
cardinalities, orientation and disjointness to the lifted public split. Hence
guarding cannot discard a well-formed output. Existing branch witnesses then
lift its accepted minimum shores and queried values to the original graph.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical
open WeightedGraph

variable {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]

theorem frontierMap_mem_terminals (p : V → B) (T : RootedTree B) (b : B)
    {v : V} (hv : v ∈ fiber p b) : frontierMap p T b v ∈ frontierTerminals p T b := by
  apply (mem_frontierTerminals p T b _).mpr
  exact ⟨⟨v, hv⟩, ((frontierMap_eq_inl p T b v ⟨v, hv⟩).mpr rfl).symm⟩

theorem frontierMap_injective_on_fiber (p : V → B) (T : RootedTree B) (b : B)
    {v w : V} (hv : v ∈ fiber p b) (hw : w ∈ fiber p b)
    (he : frontierMap p T b v = frontierMap p T b w) : v = w := by
  rw [(frontierMap_eq_inl p T b v ⟨v, hv⟩).mpr rfl,
    (frontierMap_eq_inl p T b w ⟨w, hw⟩).mpr rfl] at he
  exact congrArg Subtype.val (Sum.inl.inj he)

/-- The half-size test is about the number of original terminals, not about
proxy labels or the sizes of the proxy fibers. -/
theorem frontier_terminal_trace_card (p : V → B) (T : RootedTree B) (b : B)
    (S : Finset (FrontierVertex p T b)) :
    (pull (frontierMap p T b) S ∩ fiber p b).card = (S ∩ frontierTerminals p T b).card := by
  apply Finset.card_bij (fun v _ => frontierMap p T b v)
  · intro v hv
    exact Finset.mem_inter.mpr ⟨(mem_pull _ _ _).mp (Finset.mem_inter.mp hv).1,
      frontierMap_mem_terminals p T b (Finset.mem_inter.mp hv).2⟩
  · intro v hv w hw he
    exact frontierMap_injective_on_fiber p T b (Finset.mem_inter.mp hv).2
      (Finset.mem_inter.mp hw).2 he
  · intro z hz
    obtain ⟨u, hu⟩ := (mem_frontierTerminals p T b z).mp (Finset.mem_inter.mp hz).2
    have hmap : frontierMap p T b u.val = z :=
      ((frontierMap_eq_inl p T b u.val u).mpr rfl).trans hu
    refine ⟨u.val, Finset.mem_inter.mpr ⟨?_, u.property⟩, hmap⟩
    exact (mem_pull _ _ _).mpr (hmap.symm ▸ (Finset.mem_inter.mp hz).1)

theorem liftFrontierSplit_valid (p : V → B) (T : RootedTree B) (b : B) (r : V)
    {levels : ℕ} (out : SourcePivotOutput (FrontierVertex p T b) levels)
    (hpivot : out.pivot ∈ frontierTerminals p T b)
    (hform : OuterPivot.WellFormed (frontierTerminals p T b) out.pivot out.values out.step.batch) :
    ValidBlockSplit (fiber p b) (liftFrontierSplit p T b r (some out)) := by
  obtain ⟨s, hs⟩ := (mem_frontierTerminals p T b out.pivot).mp hpivot
  have hpiv : out.pivot = Sum.inl s := hs.symm
  let S := liftFrontierSplit p T b r (some out)
  have hsource : S.source = s.val := by simp only [S, liftFrontierSplit, hpiv]
  have hmapS : frontierMap p T b s.val = out.pivot :=
    ((frontierMap_eq_inl p T b s.val s).mpr rfl).trans hs
  have hchild {v : V} (hv : v ∈ S.children) :
      v ∈ fiber p b ∧ frontierMap p T b v ∈ out.step.batch.accepted := Finset.mem_filter.mp hv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change S.source ∈ fiber p b
    rw [hsource]
    exact s.property
  · intro v hv
    refine Finset.mem_erase.mpr ⟨?_, (hchild hv).1⟩
    intro he
    apply (Finset.mem_erase.mp (hform.indices (hchild hv).2)).1
    rw [he, hsource, hmapS]
  · intro v hv
    exact (mem_pull _ _ _).mpr (hform.contains _ (hchild hv).2)
  · intro v hv
    change S.source ∉ pull (frontierMap p T b) (out.step.batch.shore (frontierMap p T b v))
    rw [mem_pull, hsource, hmapS]
    exact hform.excludes _ (hchild hv).2
  · intro v hv
    change 2 * (pull (frontierMap p T b)
      (out.step.batch.shore (frontierMap p T b v)) ∩ fiber p b).card ≤ (fiber p b).card
    rw [frontier_terminal_trace_card, ← frontierTerminals_card p T b]
    exact hform.small _ (hchild hv).2
  · intro v hv w hw hvw
    apply Finset.disjoint_left.mpr
    intro x hxv hxw
    have hne : frontierMap p T b v ≠ frontierMap p T b w :=
      fun he => hvw (frontierMap_injective_on_fiber p T b (hchild hv).1 (hchild hw).1 he)
    exact Finset.disjoint_left.mp (hform.disjoint (hchild hv).2 (hchild hw).2 hne)
      ((mem_pull _ _ _).mp hxv) ((mem_pull _ _ _).mp hxw)

theorem checkedFrontierSplit_of_wellFormed (p : V → B) (hp : Function.Surjective p)
    (T : RootedTree B) (b : B) {levels : ℕ}
    (out : SourcePivotOutput (FrontierVertex p T b) levels)
    (hpivot : out.pivot ∈ frontierTerminals p T b)
    (hform : OuterPivot.WellFormed (frontierTerminals p T b) out.pivot out.values out.step.batch) :
    checkedFrontierSplit p hp T b (some out) =
      liftFrontierSplit p T b (blockRepresentative p hp b) (some out) :=
  normalizeBlockSplit_of_valid _ _ _ (liftFrontierSplit_valid p T b _ out hpivot hform)

/-- The local solver's actual queried values and shores lift to the original
graph once the old proxy branches have their minimum-cut witnesses. -/
theorem checkedFrontierSplit_minCuts (G : WeightedGraph V) (p : V → B)
    (hp : Function.Surjective p) (T : RootedTree B) (b : B)
    (r c : frontierProxies T b → V)
    (hbranch : ∀ e, IsSTMinCut G (r e) (c e) (pull p (frontierBranch T b e)))
    {levels : ℕ} (out : SourcePivotOutput (FrontierVertex p T b) levels)
    (hgood : SourcePivotGood (G.contract (frontierMap p T b)) (frontierTerminals p T b) out) :
    ∀ v ∈ (checkedFrontierSplit p hp T b (some out)).children,
      IsSTMinCut G v (checkedFrontierSplit p hp T b (some out)).source
        ((checkedFrontierSplit p hp T b (some out)).shore v) ∧
      (checkedFrontierSplit p hp T b (some out)).value v =
        G.cut ((checkedFrontierSplit p hp T b (some out)).shore v) := by
  simp only [checkedFrontierSplit_of_wellFormed p hp T b out hgood.1 hgood.2.2.1]
  obtain ⟨s, hs⟩ := (mem_frontierTerminals p T b out.pivot).mp hgood.1
  have hpiv : out.pivot = Sum.inl s := hs.symm
  intro v hv
  have hchild : v ∈ fiber p b ∧ frontierMap p T b v ∈ out.step.batch.accepted :=
    Finset.mem_filter.mp hv
  let u : fiber p b := ⟨v, hchild.1⟩
  have hmap : frontierMap p T b v = Sum.inl u := (frontierMap_eq_inl p T b v u).mpr rfl
  have hcut := hgood.2.2.2 (frontierMap p T b v) hchild.2
  have haux : IsSTMinCut (G.contract (frontierMap p T b)) (Sum.inl u) (Sum.inl s)
      (out.step.batch.shore (frontierMap p T b v)) := by
    simpa only [hmap, hpiv] using hcut.1
  have hlift := frontier_minCut_lift G p T b r c hbranch haux
  refine ⟨?_, ?_⟩
  · simpa only [liftFrontierSplit, hpiv, u] using hlift
  · exact hcut.2.trans (cut_contract G (frontierMap p T b) _)

end
end CutQueryComplexity.GHReduction
