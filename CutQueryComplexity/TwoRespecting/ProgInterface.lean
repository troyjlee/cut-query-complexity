import CutQueryComplexity.TwoRespecting.TreeCover
import CutQueryComplexity.MinCut.RootedTree
import CutQueryComplexity.Model.Prog

/-! # The deterministic two-respecting search on `Prog` and `RootedTree`

This module states the two-respecting search of `TwoRespecting.Main` in the form used
by `MinCut/Weighted`: a `Prog` program on `CutQueryComplexity.RootedTree`, returning a
value together with a shore.

* `Search.Comp.toProg` turns a `Comp` program into a `Prog` program with the same
  output and the same number of queries on every oracle.
* `RootedTree.toTwoRespecting` reads a `CutQueryComplexity.RootedTree` as the
  structurally identical `TwoRespecting.RootedTree`; `crossSet` corresponds to
  `crossedEdges`.
* `twoRespectingProg T` needs only `[Fintype V]`; equality and a linear order on `V`
  are chosen classically, which is free since offline choices are not charged.

Main results: `twoRespectingProg_correct`, `twoRespectingProg_isSome`, and
`twoRespectingProg_cost` (at most `72 n (⌈log₂ n⌉ + 1)` queries on every oracle).
-/

namespace CutQueryComplexity

/-! ### From `Comp` to `Prog` -/

namespace Search.Comp

variable {Q A β : Type}

/-- The same program in the `Prog` monad. -/
def toProg : Comp Q A β → Prog Q A β
  | pure b => Prog.pure b
  | query q k => Prog.query q fun a => toProg (k a)

theorem run_toProg (o : Q → A) (c : Comp Q A β) : Prog.run o c.toProg = c.run o := by
  induction c with
  | pure b => rfl
  | query q k ih => simp [toProg, Comp.run, ih]

@[simp] theorem eval_toProg (o : Q → A) (c : Comp Q A β) : Prog.eval o c.toProg = c.eval o := by
  simp [Prog.eval, Comp.eval, run_toProg]

@[simp] theorem cost_toProg (o : Q → A) (c : Comp Q A β) : Prog.cost o c.toProg = c.cost o := by
  simp [Prog.cost, Comp.cost, run_toProg]

end Search.Comp

/-! ### Reading a `RootedTree` as a `TwoRespecting.RootedTree` -/

/-- The structurally identical tree of the two-respecting development. -/
def RootedTree.toTwoRespecting {V : Type} (T : RootedTree V) : TwoRespecting.RootedTree V :=
  ⟨T.root, T.parent, T.depth, T.parent_root, T.depth_root, T.depth_parent⟩

namespace TwoRespecting

open Search Search.Comp

variable {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]

omit [LinearOrder V] in
theorem mem_crossSet_iff (T : CutQueryComplexity.RootedTree V) (S : Finset V) (v : V) :
    v ∈ T.crossSet S ↔ v ∈ T.toTwoRespecting.crossedEdges S := by
  simp [CutQueryComplexity.RootedTree.crossSet, CutQueryComplexity.RootedTree.Crosses,
    mem_crossedEdges, CutQueryComplexity.RootedTree.toTwoRespecting]

omit [LinearOrder V] in
theorem card_crossSet_eq (T : CutQueryComplexity.RootedTree V) (S : Finset V) :
    (T.crossSet S).card = (T.toTwoRespecting.crossedEdges S).card :=
  congrArg Finset.card (Finset.ext (mem_crossSet_iff T S))

/-- The two-respecting search, also returning the value of its shore. -/
noncomputable def twoRespectingVal (T : TwoRespecting.RootedTree V) :
    Comp (Finset V) ℝ (Option (ℝ × Finset V)) :=
  (tabulate (edgeInfo T) T.edgeList).bind fun info =>
    (mapList (fun pq => diffBlock T (interestOf T info) pq.1 pq.2) T.headPairs).bind fun d =>
      (mapList (fun P => samePath T (T.sortPre (T.pathEdges P))) T.heads.toList).bind fun s =>
        (askList (candidates T (d.flatten ++ s.flatten))).map fun vals =>
          (bestShore ((candidates T (d.flatten ++ s.flatten)).zip vals)).map fun p => (p.2, p.1)

variable {T : TwoRespecting.RootedTree V} (G : WeightedGraph V)

theorem eval_twoRespectingVal :
    (twoRespectingVal T).eval G.cut =
      (bestShore ((candidates T (foundPairs T G)).map fun C => (C, G.cut C))).map
        fun p => (p.2, p.1) := by
  simp [twoRespectingVal, foundPairs, infoOf, zip_map_self]

theorem cost_twoRespectingVal : (twoRespectingVal T).cost G.cut = (twoRespecting T).cost G.cut := by
  simp [twoRespectingVal, twoRespecting]

/-- Correctness in value form: the shore is proper, its value is its cut, and it is
no heavier than any proper shore crossing at most two tree edges. -/
theorem twoRespectingVal_correct :
    ∀ r, (twoRespectingVal T).eval G.cut = some r →
      ProperShore r.2 ∧ r.1 = G.cut r.2 ∧
        ∀ S, ProperShore S → (T.crossedEdges S).card ≤ 2 → r.1 ≤ G.cut S := by
  intro r hr
  set C := candidates T (foundPairs T G)
  rw [eval_twoRespectingVal] at hr
  rcases hb : bestShore (C.map fun C => (C, G.cut C)) with _ | ⟨X, x⟩
  · rw [hb] at hr; exact absurd hr (by simp)
  rw [hb] at hr
  simp only [Option.map_some, Option.some.injEq] at hr
  subst hr
  have hne : C.map (fun C => (C, G.cut C)) ≠ [] := by intro h; rw [h] at hb; simp [bestShore] at hb
  obtain ⟨p, hpm, hb', hmin⟩ := bestShore_spec _ hne
  rw [hb] at hb'
  simp only [Option.some.injEq] at hb'
  subst hb'
  obtain ⟨X', hX'C, hX'⟩ := List.mem_map.mp hpm
  simp only [Prod.mk.injEq] at hX'
  obtain ⟨rfl, rfl⟩ := hX'
  -- the shore is the output of `twoRespecting`
  have hout : (twoRespecting T).eval G.cut = X' := by
    rw [eval_twoRespecting, hb]; rfl
  have hroot : ∃ v, v ≠ T.root := by
    rcases List.mem_append.mp hX'C with h | h
    · obtain ⟨e, he, -⟩ := List.mem_map.mp h
      exact ⟨e, mem_edgeList.mp he⟩
    · obtain ⟨p, hp, -⟩ := List.mem_map.mp h
      exact ⟨p.1, (foundPairs_valid G hp).1⟩
  obtain ⟨hvalid, hopt⟩ := twoRespecting_correct G hroot
  rw [hout] at hvalid hopt
  refine ⟨isTwoRespShore_nonempty hvalid, rfl, fun S hS hc => ?_⟩
  rcases isTwoRespShore_of_card_le_two hS.1 hS.2 hc with h | h
  · exact hopt S h
  · rw [← G.cut_compl S]; exact hopt _ h

/-- The search returns a shore whenever the tree has an edge. -/
theorem twoRespectingVal_isSome (hV : ∃ v, v ≠ T.root) :
    ((twoRespectingVal T).eval G.cut).isSome := by
  obtain ⟨v, hv⟩ := hV
  rw [eval_twoRespectingVal]
  have hmem : T.subtree v ∈ candidates T (foundPairs T G) :=
    List.mem_append_left _ (List.mem_map.mpr ⟨v, mem_edgeList.mpr hv, rfl⟩)
  have hne : (candidates T (foundPairs T G)).map (fun C => (C, G.cut C)) ≠ [] := by
    intro h; rw [List.map_eq_nil_iff] at h; rw [h] at hmem; simp at hmem
  obtain ⟨p, -, hb, -⟩ := bestShore_spec _ hne
  rw [hb]; rfl

end TwoRespecting

/-! ### The interface on `Prog` and `RootedTree` -/

namespace TwoRespecting

open Search Search.Comp
open scoped Classical

variable {V : Type} [Fintype V]

/-- A classical linear order whose equality test is the classical one. -/
@[instance_reducible]
noncomputable def classicalOrder (V : Type) : LinearOrder V :=
  let L : LinearOrder V := IsWellOrder.linearOrder WellOrderingRel
  { L with
    toDecidableEq := fun a b => Classical.propDecidable (a = b)
    compare := fun a b => @compareOfLessAndEq V a b L.toLT (L.toDecidableLT a b)
      (fun a b => Classical.propDecidable (a = b))
    compare_eq_compareOfLessAndEq := fun _ _ => rfl }

/-- Auxiliary: the program for given equality and order instances. -/
noncomputable def twoRespectingProgAux [DecidableEq V] [LinearOrder V]
    (T : CutQueryComplexity.RootedTree V) : Prog (Finset V) ℝ (Option (ℝ × Finset V)) :=
  (twoRespectingVal T.toTwoRespecting).toProg

/-- **Deterministic two-respecting search** on `Prog`, for any rooted spanning tree.
The program depends only on `T`. -/
noncomputable def twoRespectingProg (T : CutQueryComplexity.RootedTree V) :
    Prog (Finset V) ℝ (Option (ℝ × Finset V)) :=
  @twoRespectingProgAux V _ (fun a b => Classical.propDecidable (a = b)) (classicalOrder V) T

/-- Correctness: an output is a proper shore whose value is its cut, and the value is
at most the cut of every proper shore crossing at most two tree edges. -/
theorem twoRespectingProg_correct (T : CutQueryComplexity.RootedTree V) (G : WeightedGraph V) :
    ∀ r, Prog.eval G.cut (twoRespectingProg T) = some r →
      ProperShore r.2 ∧ r.1 = G.cut r.2 ∧
        ∀ S, ProperShore S → (T.crossSet S).card ≤ 2 → r.1 ≤ G.cut S := by
  intro r hr
  have hr' : (@twoRespectingVal V _ (fun a b => Classical.propDecidable (a = b))
      (classicalOrder V) T.toTwoRespecting).eval G.cut = some r :=
    (eval_toProg _ _).symm.trans hr
  obtain ⟨h1, h2, h3⟩ := @twoRespectingVal_correct V _ (fun a b => Classical.propDecidable (a = b))
    (classicalOrder V) T.toTwoRespecting G r hr'
  refine ⟨h1, h2, fun S hS hc => h3 S hS ?_⟩
  rw [← @card_crossSet_eq V _ (fun a b => Classical.propDecidable (a = b))]
  exact hc

/-- The output is `some` whenever some vertex is not the root. -/
theorem twoRespectingProg_isSome (T : CutQueryComplexity.RootedTree V) (G : WeightedGraph V)
    (hV : ∃ v, v ≠ T.root) : (Prog.eval G.cut (twoRespectingProg T)).isSome :=
  (congrArg Option.isSome (eval_toProg _ _)).trans
    (@twoRespectingVal_isSome V _ (fun a b => Classical.propDecidable (a = b)) (classicalOrder V)
      T.toTwoRespecting G hV)

/-- Query count `72 n (⌈log₂ n⌉ + 1)` on every oracle. -/
theorem twoRespectingProg_cost (T : CutQueryComplexity.RootedTree V) (G : WeightedGraph V) :
    Prog.cost G.cut (twoRespectingProg T) ≤
      72 * Fintype.card V * (Nat.clog 2 (Fintype.card V) + 1) := by
  have h := @twoRespecting_cost V _ (fun a b => Classical.propDecidable (a = b)) (classicalOrder V)
    T.toTwoRespecting G
  rw [← @cost_twoRespectingVal V _ (fun a b => Classical.propDecidable (a = b))
    (classicalOrder V), ← cost_toProg] at h
  exact h

end TwoRespecting
end CutQueryComplexity
