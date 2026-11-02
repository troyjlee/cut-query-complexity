import CutQueryComplexity.Graph.ForestFacts
import CutQueryComplexity.Primitive.CrossSearch

/-! # A deterministic `O(n log n)` spanning-forest program

Each successful crossing-edge search merges two components. An unsuccessful
search certifies a complete component and marks its vertices as finished.
The potential `number of forest edges + number of finished vertices` grows
on every unfinished iteration and is less than `2*n`.
-/

namespace CutQueryComplexity

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Finished vertices already have every true connection represented in the forest. -/
def ForestClosed (G : WeightedGraph V) (F : _root_.SimpleGraph V) (C : Finset V) : Prop :=
  ∀ u ∈ C, ∀ v, G.support.Reachable u v → F.Reachable u v

theorem outside_exists {C : Finset V} (h : C ≠ Finset.univ) : ∃ v, v ∉ C :=
  not_forall.mp (fun hall => h (Finset.eq_univ_of_forall hall))

/-- A root chosen solely from the publicly maintained finished set. -/
def outsideRoot (C : Finset V) (h : C ≠ Finset.univ) : V := Classical.choose (outside_exists h)

theorem outsideRoot_notMem (C : Finset V) (h : C ≠ Finset.univ) : outsideRoot C h ∉ C :=
  Classical.choose_spec (outside_exists h)

def forestStepCost (V : Type) [Fintype V] : ℕ := 6 * (searchDepth V + 1)

/-- Bounded component merging; inconsistent transcripts still produce a graph. -/
def forestGrow : (steps : ℕ) → _root_.SimpleGraph V → Finset V →
    DTree (Finset V) ℝ (_root_.SimpleGraph V) (steps * forestStepCost V)
  | 0, F, _ => DTree.pure F
  | steps + 1, F, C =>
      if h : C = Finset.univ then DTree.pure F else
        let B := forestBlock F (outsideRoot C h)
        ((findCross (searchDepth V) B Bᶜ).bind fun answer => match answer with
          | none => forestGrow steps F (C ∪ B)
          | some (u, v) => forestGrow steps (F ⊔ _root_.SimpleGraph.edge u v) C).cast
            (by unfold forestStepCost; ring)

theorem forest_of_closed_univ (G : WeightedGraph V) (F : _root_.SimpleGraph V)
    (hsub : F ≤ G.support) (hacyc : F.IsAcyclic) (hclosed : ForestClosed G F Finset.univ) :
    IsSpanningForest G F :=
  ⟨hsub, hacyc, fun u v h => hclosed u (Finset.mem_univ _) v h⟩

/-- Every sufficient public budget finishes all components, even for disconnected graphs. -/
theorem forestGrow_correct (G : WeightedGraph V) (steps : ℕ) (F : _root_.SimpleGraph V)
    (C : Finset V) (hsub : F ≤ G.support) (hacyc : F.IsAcyclic)
    (hclosed : ForestClosed G F C)
    (hbudget : 2 * Fintype.card V ≤ F.edgeFinset.card + C.card + steps) :
    IsSpanningForest G ((forestGrow steps F C).eval G.cut) := by
  induction steps generalizing F C with
  | zero =>
      have hC : C = Finset.univ := by
        by_contra h
        have hc : C.card < Fintype.card V := by
          have hle := Finset.card_le_univ C
          have hne : C.card ≠ Fintype.card V := by
            intro he; exact h (Finset.eq_univ_of_card C he)
          omega
        have hf := forest_card_le F hacyc
        omega
      have hf := forest_of_closed_univ G F hsub hacyc (hC ▸ hclosed)
      simpa only [forestGrow, DTree.eval_pure] using hf
  | succ steps ih =>
      by_cases hC : C = Finset.univ
      · have hf := forest_of_closed_univ G F hsub hacyc (hC ▸ hclosed)
        simpa only [forestGrow, dite_eq_left hC, DTree.eval_pure] using hf
      · let root := outsideRoot C hC
        let B := forestBlock F root
        have hroot : root ∉ C := outsideRoot_notMem C hC
        have hrootB : root ∈ B := root_mem_forestBlock F root
        have hsearch := findCross_logarithmic G (S := B) (T := Bᶜ) disjoint_compl_right
        rw [forestGrow, dite_eq_right hC]
        change IsSpanningForest G ((DTree.cast _ (DTree.bind (findCross (searchDepth V) B Bᶜ) _)).eval G.cut)
        rw [DTree.eval_cast, DTree.eval_bind]
        cases he : (findCross (searchDepth V) B Bᶜ).eval G.cut with
        | none =>
            have hz : G.cut B = 0 := by simpa [he, CrossResult] using hsearch
            apply ih F (C ∪ B) hsub hacyc
            · intro u hu v huv
              rcases Finset.mem_union.mp hu with hu | hu
              · exact hclosed u hu v huv
              · exact closed_block_spans G F root hz hu huv
            · have hinc : C.card + 1 ≤ (C ∪ B).card := by
                have hi : insert root C ⊆ C ∪ B := by
                  intro u hu
                  rcases Finset.mem_insert.mp hu with rfl | hu
                  · exact Finset.mem_union_right C hrootB
                  · exact Finset.mem_union_left B hu
                simpa [Finset.card_insert_of_notMem hroot] using Finset.card_mono hi
              omega
        | some edge =>
            rcases edge with ⟨u, v⟩
            have hp : u ∈ B ∧ v ∈ Bᶜ ∧ 0 < G.w u v := by simpa [he, CrossResult] using hsearch
            have hnr : ¬F.Reachable u v := not_reachable_across_block F root hp.1
              (Finset.mem_compl.mp hp.2.1)
            have hne : u ≠ v := by intro h; subst v; exact hnr .rfl
            have hn : ¬F.Adj u v := fun h => hnr h.reachable
            have hsub' : F ⊔ _root_.SimpleGraph.edge u v ≤ G.support :=
              sup_le hsub ((_root_.SimpleGraph.edge_le_iff G.support).mpr (Or.inr (ne_of_gt hp.2.2)))
            apply ih _ C hsub' (hacyc.sup_edge_of_not_reachable hnr)
            · intro a ha b hab
              exact (hclosed a ha b hab).mono le_sup_left
            · have hc : (F ⊔ _root_.SimpleGraph.edge u v).edgeFinset.card =
                    F.edgeFinset.card + 1 := by
                convert F.card_edgeFinset_sup_edge hn hne using 1
              convert (show 2 * Fintype.card V ≤
                (F ⊔ _root_.SimpleGraph.edge u v).edgeFinset.card + C.card + steps from by omega) using 1
              congr 2
              apply congrArg Finset.card
              ext e
              simp

/-- One input-independent spanning-forest algorithm, using at most `12*n*(clog 2 n+1)` cuts. -/
def spanningForest : DTree (Finset V) ℝ (_root_.SimpleGraph V)
    (12 * Fintype.card V * (searchDepth V + 1)) :=
  (forestGrow (2 * Fintype.card V) ⊥ ∅).cast (by unfold forestStepCost; ring)

theorem spanningForest_correct (G : WeightedGraph V) :
    IsSpanningForest G (spanningForest.eval G.cut) := by
  rw [spanningForest, DTree.eval_cast]
  apply forestGrow_correct G _ _ _ bot_le _root_.SimpleGraph.isAcyclic_bot
  · simp [ForestClosed]
  · simp

theorem spanningForest_solves :
    (spanningForest (V := V)).Solves WeightedGraph.cut IsSpanningForest :=
  spanningForest_correct

theorem spanningForest_edge_bound (G : WeightedGraph V) :
    (spanningForest.eval G.cut).edgeFinset.card ≤ Fintype.card V - 1 :=
  forest_card_le _ (spanningForest_correct G).2.1

end
end CutQueryComplexity
