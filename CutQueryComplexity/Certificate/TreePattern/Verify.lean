import CutQueryComplexity.Certificate.TreePattern.Tree
import CutQueryComplexity.Primitive.Learn

/-!
# The public 4n-1 tree-pattern verifier

The query family is fixed by the labeled tree alone. Answers determine tree
capacities and the divergence of the prescribed saturated non-tree flow.
The explicit tree solver then checks feasibility, soundly against every
nonnegative weighted competitor, including changed support.
-/

set_option autoImplicit false

namespace CutQueryComplexity.Certificate.TreePattern

open Finset WeightedGraph _root_.SimpleGraph
open scoped Classical
noncomputable section

variable {n : ℕ}

def outgoingSet (hn : 2 ≤ n) (T : LabelledTree n) (v : Fin n) : Finset (Fin n) :=
  univ.filter fun u => ¬T.val.Adj v u ∧ reducedCost hn T v u < 0

@[simp] theorem mem_outgoingSet (hn : 2 ≤ n) (T : LabelledTree n) (v u : Fin n) :
    u ∈ outgoingSet hn T v ↔ ¬T.val.Adj v u ∧ reducedCost hn T v u < 0 := by
  simp [outgoingSet]

theorem self_not_mem_outgoingSet (hn : 2 ≤ n) (T : LabelledTree n) (v : Fin n) :
    v ∉ outgoingSet hn T v := by simp

def flowQueries (hn : 2 ≤ n) (T : LabelledTree n) : Finset (Finset (Fin n)) :=
  ((univ.image fun v => {v}) ∪ T.val.edgeFinset.image Sym2.toFinset) ∪
    (univ.image (outgoingSet hn T) ∪ univ.image fun v => insert v (outgoingSet hn T v))

theorem flowQueries_card_le (hn : 2 ≤ n) (T : LabelledTree n) :
    (flowQueries hn T).card ≤ 4 * n - 1 := by
  have h1 := card_image_le (s := (univ : Finset (Fin n))) (f := fun v => ({v} : Finset (Fin n)))
  have h2 := card_image_le (s := T.val.edgeFinset) (f := Sym2.toFinset)
  have h3 := card_image_le (s := (univ : Finset (Fin n))) (f := outgoingSet hn T)
  have h4 := card_image_le (s := (univ : Finset (Fin n)))
    (f := fun v => insert v (outgoingSet hn T v))
  have he := T.property.card_edgeFinset
  have hu1 := card_union_le (univ.image fun v => ({v} : Finset (Fin n)))
    (T.val.edgeFinset.image Sym2.toFinset)
  have hu2 := card_union_le (univ.image (outgoingSet hn T))
    (univ.image fun v => insert v (outgoingSet hn T v))
  have hu := card_union_le
    ((univ.image fun v => ({v} : Finset (Fin n))) ∪ T.val.edgeFinset.image Sym2.toFinset)
    (univ.image (outgoingSet hn T) ∪ univ.image fun v => insert v (outgoingSet hn T v))
  simp only [card_univ, Fintype.card_fin] at h1 h3 h4 he
  unfold flowQueries
  omega

theorem singleton_mem_flowQueries (hn : 2 ≤ n) (T : LabelledTree n) (v : Fin n) :
    {v} ∈ flowQueries hn T := by
  exact mem_union_left _ (mem_union_left _ (mem_image_of_mem _ (mem_univ v)))

theorem pair_mem_flowQueries (hn : 2 ≤ n) (T : LabelledTree n) {u v : Fin n}
    (h : T.val.Adj u v) : {u,v} ∈ flowQueries hn T := by
  apply mem_union_left
  apply mem_union_right
  have he : s(u,v) ∈ T.val.edgeFinset := SimpleGraph.mem_edgeFinset.mpr h
  simpa only [Sym2.toFinset_mk_eq] using mem_image_of_mem Sym2.toFinset he

theorem outgoing_mem_flowQueries (hn : 2 ≤ n) (T : LabelledTree n) (v : Fin n) :
    outgoingSet hn T v ∈ flowQueries hn T := by
  exact mem_union_right _ (mem_union_left _ (mem_image_of_mem _ (mem_univ v)))

theorem inserted_mem_flowQueries (hn : 2 ≤ n) (T : LabelledTree n) (v : Fin n) :
    insert v (outgoingSet hn T v) ∈ flowQueries hn T := by
  exact mem_union_right _ (mem_union_right _ (mem_image_of_mem _ (mem_univ v)))

def measuredTreeWeight (answer : Finset (Fin n) → ℝ) (u v : Fin n) : ℝ :=
  (answer {u} + answer {v} - answer {u,v}) / 2

theorem measuredTreeWeight_cut (G : WeightedGraph (Fin n)) {u v : Fin n} (h : u ≠ v) :
    measuredTreeWeight G.cut u v = G.w u v := (G.edge_eq_three_cuts h).symm

def measuredNonTreeDiv (hn : 2 ≤ n) (T : LabelledTree n)
    (answer : Finset (Fin n) → ℝ) (v : Fin n) : ℝ :=
  answer (outgoingSet hn T v) - answer (insert v (outgoingSet hn T v)) +
    ∑ u ∈ univ.filter (T.val.Adj v), measuredTreeWeight answer v u

/-- The prescribed non-tree flow, using each competitor's own capacities. -/
def nonTreeFlow (hn : 2 ≤ n) (T : LabelledTree n) (G : WeightedGraph (Fin n))
    (u v : Fin n) : ℝ :=
  if T.val.Adj u v then 0 else if reducedCost hn T u v < 0 then G.w u v else -G.w u v

theorem nonTreeFlow_tree (hn : 2 ≤ n) (T : LabelledTree n) (G : WeightedGraph (Fin n))
    {u v : Fin n} (h : T.val.Adj u v) : nonTreeFlow hn T G u v = 0 := by
  simp [nonTreeFlow, h]

theorem nonTreeFlow_isFlow (hn : 2 ≤ n) (T : LabelledTree n) (G : WeightedGraph (Fin n)) :
    IsFlow (nonTreeFlow hn T G) := by
  intro u v
  by_cases h : T.val.Adj u v
  · simp [nonTreeFlow, h, h.symm]
  · have hr : ¬T.val.Adj v u := fun h' => h h'.symm
    by_cases huv : u = v
    · subst v
      simp [nonTreeFlow, G.diag]
    · have hne : reducedCost hn T u v ≠ 0 :=
        fun hz => h ((reducedCost_eq_zero_iff hn T huv).mp hz)
      rcases lt_or_gt_of_ne hne with hneg | hpos
      · have hrev : ¬reducedCost hn T v u < 0 := by
          rw [reducedCost_reverse]
          omega
        simp [nonTreeFlow, h, hr, hneg, hrev, G.symm v u]
      · have hnot : ¬reducedCost hn T u v < 0 := by omega
        have hrev : reducedCost hn T v u < 0 := by rw [reducedCost_reverse]; omega
        simp [nonTreeFlow, h, hr, hnot, hrev, G.symm v u]

theorem nonTreeFlow_feasible (hn : 2 ≤ n) (T : LabelledTree n)
    (G : WeightedGraph (Fin n)) : Feasible G (nonTreeFlow hn T G) := by
  refine ⟨nonTreeFlow_isFlow hn T G, fun u v => ?_⟩
  unfold nonTreeFlow
  split_ifs <;> simp [abs_of_nonneg (G.nonneg u v), G.nonneg u v]

theorem nonTreeFlow_split (hn : 2 ≤ n) (T : LabelledTree n) (G : WeightedGraph (Fin n))
    (v u : Fin n) : nonTreeFlow hn T G v u =
      2 * (if u ∈ outgoingSet hn T v then G.w v u else 0) - G.w v u +
      (if T.val.Adj v u then G.w v u else 0) := by
  by_cases ht : T.val.Adj v u
  · simp [nonTreeFlow, ht]
  · by_cases hr : reducedCost hn T v u < 0
    · simp [nonTreeFlow, ht, hr]
      ring
    · simp [nonTreeFlow, ht, hr]

theorem nonTreeFlow_netOut (hn : 2 ≤ n) (T : LabelledTree n) (G : WeightedGraph (Fin n))
    (v : Fin n) : netOut (nonTreeFlow hn T G) v = measuredNonTreeDiv hn T G.cut v := by
  have hdis : Disjoint ({v} : Finset (Fin n)) (outgoingSet hn T v) :=
    disjoint_singleton_left.mpr (self_not_mem_outgoingSet hn T v)
  have hstar := G.cross_eq_three_cuts hdis
  simp only [WeightedGraph.cross, sum_singleton, G.cut_singleton, singleton_union] at hstar
  have htree : (∑ u ∈ univ.filter (T.val.Adj v), measuredTreeWeight G.cut v u) =
      ∑ u ∈ univ.filter (T.val.Adj v), G.w v u := by
    apply sum_congr rfl
    intro u hu
    exact measuredTreeWeight_cut G (mem_filter.mp hu).2.ne
  have hsum : netOut (nonTreeFlow hn T G) v =
      2 * (∑ u ∈ outgoingSet hn T v, G.w v u) - G.degree v +
        ∑ u ∈ univ.filter (T.val.Adj v), G.w v u := by
    simp only [netOut, nonTreeFlow_split hn T G v, sum_add_distrib,
      sum_sub_distrib, ← mul_sum, sum_filter, outgoingSet, WeightedGraph.degree]
    congr 2
    simp only [mem_filter, mem_univ, true_and]
  rw [hsum, measuredNonTreeDiv, htree]
  linarith

theorem measuredTreeWeight_congr (hn : 2 ≤ n) (T : LabelledTree n)
    {a b : Finset (Fin n) → ℝ} (h : ∀ S ∈ flowQueries hn T, a S = b S)
    {u v : Fin n} (huv : T.val.Adj u v) : measuredTreeWeight a u v = measuredTreeWeight b u v := by
  unfold measuredTreeWeight
  rw [h _ (singleton_mem_flowQueries hn T u), h _ (singleton_mem_flowQueries hn T v),
    h _ (pair_mem_flowQueries hn T huv)]

theorem measuredNonTreeDiv_congr (hn : 2 ≤ n) (T : LabelledTree n)
    {a b : Finset (Fin n) → ℝ} (h : ∀ S ∈ flowQueries hn T, a S = b S) :
    measuredNonTreeDiv hn T a = measuredNonTreeDiv hn T b := by
  funext v
  unfold measuredNonTreeDiv
  rw [h _ (outgoing_mem_flowQueries hn T v), h _ (inserted_mem_flowQueries hn T v)]
  congr 1
  exact sum_congr rfl fun u hu => measuredTreeWeight_congr hn T h (mem_filter.mp hu).2

def accepts (hn : 2 ≤ n) (T : LabelledTree n) (b : Fin n → ℝ)
    (answer : Finset (Fin n) → ℝ) : Prop :=
  (∑ v, (b v - measuredNonTreeDiv hn T answer v)) = 0 ∧
    ∀ u v, T.val.Adj u v →
      |treeCorrection T (fun x => b x - measuredNonTreeDiv hn T answer x) u v| ≤
        measuredTreeWeight answer u v

theorem accepts_congr (hn : 2 ≤ n) (T : LabelledTree n) (b : Fin n → ℝ)
    {a a' : Finset (Fin n) → ℝ} (h : ∀ S ∈ flowQueries hn T, a S = a' S) :
    accepts hn T b a ↔ accepts hn T b a' := by
  unfold accepts
  rw [measuredNonTreeDiv_congr hn T h]
  constructor <;> rintro ⟨hd, hf⟩ <;> refine ⟨hd, fun u v huv => ?_⟩
  · rw [← measuredTreeWeight_congr hn T h huv]
    exact hf u v huv
  · rw [measuredTreeWeight_congr hn T h huv]
    exact hf u v huv

/-- Acceptance produces an actual feasible flow, rather than a supplied oracle. -/
theorem accepts_sound (hn : 2 ≤ n) (T : LabelledTree n) (G : WeightedGraph (Fin n))
    (b : Fin n → ℝ) (hacc : accepts hn T b G.cut) :
    ∃ f, Feasible G f ∧ ∀ v, netOut f v = b v := by
  let d := fun v => b v - measuredNonTreeDiv hn T G.cut v
  let g := treeCorrection T d
  let h := nonTreeFlow hn T G
  refine ⟨fun u v => g u v + h u v, ⟨?_, ?_⟩, ?_⟩
  · intro u v
    change treeCorrection T d v u + nonTreeFlow hn T G v u =
      -(treeCorrection T d u v + nonTreeFlow hn T G u v)
    rw [(treeCorrection_isFlow T d) u v, (nonTreeFlow_isFlow hn T G) u v]
    ring
  · intro u v
    change |g u v + h u v| ≤ G.w u v
    by_cases ht : T.val.Adj u v
    · have hh : h u v = 0 := nonTreeFlow_tree hn T G ht
      rw [hh, add_zero]
      exact (hacc.2 u v ht).trans_eq (measuredTreeWeight_cut G ht.ne)
    · have hg : g u v = 0 := treeCorrection_eq_zero T d u v ht
      rw [hg, zero_add]
      exact (nonTreeFlow_feasible hn T G).2 u v
  · intro v
    rw [netOut_add, treeCorrection_netOut T d hacc.1,
      nonTreeFlow_netOut hn T G v]
    dsimp [d]
    ring

theorem accepts_transfer (hn : 2 ≤ n) (T : LabelledTree n)
    (G H : WeightedGraph (Fin n)) (b : Fin n → ℝ)
    (hacc : accepts hn T b G.cut) (hH : Consistent G H (flowQueries hn T)) :
    ∃ f, Feasible H f ∧ ∀ v, netOut f v = b v := by
  exact accepts_sound hn T H b ((accepts_congr hn T b hH).mpr hacc)

/-- This local completeness lemma consumes an explicit normal-form flow.
Global existence of such a public tree is proved separately in NormalForm. -/
theorem accepts_of_normalForm (hn : 2 ≤ n) (T : LabelledTree n)
    (G : WeightedGraph (Fin n)) (b : Fin n → ℝ) {f : Fin n → Fin n → ℝ}
    (hf : Feasible G f) (hdiv : ∀ v, netOut f v = b v)
    (hoff : ∀ u v, ¬T.val.Adj u v → f u v = nonTreeFlow hn T G u v) :
    accepts hn T b G.cut := by
  let g := fun u v => f u v - nonTreeFlow hn T G u v
  let d := fun v => b v - measuredNonTreeDiv hn T G.cut v
  have hg : IsFlow g := by
    intro u v
    dsimp [g]
    rw [hf.1 u v, (nonTreeFlow_isFlow hn T G) u v]
    ring
  have hgs : ∀ u v, ¬T.val.Adj u v → g u v = 0 := by
    intro u v huv
    simp [g, hoff u v huv]
  have hgd : ∀ v, netOut g v = d v := by
    intro v
    change (∑ u, (f v u - nonTreeFlow hn T G v u)) = _
    rw [sum_sub_distrib]
    change netOut f v - netOut (nonTreeFlow hn T G) v = _
    rw [hdiv v, nonTreeFlow_netOut hn T G v]
  have hd : ∑ v, d v = 0 := by
    rw [← sum_congr rfl (fun v _ => hgd v)]
    exact hg.sum_sum_eq_zero univ
  have hgeq := treeCorrection_unique T d hd hg hgs hgd
  refine ⟨hd, fun u v huv => ?_⟩
  change |treeCorrection T d u v| ≤ _
  rw [← hgeq, show g u v = f u v by simp [g, nonTreeFlow_tree hn T G huv],
    measuredTreeWeight_cut G huv.ne]
  exact hf.2 u v

/-- The query schedule is public; only the final arithmetic uses the answers. -/
def verifyFlow (hn : 2 ≤ n) (T : LabelledTree n) (b : Fin n → ℝ) :
    DTree (Finset (Fin n)) ℝ Bool (4 * n - 1) :=
  ((DTree.queryList id (fun _ => (0 : ℝ)) (flowQueries hn T).toList).map
    (fun a => decide (accepts hn T b a))).weaken
      (by simpa using flowQueries_card_le hn T)

theorem verifyFlow_eval (hn : 2 ≤ n) (T : LabelledTree n) (b : Fin n → ℝ)
    (G : WeightedGraph (Fin n)) :
    (verifyFlow hn T b).eval G.cut = true ↔ accepts hn T b G.cut := by
  simp only [verifyFlow, DTree.eval, DTree.run_weaken, DTree.run_map, DTree.queryList_run,
    id_eq, decide_eq_true_eq]
  apply accepts_congr hn T b
  intro S hS
  simp [hS]

theorem verifyFlow_cost (hn : 2 ≤ n) (T : LabelledTree n) (b : Fin n → ℝ)
    (answer : Finset (Fin n) → ℝ) : (verifyFlow hn T b).cost answer ≤ 4 * n - 1 :=
  DTree.cost_le _ _

end
end CutQueryComplexity.Certificate.TreePattern

#print axioms CutQueryComplexity.Certificate.TreePattern.flowQueries_card_le
#print axioms CutQueryComplexity.Certificate.TreePattern.nonTreeFlow_isFlow
#print axioms CutQueryComplexity.Certificate.TreePattern.nonTreeFlow_netOut
#print axioms CutQueryComplexity.Certificate.TreePattern.accepts_sound
#print axioms CutQueryComplexity.Certificate.TreePattern.accepts_transfer
#print axioms CutQueryComplexity.Certificate.TreePattern.accepts_of_normalForm
#print axioms CutQueryComplexity.Certificate.TreePattern.verifyFlow_eval
#print axioms CutQueryComplexity.Certificate.TreePattern.verifyFlow_cost
