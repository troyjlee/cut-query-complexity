import CutQueryComplexity.Certificate.Main
import CutQueryComplexity.Model.Composition
import CutQueryComplexity.Model.Complexity

/-! # `cert(G)` lower-bounds deterministic cut-query complexity

A deterministic decision tree that outputs the minimum-cut value of every nonnegative
weighted graph on `V` asks, on input `G`, a family of shores whose answers already force
the value: every competitor consistent with `G` on those shores produces the same
transcript, hence the same output. The family is therefore a certificate, so
`cert(G) ≤ cost(T, G) ≤ q` for every such tree of budget `q`, and
`cert(G) ≤ D(λ)` for the exact deterministic complexity `D(λ)` of the value problem.
-/

namespace CutQueryComplexity
namespace Certificate

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The shores a decision tree asks the cut oracle of `G`. -/
def queriedShores {O : Type} {q : ℕ} (T : DTree (Finset V) ℝ O q) (G : WeightedGraph V) :
    Finset (Finset V) :=
  ((DTree.transcript G.cut T).map Prod.fst).toFinset

theorem queriedShores_card_le {O : Type} {q : ℕ} (T : DTree (Finset V) ℝ O q)
    (G : WeightedGraph V) : (queriedShores T G).card ≤ T.cost G.cut :=
  (List.toFinset_card_le _).trans (by rw [List.length_map, DTree.transcript_length])

/-- A competitor answering the asked shores as `G` does receives the same output. -/
theorem eval_eq_of_consistent {O : Type} {q : ℕ} (T : DTree (Finset V) ℝ O q)
    {G G' : WeightedGraph V} (h : Consistent G G' (queriedShores T G)) :
    T.eval G'.cut = T.eval G.cut := by
  have he := DTree.run_eq_of_agree T G.cut G'.cut fun S v hv =>
    (h S (List.mem_toFinset.mpr (List.mem_map.mpr ⟨(S, v), hv, rfl⟩))).symm
  exact (congrArg Prod.fst he).symm

/-- The value problem: on input `G` the cut oracle answers `G.cut`, and the correct
outputs are exactly `mincutValue G`. -/
def minCutValueRead (G : WeightedGraph V) : Finset V → ℝ := G.cut

def MinCutValueGood (G : WeightedGraph V) (v : ℝ) : Prop := v = mincutValue G

/-- The exact deterministic cut-query complexity of the minimum-cut value on `V`. -/
noncomputable def minCutValueComplexity (V : Type) [Fintype V] [DecidableEq V] : WithTop ℕ :=
  deterministicComplexity (minCutValueRead (V := V)) MinCutValueGood

/-- The shores asked on `G` by a correct value algorithm certify `G`. -/
theorem isMinCutCertificate_queriedShores {q : ℕ} {T : DTree (Finset V) ℝ ℝ q}
    (hT : T.Solves minCutValueRead MinCutValueGood) (G : WeightedGraph V) :
    IsMinCutCertificate G (queriedShores T G) := by
  intro G' hG'
  have h1 : T.eval G'.cut = mincutValue G' := hT G'
  have h2 : T.eval G.cut = mincutValue G := hT G
  rw [← h1, ← h2, eval_eq_of_consistent T hG']

/-- Instance-wise lower bound: a correct deterministic value algorithm asks at least
`cert(G)` shores on input `G`. -/
theorem certificateComplexity_le_cost {q : ℕ} {T : DTree (Finset V) ℝ ℝ q}
    (hT : T.Solves minCutValueRead MinCutValueGood) (G : WeightedGraph V) :
    certificateComplexity G ≤ T.cost G.cut :=
  (certificateComplexity_le (isMinCutCertificate_queriedShores hT G)).trans
    (queriedShores_card_le T G)

theorem certificateComplexity_le_budget {q : ℕ} {T : DTree (Finset V) ℝ ℝ q}
    (hT : T.Solves minCutValueRead MinCutValueGood) (G : WeightedGraph V) :
    certificateComplexity G ≤ q :=
  (certificateComplexity_le_cost hT G).trans (T.cost_le G.cut)

theorem cut_eq_mincutValue_of_isMinCut {G : WeightedGraph V} {S : Finset V} (h : IsMinCut G S) :
    G.cut S = mincutValue G := by
  obtain ⟨T, hT, hTv⟩ := exists_isMinCut G ⟨S, (mem_properShores S).mpr h.1⟩
  exact le_antisymm (hTv ▸ h.2 T hT.1) (mincutValue_le G h.1)

/-- A shore algorithm becomes a value algorithm with one more query (the returned shore), so
`cert(G) ≤ q + 1` for every budget-`q` tree returning a minimum cut of every graph on `V`. -/
theorem certificateComplexity_le_shore_budget {q : ℕ}
    {T : DTree (Finset V) ℝ (Option (Finset V)) q}
    (hT : ∀ G : WeightedGraph V, ∃ S, T.eval G.cut = some S ∧ IsMinCut G S)
    (G : WeightedGraph V) : certificateComplexity G ≤ q + 1 := by
  let T' : DTree (Finset V) ℝ ℝ (q + 1) :=
    DTree.bind T fun o => match o with
      | some S => DTree.query S fun a => DTree.pure a
      | none => DTree.pure 0
  have hT' : T'.Solves minCutValueRead MinCutValueGood := by
    intro H
    obtain ⟨S, hS, hmin⟩ := hT H
    show T'.eval H.cut = mincutValue H
    have hS' : (DTree.run H.cut T).1 = some S := hS
    simp only [T', DTree.eval, DTree.run_bind]
    rw [hS']
    simp [DTree.run_query, DTree.run_pure, cut_eq_mincutValue_of_isMinCut hmin]
  exact certificateComplexity_le_budget hT' G

/-- `cert(G)` is a lower bound on the deterministic cut-query complexity of the
minimum-cut value on nonnegative weighted graphs over `V`, for every `G`. -/
theorem certificateComplexity_le_minCutValueComplexity (G : WeightedGraph V) :
    (certificateComplexity G : WithTop ℕ) ≤ minCutValueComplexity V := by
  refine le_queryComplexity fun q hq => ?_
  obtain ⟨T, hT⟩ := hq
  exact_mod_cast certificateComplexity_le_budget hT G

end Certificate
end CutQueryComplexity
