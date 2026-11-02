import CutQueryComplexity.SupportForest.FindPos
import CutQueryComplexity.Search.Subst
import CutQueryComplexity.Graph.Operations
import Mathlib.Data.Finset.Sort

/-! # The two cut-query simulations of subset-sum oracles

The forest routine runs `findPos` twice per merge, each time against a subset-sum oracle that
is not a cut function but is computable from two cut queries and one known value:

* **Inside.** On the vertices of a class `A` with known `cut A`, the mass of `u ∈ A` is
  `cross {u} Aᶜ`. For any `S`, the rectangle identity
  `2 cross (S ∩ A) Aᶜ = cut (S ∩ A) + cut A − cut (A \ S)` (`cross_inter_compl_eq`) gives the
  subset sum from the two queries `cut (S ∩ A)` and `cut (A \ S)`.
* **Outside.** On `Aᶜ` with the degree `d_u` known, the mass of `v` is `w u v`. For any `S`,
  `2 cross {u} (S \ {u}) = d_u + cut (S \ {u}) − cut (S ∪ {u})` (`cross_eq_three_cuts`) gives
  the subset sum from two queries.

Each simulated oracle call costs exactly two cut queries (`Comp.subst`), so the searches cost
at most `2 ⌈log₂ |A|⌉` and `2 ⌈log₂ |Aᶜ|⌉` cut queries.
-/

namespace CutQueryComplexity
namespace SupportForest

open WeightedGraph Search Search.Comp Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## Rectangle identities -/

/-- `2 cross (S ∩ A) Aᶜ = cut (S ∩ A) + cut A − cut (A \ S)`. -/
theorem cross_inter_compl_eq (G : WeightedGraph V) (A S : Finset V) :
    G.cross (S ∩ A) Aᶜ = (G.cut (S ∩ A) + G.cut A - G.cut (A \ S)) / 2 := by
  have h : G.cut (S ∩ A) + G.cut A + G.cross (A \ S) (S ∩ A) =
      G.cut (A \ S) + G.cross (S ∩ A) (A \ S) + (G.cross (S ∩ A) Aᶜ + G.cross (S ∩ A) Aᶜ) := by
    simp only [cut_eq_sum_ite, cross_eq_sum_ite, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    by_cases huS : u ∈ S <;> by_cases huA : u ∈ A <;>
      by_cases hvS : v ∈ S <;> by_cases hvA : v ∈ A <;>
      simp [huS, huA, hvS, hvA]
  rw [G.cross_comm (A \ S)] at h
  linarith

/-- The inside mass of a vertex: its weight to the outside of `A`, or zero outside `A`. -/
noncomputable def insideMass (G : WeightedGraph V) (A : Finset V) (v : V) : ℝ :=
  if v ∈ A then G.cross {v} Aᶜ else 0

theorem insideMass_nonneg (G : WeightedGraph V) (A : Finset V) (v : V) :
    0 ≤ insideMass G A v := by
  unfold insideMass; split <;> simp [G.cross_nonneg]

theorem sum_insideMass (G : WeightedGraph V) (A S : Finset V) :
    ∑ v ∈ S, insideMass G A v = G.cross (S ∩ A) Aᶜ := by
  simp only [insideMass, ← Finset.sum_filter, Finset.filter_mem_eq_inter, cross,
    Finset.sum_singleton]

/-! ## The inside search -/

/-- Two cut queries answering the subset-sum question `S ↦ cross (S ∩ A) Aᶜ`, given
`m = cut A`. -/
noncomputable def insideOracle (A : Finset V) (m : ℝ) (S : Finset V) : Comp (Finset V) ℝ ℝ :=
  (ask (S ∩ A)).bind fun a => (ask (A \ S)).map fun b => (a + m - b) / 2

theorem insideOracle_eval (G : WeightedGraph V) (A S : Finset V) :
    (insideOracle A (G.cut A) S).eval G.cut = ∑ v ∈ S, insideMass G A v := by
  simp only [insideOracle, eval_bind, eval_map, eval_ask]
  rw [sum_insideMass, cross_inter_compl_eq]

omit [Fintype V] in
theorem insideOracle_cost (A : Finset V) (m : ℝ) (S : Finset V) (o : Finset V → ℝ) :
    (insideOracle A m S).cost o = 2 := by
  simp [insideOracle]

/-! ## The outside search -/

/-- Two cut queries answering the subset-sum question `S ↦ ∑ v ∈ S, w u v`, given
`d = degree u`. -/
noncomputable def outsideOracle (u : V) (d : ℝ) (S : Finset V) : Comp (Finset V) ℝ ℝ :=
  (ask (S.erase u)).bind fun a => (ask (insert u (S.erase u))).map fun b => (d + a - b) / 2

theorem outsideOracle_eval (G : WeightedGraph V) (u : V) (S : Finset V) :
    (outsideOracle u (G.degree u) S).eval G.cut = ∑ v ∈ S, G.w u v := by
  simp only [outsideOracle, eval_bind, eval_map, eval_ask]
  have h : G.cross {u} (S.erase u) =
      (G.degree u + G.cut (S.erase u) - G.cut (insert u (S.erase u))) / 2 := by
    rw [G.cross_eq_three_cuts (by simp), cut_singleton, ← Finset.insert_eq]
  rw [← h, cross, Finset.sum_singleton, Finset.sum_erase _ (G.diag u)]

omit [Fintype V] in
theorem outsideOracle_cost (u : V) (d : ℝ) (S : Finset V) (o : Finset V → ℝ) :
    (outsideOracle u d S).cost o = 2 := by
  simp [outsideOracle]

/-! ## The two searches -/

variable [LinearOrder V]

/-- The inside endpoint: a vertex of `A` with positive weight to `Aᶜ`, with that weight. -/
noncomputable def insideSearch (dflt : V) (A : Finset V) (m : ℝ) :
    Comp (Finset V) ℝ (V × ℝ) :=
  subst (insideOracle A m) (findPos dflt A.sort m)

theorem insideSearch_spec (G : WeightedGraph V) (dflt : V) (A : Finset V)
    (hpos : 0 < G.cut A) :
    ((insideSearch dflt A (G.cut A)).eval G.cut).1 ∈ A ∧
    0 < G.cross {((insideSearch dflt A (G.cut A)).eval G.cut).1} Aᶜ ∧
    ((insideSearch dflt A (G.cut A)).eval G.cut).2 =
      G.cross {((insideSearch dflt A (G.cut A)).eval G.cut).1} Aᶜ ∧
    (insideSearch dflt A (G.cut A)).cost G.cut ≤ 2 * Nat.clog 2 A.card := by
  have hev := eval_subst (insideOracle A (G.cut A)) G.cut (fun S => ∑ v ∈ S, insideMass G A v)
    (insideOracle_eval G A) (findPos dflt A.sort (G.cut A))
  have hcost := cost_subst_le (insideOracle A (G.cut A)) G.cut
    (fun S => ∑ v ∈ S, insideMass G A v) (insideOracle_eval G A)
    (fun S => le_of_eq (insideOracle_cost A _ S G.cut)) (findPos dflt A.sort (G.cut A))
  have hmass : G.cut A = ∑ v ∈ A.sort.toFinset, insideMass G A v := by
    rw [Finset.sort_toFinset, sum_insideMass, Finset.inter_self, cross_compl]
  obtain ⟨hmem, hp, heq, hc⟩ := findPos_spec (insideMass G A) (insideMass_nonneg G A) dflt _
    A.sort (G.cut A) le_rfl (Finset.sort_nodup _ _) hmass hpos
  unfold insideSearch
  rw [hev]
  rw [Finset.mem_sort] at hmem
  rw [insideMass, ite_eq_left hmem] at hp heq
  refine ⟨hmem, hp, heq, ?_⟩
  rw [Finset.length_sort] at hc
  omega

/-- The outside endpoint: a vertex of `B` joined to `u` by a positive edge, with its weight. -/
noncomputable def outsideSearch (dflt u : V) (d : ℝ) (B : Finset V) (m : ℝ) :
    Comp (Finset V) ℝ (V × ℝ) :=
  subst (outsideOracle u d) (findPos dflt B.sort m)

theorem outsideSearch_spec (G : WeightedGraph V) (dflt u : V) (B : Finset V)
    (hpos : 0 < G.cross {u} B) :
    ((outsideSearch dflt u (G.degree u) B (G.cross {u} B)).eval G.cut).1 ∈ B ∧
    0 < G.w u ((outsideSearch dflt u (G.degree u) B (G.cross {u} B)).eval G.cut).1 ∧
    ((outsideSearch dflt u (G.degree u) B (G.cross {u} B)).eval G.cut).2 =
      G.w u ((outsideSearch dflt u (G.degree u) B (G.cross {u} B)).eval G.cut).1 ∧
    (outsideSearch dflt u (G.degree u) B (G.cross {u} B)).cost G.cut ≤
      2 * Nat.clog 2 B.card := by
  have hev := eval_subst (outsideOracle u (G.degree u)) G.cut (fun S => ∑ v ∈ S, G.w u v)
    (outsideOracle_eval G u) (findPos dflt B.sort (G.cross {u} B))
  have hcost := cost_subst_le (outsideOracle u (G.degree u)) G.cut
    (fun S => ∑ v ∈ S, G.w u v) (outsideOracle_eval G u)
    (fun S => le_of_eq (outsideOracle_cost u _ S G.cut)) (findPos dflt B.sort (G.cross {u} B))
  have hmass : G.cross {u} B = ∑ v ∈ B.sort.toFinset, G.w u v := by
    rw [Finset.sort_toFinset, cross, Finset.sum_singleton]
  obtain ⟨hmem, hp, heq, hc⟩ := findPos_spec (G.w u) (G.nonneg u) dflt _
    B.sort (G.cross {u} B) le_rfl (Finset.sort_nodup _ _) hmass hpos
  unfold outsideSearch
  rw [hev]
  rw [Finset.mem_sort] at hmem
  refine ⟨hmem, hp, heq, ?_⟩
  rw [Finset.length_sort] at hc
  omega

end SupportForest
end CutQueryComplexity
