import CutQueryComplexity.DirectedCertificate.Pruning

/-! # Measurement form of the flow certificate (W5; `lem:flow` on an implicit graph)

The undirected flow certificate (`Certificate.exists_flowCert`) uses only three kinds of facts
about a competitor `G'`, all of them pair or partial-star values:

* the capacity of each unsaturated pair touching `W` (`FlowPremises.pair`);
* for each `x ∈ W`, the total competitor capacity on the pairs saturated *out of* `x`
  (`FlowPremises.starOut`) and *into* `x` (`FlowPremises.starIn`).

No other cut of `G'` is used. `exists_flowCert_premises` states the transfer with exactly these
`≤ 3 |W|` premises (at most `|W|` pairs, `2 |W|` partial stars), and the transferred flow is `0`
on every originally zero pair, whatever capacity a competitor puts there
(`transferFlow_eq_zero`). `FlowPremises.of_consistent` recovers the cut-query form.

For an implicit graph `G' ↦ toGraph G'` (e.g. `H′` of `lem:prune`) only these values, and the
degrees, are available through W1's compiler. `exists_implicitFlowTransfer` compiles the
premises, applied to `(toGraph G).sym` and the shifted flow `z = a − aᵀ − 2f`, and
`exists_implicitFlowCert` concludes `Σ_{v ∈ S} d v ≤ F_{toGraph G'}(S)` for every shore.
`PruningCert.exists_flowCert_H` instantiates it for `H′` with `15 n` original queries.
-/

namespace CutQueryComplexity.DirectedCertificate

open Finset WeightedDiGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Part 1: the premises actually used by the undirected transfer -/

section Premises
open Certificate WeightedGraph

/-- The pair and partial-star premises on a competitor `G'` used by the flow transfer. -/
structure FlowPremises (G G' : WeightedGraph V) (W : Finset V) (f₀ : V → V → ℝ)
    (P : Finset (V × V)) : Prop where
  pair : ∀ p ∈ P, G'.w p.1 p.2 = G.w p.1 p.2
  starOut : ∀ x ∈ W, ∑ u ∈ satOut G f₀ x, G'.w x u = ∑ u ∈ satOut G f₀ x, G.w x u
  starIn : ∀ x ∈ W, ∑ u ∈ satIn G f₀ x, G'.w x u = ∑ u ∈ satIn G f₀ x, G.w x u

omit [Fintype V] in
/-- The transferred flow vanishes on every originally zero pair (support changes: a competitor
may put positive capacity there; the transferred flow ignores it). -/
theorem transferFlow_eq_zero (G G' : WeightedGraph V) (W : Finset V) {f₀ : V → V → ℝ}
    {u v : V} (h : G.w u v = 0) : transferFlow G G' W f₀ u v = 0 := by
  simp only [transferFlow, h, div_zero, zero_mul]
  split_ifs with h1 h2
  · exact absurd h2 (not_lt.mpr (abs_nonneg _))
  · rfl
  · rfl

/-- The transfer step of `Certificate.exists_flowCert` from the pair and partial-star premises
alone (no cut-consistency). -/
theorem transferFlow_spec_premises (G : WeightedGraph V) (W : Finset V) {e : V → ℕ}
    (he : Function.Injective e) {f₀ : V → V → ℝ} (hf₀ : Certificate.Feasible G f₀)
    (G' : WeightedGraph V) (hG' : FlowPremises G G' W f₀ (unsatPairs G W e f₀)) :
    Certificate.Feasible G' (transferFlow G G' W f₀) ∧
      (∀ x ∈ W, Certificate.netOut (transferFlow G G' W f₀) x = Certificate.netOut f₀ x) ∧
      (∀ u v, (u ∈ W ∨ v ∈ W) → |f₀ u v| < G.w u v → G'.w u v = G.w u v) ∧
      (∀ u v, G.w u v = 0 → transferFlow G G' W f₀ u v = 0) := by
  classical
  set P := unsatPairs G W e f₀
  have hw : ∀ u v, (u ∈ W ∨ v ∈ W) → |f₀ u v| < G.w u v → G'.w u v = G.w u v := by
    intro u v huv hlt
    have hne : u ≠ v := fun h => by subst h; rw [G.diag, hf₀.1.self] at hlt; simp at hlt
    rcases lt_or_gt_of_ne (fun h => hne (he h)) with hlt' | hgt'
    · have hp : (u, v) ∈ P := mem_unsatPairs.mpr ⟨hlt', huv, hlt⟩
      exact hG'.pair _ hp
    · have hp : (v, u) ∈ P := mem_unsatPairs.mpr ⟨hgt', huv.symm, by
        rw [hf₀.1 u v, abs_neg, G.symm]; exact hlt⟩
      rw [G'.symm, G.symm]
      exact hG'.pair _ hp
  set f' := transferFlow G G' W f₀
  refine ⟨⟨fun u v => ?_, fun u v => ?_⟩, fun x hx => ?_, hw,
    fun u v h => transferFlow_eq_zero G G' W h⟩
  · simp only [f', transferFlow, or_comm (a := v ∈ W), hf₀.1 u v, abs_neg, G.symm v u,
      G'.symm v u]
    split_ifs <;> ring
  · simp only [f', transferFlow]
    split_ifs with h1 h2
    · rw [hw u v h1 h2]; exact h2.le
    · rw [abs_mul, abs_of_nonneg (G'.nonneg u v)]
      exact mul_le_of_le_one_left (G'.nonneg u v) (abs_div_le_one (hf₀.2 u v))
    · simp [G'.nonneg]
  · have hO := hG'.starOut x hx
    have hI := hG'.starIn x hx
    have split : ∀ H : WeightedGraph V, ∀ (s : V → ℝ),
        (∀ u, (¬ |f₀ x u| < G.w x u) → s u = f₀ x u / G.w x u * H.w x u) →
        (∀ u, |f₀ x u| < G.w x u → s u = f₀ x u) →
        ∑ u, s u = ∑ u, (if |f₀ x u| < G.w x u then f₀ x u else 0) +
          ∑ u ∈ satOut G f₀ x, H.w x u - ∑ u ∈ satIn G f₀ x, H.w x u := by
      intro H s hs1 hs2
      simp only [satOut, satIn, Finset.sum_filter]
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      · refine Finset.sum_congr rfl fun u _ => ?_
        by_cases hlt : |f₀ x u| < G.w x u
        · simp [hlt, hs2 u hlt]
        · have hsat : |f₀ x u| = G.w x u := le_antisymm (hf₀.2 x u) (not_lt.mp hlt)
          rw [hs1 u hlt]
          rcases lt_trichotomy (f₀ x u) 0 with hneg | hz | hpos
          · have hwv : G.w x u = -f₀ x u := by rw [← hsat, abs_of_neg hneg]
            have hw0 : G.w x u ≠ 0 := by linarith
            simp [hlt, hneg, not_lt.mpr hneg.le]
            rw [hwv, div_neg, div_self (by linarith)]; ring
          · simp [hz]
          · have hwv : G.w x u = f₀ x u := by rw [← hsat, abs_of_pos hpos]
            simp [hlt, hpos, not_lt.mpr hpos.le]
            rw [hwv, div_self (by linarith)]; ring
    have h1 := split G' (fun u => f' x u) (fun u hu => by
        simp only [f', transferFlow, hx, true_or, ite_true]; simp [hu])
      (fun u hu => by simp only [f', transferFlow, hx, true_or, ite_true]; simp [hu])
    have h2 := split G (fun u => f₀ x u) (fun u hu => by
        have hsat : |f₀ x u| = G.w x u := le_antisymm (hf₀.2 x u) (not_lt.mp hu)
        rcases eq_or_ne (G.w x u) 0 with h0 | h0
        · rw [h0] at hsat ⊢; rw [abs_eq_zero.mp hsat]; simp
        · rw [div_mul_cancel₀ _ h0])
      (fun u _ => rfl)
    simp only [Certificate.netOut]
    rw [h1, h2, hO, hI]

/-- Cut-consistency on the shores of `Certificate.exists_flowCert` implies the premises; the
premise form is therefore no stronger a hypothesis. -/
theorem FlowPremises.of_consistent {G G' : WeightedGraph V} {W : Finset V}
    {f₀ : V → V → ℝ} (hf₀ : Certificate.Feasible G f₀) {P : Finset (V × V)}
    (hP : ∀ p ∈ P, p.1 ≠ p.2)
    (hG' : Certificate.Consistent G G' (flowCertQueries G W f₀ P)) :
    FlowPremises G G' W f₀ P := by
  have mA : ∀ x ∈ W, {x} ∈ flowCertQueries G W f₀ P := fun x hx =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_image_of_mem (fun x => ({x} : Finset V)) hx)))))))
  have mB : ∀ x ∈ W, satOut G f₀ x ∈ flowCertQueries G W f₀ P := fun x hx =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_image_of_mem (satOut G f₀) hx)))))))
  have mC : ∀ x ∈ W, insert x (satOut G f₀ x) ∈ flowCertQueries G W f₀ P := fun x hx =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image_of_mem (fun x => insert x (satOut G f₀ x)) hx))))))
  have mD : ∀ x ∈ W, satIn G f₀ x ∈ flowCertQueries G W f₀ P := fun x hx =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image_of_mem (satIn G f₀) hx)))))
  have mE : ∀ x ∈ W, insert x (satIn G f₀ x) ∈ flowCertQueries G W f₀ P := fun x hx =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image_of_mem (fun x => insert x (satIn G f₀ x)) hx))))
  have mF : ∀ p ∈ P, {p.1} ∈ flowCertQueries G W f₀ P := fun p hp =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun p : V × V => ({p.1} : Finset V)) hp)))
  have mG : ∀ p ∈ P, {p.2} ∈ flowCertQueries G W f₀ P := fun p hp =>
    Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun p : V × V => ({p.2} : Finset V)) hp))
  have mH : ∀ p ∈ P, {p.1, p.2} ∈ flowCertQueries G W f₀ P := fun p hp =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem (fun p : V × V => ({p.1, p.2} : Finset V)) hp)
  refine ⟨fun p hp => hG'.w_eq (hP p hp) (mF p hp) (mG p hp) (mH p hp), fun x hx => ?_,
    fun x hx => ?_⟩
  · have hxO : x ∉ satOut G f₀ x := by simp [satOut, hf₀.1.self]
    have hO := hG'.cross_eq (Finset.disjoint_singleton_left.mpr hxO) (mA x hx) (mB x hx)
      (by rw [← Finset.insert_eq]; exact mC x hx)
    simpa only [cross, Finset.sum_singleton] using hO
  · have hxI : x ∉ satIn G f₀ x := by simp [satIn, hf₀.1.self]
    have hI := hG'.cross_eq (Finset.disjoint_singleton_left.mpr hxI) (mA x hx) (mD x hx)
      (by rw [← Finset.insert_eq]; exact mE x hx)
    simpa only [cross, Finset.sum_singleton] using hI

/-- **Measurement form of the undirected flow certificate.** For a feasible `f` there is a
feasible `f₀` with the same net outflows on `W` and at most `|W|` pairs `P` (each touching `W`,
with distinct ends) such that, for every competitor `G'` satisfying the `≤ 3 |W|` pair and
partial-star premises, some flow feasible in `G'` has the same net outflows on `W` and is `0` on
every originally zero pair. -/
theorem exists_flowCert_premises (G : WeightedGraph V) (W : Finset V) {f : V → V → ℝ}
    (hf : Certificate.Feasible G f) :
    ∃ f₀ : V → V → ℝ, ∃ P : Finset (V × V), Certificate.Feasible G f₀ ∧
      (∀ x ∈ W, Certificate.netOut f₀ x = Certificate.netOut f x) ∧ P.card ≤ W.card ∧
      (∀ p ∈ P, p.1 ≠ p.2 ∧ (p.1 ∈ W ∨ p.2 ∈ W)) ∧
      ∀ G' : WeightedGraph V, FlowPremises G G' W f₀ P →
        ∃ f', Certificate.Feasible G' f' ∧
          (∀ x ∈ W, Certificate.netOut f' x = Certificate.netOut f x) ∧
          (∀ u v, G.w u v = 0 → f' u v = 0) := by
  classical
  set e : V → ℕ := fun v => (Fintype.equivFin V v : ℕ)
  have he : Function.Injective e := Fin.val_injective.comp (Fintype.equivFin V).injective
  obtain ⟨f₀, hf₀, hnet₀, hP⟩ := exists_sparse_flow G W e hf
  refine ⟨f₀, unsatPairs G W e f₀, hf₀, hnet₀, hP, fun p hp => ?_, fun G' hG' => ?_⟩
  · have h := mem_unsatPairs.mp hp
    exact ⟨fun h' => by rw [h'] at h; exact lt_irrefl _ h.1, h.2.1⟩
  · obtain ⟨h1, h2, -, h4⟩ := transferFlow_spec_premises G W he hf₀ G' hG'
    exact ⟨_, h1, fun x hx => (h2 x hx).trans (hnet₀ x hx), h4⟩

end Premises

/-! ## Part 2: compiled premises for an implicit directed graph -/

section Implicit

/-- Pair capacities, symmetrized partial stars and degrees of an implicit competitor graph
`toGraph G'`, each compiled to at most `c` original outgoing-cut queries. Pair capacities are
the singleton partial stars `symStar v {w}`. -/
structure ImplicitMeasures (G : WeightedDiGraph V)
    (toGraph : WeightedDiGraph V → WeightedDiGraph V) (c : ℕ) where
  symStar : ∀ v T, Compiled G (fun G' => (toGraph G').symStar v T)
  symStar_cost : ∀ v T, (symStar v T).cost ≤ c
  outdeg : ∀ v, Compiled G (fun G' => (toGraph G').outdeg v)
  outdeg_cost : ∀ v, (outdeg v).cost ≤ c
  indeg : ∀ v, Compiled G (fun G' => (toGraph G').indeg v)
  indeg_cost : ∀ v, (indeg v).cost ≤ c

omit [Fintype V] [DecidableEq V] in
theorem symStar_singleton (H : WeightedDiGraph V) (v w : V) :
    H.symStar v {w} = H.sym.w v w := by
  simp [symStar]

omit [Fintype V] in
theorem card_biUnion_le_mul {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (t : ι → Finset (Finset V)) (c : ℕ) (h : ∀ i ∈ s, (t i).card ≤ c) :
    (s.biUnion t).card ≤ c * s.card := by
  refine Finset.card_biUnion_le.trans ?_
  rw [mul_comm]
  exact Finset.sum_le_card_nsmul _ _ _ h

/-- **`lem:flow` for an implicit graph, transfer form.** Let `f` be a feasible directed flow in
`H = toGraph G`. At most `5 c |W|` original queries (the pair, saturated partial-star and degree
measurements on `W`, compiled) ensure that every consistent `G'` has a signed flow feasible in
the symmetrization of `H′ = toGraph G'` with divergence `β_H − 2 d` on `W`, and that `H′` has
the imbalance of `H` on `W`. No other cut of `H′` is used. -/
theorem exists_implicitFlowTransfer {G : WeightedDiGraph V}
    {toGraph : WeightedDiGraph V → WeightedDiGraph V} {c : ℕ}
    (M : ImplicitMeasures G toGraph c) (W : Finset V) {f : V → V → ℝ}
    (hf : (toGraph G).Feasible f) :
    ∃ Q : Finset (Finset V), Q.card ≤ 5 * c * W.card ∧ ∀ G' : WeightedDiGraph V,
      Consistent G G' Q →
        (∃ z', Certificate.Feasible (toGraph G').sym z' ∧
          (∀ x ∈ W, Certificate.netOut z' x =
            (toGraph G).imbalance x - 2 * Certificate.netOut f x) ∧
          (∀ u v, (toGraph G).sym.w u v = 0 → z' u v = 0)) ∧
        ∀ x ∈ W, (toGraph G').imbalance x = (toGraph G).imbalance x := by
  classical
  set H := toGraph G
  obtain ⟨f₀, P, hf₀, hnet₀, hP, -, hT⟩ :=
    exists_flowCert_premises H.sym W (feasible_flowShift hf)
  set QP := P.biUnion fun p => (M.symStar p.1 {p.2}).shores
  set QO := W.biUnion fun x => (M.symStar x (Certificate.satOut H.sym f₀ x)).shores
  set QI := W.biUnion fun x => (M.symStar x (Certificate.satIn H.sym f₀ x)).shores
  set QD := W.biUnion fun x => (M.outdeg x).shores
  set QE := W.biUnion fun x => (M.indeg x).shores
  refine ⟨QP ∪ QO ∪ QI ∪ QD ∪ QE, ?_, fun G' hG' => ?_⟩
  · have h1 : QP.card ≤ c * P.card := card_biUnion_le_mul _ _ _ fun p _ => M.symStar_cost _ _
    have h2 : QO.card ≤ c * W.card := card_biUnion_le_mul _ _ _ fun x _ => M.symStar_cost _ _
    have h3 : QI.card ≤ c * W.card := card_biUnion_le_mul _ _ _ fun x _ => M.symStar_cost _ _
    have h4 : QD.card ≤ c * W.card := card_biUnion_le_mul _ _ _ fun x _ => M.outdeg_cost _
    have h5 : QE.card ≤ c * W.card := card_biUnion_le_mul _ _ _ fun x _ => M.indeg_cost _
    have u1 := Finset.card_union_le (QP ∪ QO ∪ QI ∪ QD) QE
    have u2 := Finset.card_union_le (QP ∪ QO ∪ QI) QD
    have u3 := Finset.card_union_le (QP ∪ QO) QI
    have u4 := Finset.card_union_le QP QO
    have hcP : c * P.card ≤ c * W.card := Nat.mul_le_mul_left c hP
    have : 5 * c * W.card = c * W.card + c * W.card + c * W.card + c * W.card + c * W.card := by
      ring
    omega
  simp only [consistent_union] at hG'
  obtain ⟨⟨⟨⟨hQP, hQO⟩, hQI⟩, hQD⟩, hQE⟩ := hG'
  have prem : FlowPremises H.sym (toGraph G').sym W f₀ P := by
    refine ⟨fun p hp => ?_, fun x hx => ?_, fun x hx => ?_⟩
    · have := (M.symStar p.1 {p.2}).fixes G' (consistent_biUnion.mp hQP p hp)
      simpa only [symStar_singleton] using this
    · exact (M.symStar x _).fixes G' (consistent_biUnion.mp hQO x hx)
    · exact (M.symStar x _).fixes G' (consistent_biUnion.mp hQI x hx)
  obtain ⟨z', hz', hnet, hzero⟩ := hT _ prem
  refine ⟨⟨z', hz', fun x hx => ?_, hzero⟩, fun x hx => ?_⟩
  · rw [hnet x hx, netOut_flowShift]
  · have ho := (M.outdeg x).fixes G' (consistent_biUnion.mp hQD x hx)
    have hi := (M.indeg x).fixes G' (consistent_biUnion.mp hQE x hx)
    simp only [imbalance]
    rw [ho, hi]

/-- **`lem:flow` for an implicit graph.** If `f` is feasible in `H = toGraph G` with net
outflows `d`, then at most `5 c n` original queries certify `d(S) ≤ F_{H′}(S)` for every shore
`S` and every consistent `G'`, where `H′ = toGraph G'`. -/
theorem exists_implicitFlowCert {G : WeightedDiGraph V}
    {toGraph : WeightedDiGraph V → WeightedDiGraph V} {c : ℕ}
    (M : ImplicitMeasures G toGraph c) {f : V → V → ℝ} (hf : (toGraph G).Feasible f) :
    ∃ Q : Finset (Finset V), Q.card ≤ 5 * c * Fintype.card V ∧ ∀ G' : WeightedDiGraph V,
      Consistent G G' Q → ∀ S : Finset V,
        ∑ v ∈ S, Certificate.netOut f v ≤ (toGraph G').out S := by
  obtain ⟨Q, hQ, hT⟩ := exists_implicitFlowTransfer M Finset.univ hf
  refine ⟨Q, by simpa using hQ, fun G' hG' S => ?_⟩
  obtain ⟨⟨z', hz', hnet, -⟩, himb⟩ := hT G' hG'
  have hc := Certificate.sum_netOut_le_cut hz' Sᶜ
  rw [WeightedGraph.cut_compl] at hc
  have h0 := WeightedDiGraph.sum_univ_netOut hz'.1
  rw [← Finset.sum_add_sum_compl S] at h0
  have h2 := (toGraph G').two_mul_out S
  rw [Finset.sum_congr rfl fun v _ => himb v (Finset.mem_univ v)] at h2
  have h3 : ∑ v ∈ S, Certificate.netOut z' v =
      ∑ v ∈ S, (toGraph G).imbalance v - 2 * ∑ v ∈ S, Certificate.netOut f v := by
    rw [Finset.sum_congr rfl fun v _ => hnet v (Finset.mem_univ v), Finset.sum_sub_distrib,
      Finset.mul_sum]
  linarith

end Implicit

/-! ## Instantiation for the pruned graph `H′` of `lem:prune` -/

namespace PruningCert
variable {G : WeightedDiGraph V} (C : PruningCert G)

/-- The compiled measurements of `H′ = C.toGraph G'` (`≤ 3` original queries each): degrees are
the full directed partial stars. -/
def measures : ImplicitMeasures G C.toGraph 3 where
  symStar := C.symStar
  symStar_cost := C.symStar_cost
  outdeg v := (C.outStar v univ).congr fun _ => rfl
  outdeg_cost v := C.outStar_cost v univ
  indeg v := (C.inStar v univ).congr fun _ => rfl
  indeg_cost v := C.inStar_cost v univ

/-- `C.toGraph G` is the implicit graph `H` of the actual input. -/
theorem toGraph_self_eq : C.toGraph G = C.H := by
  cases h : C.toGraph G with
  | mk c nonneg diag =>
    cases hH : C.H with
    | mk c' nonneg' diag' =>
      have : c = c' := funext fun u => funext fun v => by
        have := C.toGraph_self u v
        rw [h, hH] at this
        exact this
      subst this
      rfl

/-- **`lem:flow` on the pruned graph.** For a feasible directed flow `f` in `H` with net outflows
`d`, at most `15 n` original queries certify `d(S) ≤ F_{H′}(S)` for every shore `S` and every
consistent `G'`, where `H′ = C.toGraph G'`. Only pair, symmetrized partial-star and degree
measurements of `H′` are used. -/
theorem exists_flowCert_H {f : V → V → ℝ} (hf : C.H.Feasible f) :
    ∃ Q : Finset (Finset V), Q.card ≤ 15 * Fintype.card V ∧ ∀ G' : WeightedDiGraph V,
      Consistent G G' Q → ∀ S : Finset V,
        ∑ v ∈ S, Certificate.netOut f v ≤ (C.toGraph G').out S := by
  rw [← C.toGraph_self_eq] at hf
  exact exists_implicitFlowCert C.measures hf

/-- Transfer form on the pruned graph, local to `W` (`15 |W|` original queries). -/
theorem exists_flowTransfer_H (W : Finset V) {f : V → V → ℝ} (hf : C.H.Feasible f) :
    ∃ Q : Finset (Finset V), Q.card ≤ 15 * W.card ∧ ∀ G' : WeightedDiGraph V,
      Consistent G G' Q →
        (∃ z', Certificate.Feasible (C.toGraph G').sym z' ∧
          (∀ x ∈ W, Certificate.netOut z' x = C.H.imbalance x - 2 * Certificate.netOut f x) ∧
          (∀ u v, C.H.sym.w u v = 0 → z' u v = 0)) ∧
        ∀ x ∈ W, (C.toGraph G').imbalance x = C.H.imbalance x := by
  rw [← C.toGraph_self_eq] at hf ⊢
  exact exists_implicitFlowTransfer C.measures W hf

end PruningCert

end CutQueryComplexity.DirectedCertificate
