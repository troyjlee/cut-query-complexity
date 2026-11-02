import CutQueryComplexity.DirectedCertificate.FlowCert

/-! # A cut-equivalent orientation with few split pairs (W5; `lem:orientation`)

`exists_orientationCert`: at most `18 n` queries certify an implicit `G°` with the cut function
of `G`. There are at most `n` exceptional unordered pairs, and the data that pruning needs is
packaged in `OrientationCert`:
* on an ordinary positive pair, the prescribed arc carries the competitor's symmetrized
  capacity and the reverse arc carries `0` (`toGraph_ord`);
* exceptional arcs are fixed constants (`toGraph_c_exc`, `exc_w`);
* originally zero pairs get half the competitor's capacity each way (`toGraph_c_zero`);
* every consistent `G'` gives a nonnegative `G°′ = O.toGraph G'` with exactly the cut function
  of `G'` (`out_eq`).

`transferFlow_spec` exposes the transfer step of the undirected flow certificate
(`Certificate.exists_flowCert`), with the sparse flow and the transferred flow explicit.
-/

namespace CutQueryComplexity.DirectedCertificate

open Finset WeightedDiGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Exposed transfer step of the undirected flow certificate

`Certificate.exists_flowCert` hides its sparse flow and its transferred flow. The orientation
needs both, so the transfer part of its proof is restated here with explicit data
(copy-adapted from `CutQueryComplexity/Certificate/FlowCert.lean`). -/

section Transfer
open Certificate WeightedGraph

/-- The transfer step of `exists_flowCert`, with the flow `f₀`, the shores, and the
transferred flow `transferFlow G G' W f₀` explicit. No sparsity is needed here. -/
theorem transferFlow_spec (G : WeightedGraph V) (W : Finset V) {e : V → ℕ}
    (he : Function.Injective e) {f₀ : V → V → ℝ} (hf₀ : Certificate.Feasible G f₀)
    (G' : WeightedGraph V)
    (hG' : Certificate.Consistent G G' (flowCertQueries G W f₀ (unsatPairs G W e f₀))) :
    Certificate.Feasible G' (transferFlow G G' W f₀) ∧
      (∀ x ∈ W, Certificate.netOut (transferFlow G G' W f₀) x = Certificate.netOut f₀ x) ∧
      (∀ u v, (u ∈ W ∨ v ∈ W) → |f₀ u v| < G.w u v → G'.w u v = G.w u v) := by
  classical
  set P := unsatPairs G W e f₀
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
  have hw : ∀ u v, (u ∈ W ∨ v ∈ W) → |f₀ u v| < G.w u v → G'.w u v = G.w u v := by
    intro u v huv hlt
    have hne : u ≠ v := fun h => by subst h; rw [G.diag, hf₀.1.self] at hlt; simp at hlt
    rcases lt_or_gt_of_ne (fun h => hne (he h)) with hlt' | hgt'
    · have hp : (u, v) ∈ P := mem_unsatPairs.mpr ⟨hlt', huv, hlt⟩
      exact hG'.w_eq hne (mF _ hp) (mG _ hp) (mH _ hp)
    · have hp : (v, u) ∈ P := mem_unsatPairs.mpr ⟨hgt', huv.symm, by
        rw [hf₀.1 u v, abs_neg, G.symm]; exact hlt⟩
      rw [G'.symm, G.symm]
      exact hG'.w_eq (Ne.symm hne) (mF _ hp) (mG _ hp) (mH _ hp)
  set f' := transferFlow G G' W f₀
  refine ⟨⟨fun u v => ?_, fun u v => ?_⟩, fun x hx => ?_, hw⟩
  · simp only [f', transferFlow, or_comm (a := v ∈ W), hf₀.1 u v, abs_neg, G.symm v u,
      G'.symm v u]
    split_ifs <;> ring
  · simp only [f', transferFlow]
    split_ifs with h1 h2
    · rw [hw u v h1 h2]; exact h2.le
    · rw [abs_mul, abs_of_nonneg (G'.nonneg u v)]
      exact mul_le_of_le_one_left (G'.nonneg u v) (abs_div_le_one (hf₀.2 u v))
    · simp [G'.nonneg]
  · have hxO : x ∉ satOut G f₀ x := by simp [satOut, hf₀.1.self]
    have hxI : x ∉ satIn G f₀ x := by simp [satIn, hf₀.1.self]
    have hO := hG'.cross_eq (Finset.disjoint_singleton_left.mpr hxO) (mA x hx) (mB x hx)
      (by rw [← Finset.insert_eq]; exact mC x hx)
    have hI := hG'.cross_eq (Finset.disjoint_singleton_left.mpr hxI) (mA x hx) (mD x hx)
      (by rw [← Finset.insert_eq]; exact mE x hx)
    simp only [cross, Finset.sum_singleton] at hO hI
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

end Transfer

/-! ## `lem:orientation`: the orientation data -/

/-- `IsExc E u v`: the unordered pair `{u, v}` is exceptional (listed once, in either order). -/
def IsExc (E : Finset (V × V)) (u v : V) : Prop := (u, v) ∈ E ∨ (v, u) ∈ E

instance (E : Finset (V × V)) (u v : V) : Decidable (IsExc E u v) :=
  inferInstanceAs (Decidable (_ ∨ _))

omit [Fintype V] [DecidableEq V] in
theorem IsExc.symm {E : Finset (V × V)} {u v : V} (h : IsExc E u v) : IsExc E v u :=
  Or.symm h

omit [Fintype V] [DecidableEq V] in
theorem isExc_comm {E : Finset (V × V)} {u v : V} : IsExc E u v ↔ IsExc E v u :=
  ⟨IsExc.symm, IsExc.symm⟩

/-- The sign/mask data of a cut-equivalent orientation of `G`, together with the
queries that freeze it. The implicit graph is `OrientationData.toGraph`:
* on an exceptional pair (`IsExc E u v`) the arc `u → v` has the fixed constant `k u v`;
* on every other pair it is `(1 + sgn u v)/2 · u'_{uv}`, where `u' = G'.sym.w`.
On an ordinary originally positive pair `sgn = ±1` (one prescribed direction carries all of
`u'`); on an originally zero pair `sgn = 0` (`u'/2` each way). -/
structure OrientationData (G : WeightedDiGraph V) where
  /-- The certificate's outgoing-cut queries. -/
  queries : Finset (Finset V)
  card_queries : queries.card ≤ 18 * Fintype.card V
  /-- Exceptional unordered pairs, each listed once. -/
  E : Finset (V × V)
  card_E : E.card ≤ Fintype.card V
  E_ne : ∀ p ∈ E, p.1 ≠ p.2
  /-- No pair is listed in both orders. -/
  E_asymm : ∀ p ∈ E, (p.2, p.1) ∉ E
  /-- The prescribed (normalized) sign `z_{uv}/u_{uv}`, in `[-1, 1]`. -/
  sgn : V → V → ℝ
  sgn_antisymm : ∀ u v, sgn v u = -sgn u v
  abs_sgn_le : ∀ u v, |sgn u v| ≤ 1
  /-- Ordinary originally positive pairs are fully oriented. -/
  sgn_ord : ∀ u v, ¬ IsExc E u v → 0 < G.sym.w u v → sgn u v = 1 ∨ sgn u v = -1
  /-- Originally zero pairs carry no sign. -/
  sgn_zero : ∀ u v, G.sym.w u v = 0 → sgn u v = 0
  /-- Fixed exceptional arc capacities. -/
  k : V → V → ℝ
  k_nonneg : ∀ u v, 0 ≤ k u v
  k_add : ∀ u v, IsExc E u v → k u v + k v u = G.sym.w u v
  /-- Exceptional pairs are originally positive. -/
  exc_pos : ∀ u v, IsExc E u v → 0 < G.sym.w u v
  /-- The queries fix the symmetrized capacity of every exceptional pair. -/
  exc_w : ∀ G' : WeightedDiGraph V, Consistent G G' queries →
    ∀ u v, IsExc E u v → G'.sym.w u v = G.sym.w u v
  /-- The queries contain the degree queries. -/
  degree_sub : degreeQueries V ⊆ queries

namespace OrientationData
variable {G : WeightedDiGraph V} (O : OrientationData G)

theorem not_isExc_self (v : V) : ¬ IsExc O.E v v := by
  rintro (h | h) <;> exact O.E_ne _ h rfl

noncomputable section

/-- Capacity of the implicit orientation built from `G'`. -/
def cap (G' : WeightedDiGraph V) (u v : V) : ℝ :=
  if IsExc O.E u v then O.k u v else (1 + O.sgn u v) / 2 * G'.sym.w u v

/-- The implicit orientation `G°′` of a competitor `G'` (`G° = O.toGraph G`). It is a
nonnegative digraph for every `G'`. -/
def toGraph (G' : WeightedDiGraph V) : WeightedDiGraph V where
  c := O.cap G'
  nonneg u v := by
    unfold cap
    split_ifs
    · exact O.k_nonneg u v
    · have := (abs_le.mp (O.abs_sgn_le u v)).1
      exact mul_nonneg (by linarith) (G'.sym.nonneg u v)
  diag v := by simp [cap, O.not_isExc_self v, G'.diag]

theorem toGraph_c (G' : WeightedDiGraph V) (u v : V) :
    (O.toGraph G').c u v =
      if IsExc O.E u v then O.k u v else (1 + O.sgn u v) / 2 * G'.sym.w u v := rfl

theorem toGraph_c_exc (G' : WeightedDiGraph V) {u v : V} (h : IsExc O.E u v) :
    (O.toGraph G').c u v = O.k u v := by simp [toGraph_c, h]

/-- Prescribed arc of an ordinary pair: all of `u'`. -/
theorem toGraph_c_pos (G' : WeightedDiGraph V) {u v : V} (h : ¬ IsExc O.E u v)
    (hs : O.sgn u v = 1) : (O.toGraph G').c u v = G'.sym.w u v := by
  simp [toGraph_c, h, hs]

/-- Reverse of the prescribed arc: zero. -/
theorem toGraph_c_neg (G' : WeightedDiGraph V) {u v : V} (h : ¬ IsExc O.E u v)
    (hs : O.sgn u v = -1) : (O.toGraph G').c u v = 0 := by
  simp [toGraph_c, h, hs]

/-- An ordinary originally positive pair: one arc is `u'`, the reverse is `0`. -/
theorem toGraph_ord (G' : WeightedDiGraph V) {u v : V} (h : ¬ IsExc O.E u v)
    (hpos : 0 < G.sym.w u v) :
    ((O.toGraph G').c u v = G'.sym.w u v ∧ (O.toGraph G').c v u = 0) ∨
      ((O.toGraph G').c u v = 0 ∧ (O.toGraph G').c v u = G'.sym.w u v) := by
  have h' : ¬ IsExc O.E v u := fun h2 => h h2.symm
  rcases O.sgn_ord u v h hpos with hs | hs
  · left
    refine ⟨O.toGraph_c_pos G' h hs, O.toGraph_c_neg G' h' ?_⟩
    rw [O.sgn_antisymm, hs]
  · right
    refine ⟨O.toGraph_c_neg G' h hs, ?_⟩
    rw [O.toGraph_c_pos G' h' (by rw [O.sgn_antisymm, hs]; norm_num), G'.sym.symm]

/-- An originally zero pair splits `u'` evenly. -/
theorem toGraph_c_zero (G' : WeightedDiGraph V) {u v : V} (h0 : G.sym.w u v = 0) :
    (O.toGraph G').c u v = G'.sym.w u v / 2 := by
  have h : ¬ IsExc O.E u v := fun h => by have := O.exc_pos u v h; linarith
  simp [toGraph_c, h, O.sgn_zero u v h0]; ring

/-- For a consistent `G'`, `G°′` has symmetrization `G'.sym`. -/
theorem toGraph_sym_w {G' : WeightedDiGraph V} (hG' : Consistent G G' O.queries) (u v : V) :
    (O.toGraph G').sym.w u v = G'.sym.w u v := by
  rw [sym_w, toGraph_c, toGraph_c]
  by_cases h : IsExc O.E u v
  · have h' : IsExc O.E v u := h.symm
    simp only [h, h', ↓reduceIte]
    rw [O.k_add u v h, O.exc_w G' hG' u v h]
  · have h' : ¬ IsExc O.E v u := fun h2 => h h2.symm
    simp only [h, h', ↓reduceIte]
    rw [O.sgn_antisymm, G'.sym.symm v u]; ring

theorem degrees_eq {G' : WeightedDiGraph V} (hG' : Consistent G G' O.queries) (v : V) :
    G'.outdeg v = G.outdeg v ∧ G'.indeg v = G.indeg v ∧ G'.imbalance v = G.imbalance v :=
  degrees_eq_of_consistent (hG'.mono O.degree_sub) v

end

end OrientationData

/-- **`lem:orientation`** package: the data plus the exact cut-function equality for every
consistent competitor. Applied to `G` itself it gives `G°` (`out_toGraph_self`). -/
structure OrientationCert (G : WeightedDiGraph V) extends OrientationData G where
  out_eq : ∀ G' : WeightedDiGraph V, Consistent G G' queries →
    ∀ S, (toOrientationData.toGraph G').out S = G'.out S

namespace OrientationCert
variable {G : WeightedDiGraph V} (O : OrientationCert G)

/-- `G°` has the cut function of `G`. -/
theorem out_toGraph_self (S : Finset V) : (O.toGraph G).out S = G.out S :=
  O.out_eq G (Consistent.refl G _) S

end OrientationCert

/-! ## Construction of the orientation -/

section Construction
open Certificate

/-- **`lem:orientation`**: every `G` has an orientation certificate with at most `18 n`
queries and at most `n` exceptional unordered pairs. -/
theorem exists_orientationCert (G : WeightedDiGraph V) : Nonempty (OrientationCert G) := by
  classical
  set e : V → ℕ := fun v => (Fintype.equivFin V v : ℕ)
  have he : Function.Injective e := Fin.val_injective.comp (Fintype.equivFin V).injective
  have hf0 : G.Feasible (fun _ _ => 0) := ⟨fun _ _ => by simp, fun u v => G.nonneg u v⟩
  obtain ⟨z, hz, hnet, hP⟩ :=
    exists_sparse_flow G.sym Finset.univ e (feasible_flowShift hf0)
  set P := unsatPairs G.sym Finset.univ e z
  set Q₀ := flowCertQueries G.sym Finset.univ z P
  set Q := symQueries Q₀ ∪ degreeQueries V
  -- exceptional = unsaturated
  have hexc : ∀ u v, IsExc P u v ↔ |z u v| < G.sym.w u v := by
    intro u v
    simp only [IsExc, P, mem_unsatPairs, Finset.mem_univ, true_or, true_and]
    constructor
    · rintro (h | h)
      · exact h.2
      · rw [hz.1 v u, abs_neg, G.sym.symm]; exact h.2
    · intro h
      have hne : u ≠ v := fun huv => by
        subst huv; rw [G.sym.diag, hz.1.self] at h; simp at h
      rcases lt_or_gt_of_ne (fun h' => hne (he h')) with h1 | h1
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr ⟨h1, by rw [hz.1 u v, abs_neg, G.sym.symm]; exact h⟩
  have hnet' : ∀ v, netOut z v = G.imbalance v := fun v => by
    rw [hnet v (Finset.mem_univ v), netOut_flowShift]; simp [netOut]
  have hQcard : Q.card ≤ 18 * Fintype.card V := by
    show (symQueries Q₀ ∪ degreeQueries V).card ≤ _
    have h1 : Q₀.card ≤ 5 * (Finset.univ : Finset V).card + 3 * P.card :=
      card_flowCertQueries_le G.sym Finset.univ z P
    have := symQueries_card Q₀
    have := degreeQueries_card (V := V)
    have := Finset.card_union_le (symQueries Q₀) (degreeQueries V)
    rw [Finset.card_univ] at hP h1
    omega
  have htr : ∀ G' : WeightedDiGraph V, Consistent G G' Q →
      Certificate.Feasible G'.sym (transferFlow G.sym G'.sym Finset.univ z) ∧
      (∀ x, netOut (transferFlow G.sym G'.sym Finset.univ z) x = G.imbalance x) ∧
      (∀ u v, |z u v| < G.sym.w u v → G'.sym.w u v = G.sym.w u v) := by
    intro G' hG'
    obtain ⟨h1, h2, h3⟩ := transferFlow_spec G.sym Finset.univ he hz G'.sym
      (Consistent.sym (hG'.mono Finset.subset_union_left))
    exact ⟨h1, fun x => by rw [h2 x (Finset.mem_univ x), hnet'],
      fun u v h => h3 u v (Or.inl (Finset.mem_univ u)) h⟩
  let D : OrientationData G :=
    { queries := Q
      card_queries := hQcard
      E := P
      card_E := by simpa using hP
      E_ne := fun p hp h => by
        have := (mem_unsatPairs.mp hp).1; rw [h] at this; exact lt_irrefl _ this
      E_asymm := fun p hp hp' =>
        lt_asymm (mem_unsatPairs.mp hp).1 (mem_unsatPairs.mp hp').1
      sgn := fun u v => z u v / G.sym.w u v
      sgn_antisymm := fun u v => by rw [hz.1 u v, G.sym.symm v u, neg_div]
      abs_sgn_le := fun u v => abs_div_le_one (hz.2 u v)
      sgn_ord := fun u v hu hpos => by
        have hsat : |z u v| = G.sym.w u v :=
          le_antisymm (hz.2 u v) (not_lt.mp fun h => hu ((hexc u v).mpr h))
        rcases abs_eq hpos.le |>.mp hsat with h | h
        · left; rw [h, div_self hpos.ne']
        · right; rw [h, neg_div, div_self hpos.ne']
      sgn_zero := fun u v h0 => by rw [h0, div_zero]
      k := fun u v => (G.sym.w u v + z u v) / 2
      k_nonneg := fun u v => by
        have := (abs_le.mp (hz.2 u v)).1; linarith
      k_add := fun u v _ => by rw [hz.1 u v, G.sym.symm v u]; ring
      exc_pos := fun u v h => lt_of_le_of_lt (abs_nonneg _) ((hexc u v).mp h)
      exc_w := fun G' hG' u v h => (htr G' hG').2.2 u v ((hexc u v).mp h)
      degree_sub := Finset.subset_union_right }
  refine ⟨{ D with out_eq := fun G' hG' S => ?_ }⟩
  obtain ⟨hf', hnet'', hw⟩ := htr G' hG'
  set z' := transferFlow G.sym G'.sym Finset.univ z
  -- `G°′` is `(u' + z')/2`.
  have hcap : ∀ u v, (D.toGraph G').c u v = (G'.sym.w u v + z' u v) / 2 := by
    intro u v
    rw [D.toGraph_c]
    simp only [D, z', transferFlow, Finset.mem_univ, true_or, ↓reduceIte]
    by_cases h : |z u v| < G.sym.w u v
    · simp only [(hexc u v).mpr h, h, ↓reduceIte, hw u v h]
    · have h' : ¬ IsExc P u v := fun h' => h ((hexc u v).mp h')
      simp only [h', h, ↓reduceIte]; ring
  refine out_eq_of_sym_imbalance (D.toGraph_sym_w hG') (fun v => ?_) S
  rw [(D.degrees_eq hG' v).2.2, ← hnet'' v, imbalance, outdeg, indeg, netOut,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [hcap, hcap, hf'.1 v w, G'.sym.symm w v]; ring

end Construction

end CutQueryComplexity.DirectedCertificate
