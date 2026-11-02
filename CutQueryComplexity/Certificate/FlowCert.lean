import CutQueryComplexity.Certificate.MaxFlow
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Flow certificates (Lemma 5 and Remark 6)

Fix a set `W` of vertices whose net outflows are to be preserved. A feasible flow
in `G` is transferred to every graph consistent with `O(|W|)` cut queries.

* `exists_flowCert`: for every feasible flow `f` in `G` there are at most
  `8 |W|` shores such that every consistent graph carries a feasible flow with the
  same net outflow as `f` at every vertex of `W`. With `W = univ` this is Lemma 5;
  for a smaller `W` it is the local network form of Remark 6.
* `exists_cutCert`: the minimum value of a cut containing `A` and avoiding `B` is
  certified by `8 n + 1` shores.

Instead of an extreme point, the proof chooses a flow minimizing the number of
unsaturated pairs that touch `W`. If there were more than `|W|` of them, a nonzero
combination of them would have zero net outflow on `W` by rank-nullity, and pushing
it until one more pair saturates would contradict minimality.
-/

namespace CutQueryComplexity
namespace Certificate

open WeightedGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Saturating one pair -/

/-- The step size at which `a + t c` reaches `±w` in the direction of `c`. -/
noncomputable def satStep (a w c : ℝ) : ℝ := (if 0 < c then w - a else -w - a) / c

theorem satStep_spec {a w c : ℝ} (ha : |a| < w) (hc : c ≠ 0) :
    0 < satStep a w c ∧ (∀ s, 0 ≤ s → s ≤ satStep a w c → |a + s * c| ≤ w) ∧
      |a + satStep a w c * c| = w := by
  rw [abs_lt] at ha
  unfold satStep
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · have hc' : ¬ 0 < c := not_lt.mpr hneg.le
    simp only [hc', ite_false]
    have ht : (-w - a) / c * c = -w - a := div_mul_cancel₀ _ hc
    refine ⟨div_pos_of_neg_of_neg (by linarith) hneg, fun s hs hst => ?_, ?_⟩
    · have h1 : (-w - a) / c * c ≤ s * c := mul_le_mul_of_nonpos_right hst hneg.le
      have h2 : s * c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs hneg.le
      rw [abs_le]; constructor <;> linarith
    · rw [ht, show a + (-w - a) = -w by ring, abs_neg, abs_of_pos (by linarith)]
  · simp only [hpos, ite_true]
    have ht : (w - a) / c * c = w - a := div_mul_cancel₀ _ hc
    refine ⟨div_pos (by linarith) hpos, fun s hs hst => ?_, ?_⟩
    · have h1 : s * c ≤ (w - a) / c * c := mul_le_mul_of_nonneg_right hst hpos.le
      have h2 : 0 ≤ s * c := mul_nonneg hs hpos.le
      rw [abs_le]; constructor <;> linarith
    · rw [ht, show a + (w - a) = w by ring, abs_of_pos (by linarith)]

/-! ### Combinations of pairs -/

/-- The signed flow placing weight `g q` on each ordered pair `q ∈ P`. -/
def comb (P : Finset (V × V)) (g : {q // q ∈ P} → ℝ) : V → V → ℝ := fun u v =>
  ∑ q : {q // q ∈ P}, g q * arc q.1.1 q.1.2 u v

omit [Fintype V] in
theorem isFlow_comb (P : Finset (V × V)) (g : {q // q ∈ P} → ℝ) : IsFlow (comb P g) := by
  intro u v
  simp only [comb, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun q _ => by rw [isFlow_arc]; ring

theorem netOut_comb (P : Finset (V × V)) (g : {q // q ∈ P} → ℝ) (x : V) :
    netOut (comb P g) x = ∑ q : {q // q ∈ P}, g q * netOut (arc q.1.1 q.1.2) x := by
  simp only [netOut, comb, Finset.mul_sum]
  exact Finset.sum_comm

omit [Fintype V] in
theorem comb_eq_zero (P : Finset (V × V)) (g : {q // q ∈ P} → ℝ) {u v : V}
    (h1 : (u, v) ∉ P) (h2 : (v, u) ∉ P) : comb P g u v = 0 := by
  refine Finset.sum_eq_zero fun q _ => ?_
  have e1 : ¬ (u = q.1.1 ∧ v = q.1.2) := fun h => h1 (by
    have : q.1 = (u, v) := Prod.ext h.1.symm h.2.symm
    exact this ▸ q.2)
  have e2 : ¬ (u = q.1.2 ∧ v = q.1.1) := fun h => h2 (by
    have : q.1 = (v, u) := Prod.ext h.2.symm h.1.symm
    exact this ▸ q.2)
  simp [arc, e1, e2]

omit [Fintype V] in
theorem comb_apply_of_mem (P : Finset (V × V)) (g : {q // q ∈ P} → ℝ) (e : V → ℕ)
    (hP : ∀ q ∈ P, e q.1 < e q.2) (q : {q // q ∈ P}) : comb P g q.1.1 q.1.2 = g q := by
  rw [comb, Finset.sum_eq_single q]
  · have hne : ¬ (q.1.1 = q.1.2 ∧ q.1.2 = q.1.1) := fun h => by
      have := hP q.1 q.2; rw [h.1] at this; exact lt_irrefl _ this
    simp [arc, hne]
  · intro q' _ hq'
    have e1 : ¬ (q.1.1 = q'.1.1 ∧ q.1.2 = q'.1.2) := fun h =>
      hq' (Subtype.ext (Prod.ext h.1.symm h.2.symm))
    have e2 : ¬ (q.1.1 = q'.1.2 ∧ q.1.2 = q'.1.1) := fun h => by
      have h1 := hP q.1 q.2; have h2 := hP q'.1 q'.2
      rw [h.1, h.2] at h1; exact lt_asymm h1 h2
    simp [arc, e1, e2]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Net outflow on `W` of a combination of the pairs in `P`, as a linear map. -/
noncomputable def pairDiv (P : Finset (V × V)) (W : Finset V) :
    ({q // q ∈ P} → ℝ) →ₗ[ℝ] ({x // x ∈ W} → ℝ) where
  toFun g x := netOut (comb P g) x
  map_add' g h := by
    ext x; simp only [netOut_comb, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c g := by
    ext x; simp only [netOut_comb, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum, mul_assoc]

/-- More than `|W|` pairs support a nonzero combination with zero net outflow on `W`. -/
theorem exists_circulation (P : Finset (V × V)) (W : Finset V) (h : W.card < P.card) :
    ∃ g : {q // q ∈ P} → ℝ, g ≠ 0 ∧ ∀ x ∈ W, netOut (comb P g) x = 0 := by
  have hlt : Module.finrank ℝ ({x // x ∈ W} → ℝ) < Module.finrank ℝ ({q // q ∈ P} → ℝ) := by
    simpa [Module.finrank_fintype_fun_eq_card] using h
  obtain ⟨g, hg, hne⟩ := (Submodule.ne_bot_iff _).mp (LinearMap.ker_ne_bot_of_finrank_lt
    (f := pairDiv P W) hlt)
  refine ⟨g, hne, fun x hx => ?_⟩
  have := congrFun (LinearMap.mem_ker.mp hg) ⟨x, hx⟩
  exact this

/-! ### Flows with few unsaturated pairs -/

/-- Ordered (by `e`) pairs touching `W` that `h` leaves unsaturated in `G`. -/
noncomputable def unsatPairs (G : WeightedGraph V) (W : Finset V) (e : V → ℕ)
    (h : V → V → ℝ) : Finset (V × V) := by
  classical
  exact Finset.univ.filter fun p =>
    e p.1 < e p.2 ∧ (p.1 ∈ W ∨ p.2 ∈ W) ∧ |h p.1 p.2| < G.w p.1 p.2

theorem mem_unsatPairs {G : WeightedGraph V} {W : Finset V} {e : V → ℕ}
    {h : V → V → ℝ} {p : V × V} :
    p ∈ unsatPairs G W e h ↔
      e p.1 < e p.2 ∧ (p.1 ∈ W ∨ p.2 ∈ W) ∧ |h p.1 p.2| < G.w p.1 p.2 := by
  classical
  simp [unsatPairs]

/-- A feasible flow agreeing with `f` on `W` and leaving at most `|W|` touching
pairs unsaturated. -/
theorem exists_sparse_flow (G : WeightedGraph V) (W : Finset V) (e : V → ℕ)
    {f : V → V → ℝ} (hf : Feasible G f) :
    ∃ f₀, Feasible G f₀ ∧ (∀ x ∈ W, netOut f₀ x = netOut f x) ∧
      (unsatPairs G W e f₀).card ≤ W.card := by
  classical
  set Good : (V → V → ℝ) → Prop := fun h => Feasible G h ∧ ∀ x ∈ W, netOut h x = netOut f x
  have hex : ∃ k, ∃ h, Good h ∧ (unsatPairs G W e h).card = k :=
    ⟨_, f, ⟨hf, fun _ _ => rfl⟩, rfl⟩
  obtain ⟨f₀, ⟨hf₀, hnet₀⟩, hk⟩ := Nat.find_spec hex
  have hmin : ∀ h, Good h → Nat.find hex ≤ (unsatPairs G W e h).card :=
    fun h hh => Nat.find_min' hex ⟨h, hh, rfl⟩
  refine ⟨f₀, hf₀, hnet₀, ?_⟩
  by_contra hlt
  push Not at hlt
  set P := unsatPairs G W e f₀
  have hPord : ∀ q ∈ P, e q.1 < e q.2 := fun q hq => (mem_unsatPairs.mp hq).1
  obtain ⟨g, hg0, hgW⟩ := exists_circulation P W hlt
  set c := comb P g
  have hc : IsFlow c := isFlow_comb P g
  -- Some pair of `P` carries the combination.
  obtain ⟨q₀, hq₀⟩ : ∃ q, g q ≠ 0 := by
    by_contra hall; push Not at hall; exact hg0 (funext hall)
  set P' := P.filter fun q => c q.1 q.2 ≠ 0
  have hP'ne : P'.Nonempty := ⟨q₀.1, Finset.mem_filter.mpr ⟨q₀.2, by
    rw [show c = comb P g from rfl, comb_apply_of_mem P g e hPord q₀]; exact hq₀⟩⟩
  set T : V × V → ℝ := fun q => satStep (f₀ q.1 q.2) (G.w q.1 q.2) (c q.1 q.2)
  obtain ⟨qs, hqsP', hqsmin⟩ := Finset.exists_min_image P' T hP'ne
  have hqs := Finset.mem_filter.mp hqsP'
  have hqsU := (mem_unsatPairs (G := G) (W := W) (e := e) (h := f₀)).mp hqs.1
  obtain ⟨htpos, -, htsat⟩ := satStep_spec hqsU.2.2 hqs.2
  set t := T qs
  set f₁ : V → V → ℝ := fun u v => f₀ u v + t * c u v
  -- Feasibility on a pair of `P`.
  have hfeasP : ∀ u v, (u, v) ∈ P → |f₁ u v| ≤ G.w u v := by
    intro u v huv
    by_cases hcz : c u v = 0
    · simp only [f₁, hcz, mul_zero, add_zero]; exact hf₀.2 u v
    · have hmem : (u, v) ∈ P' := Finset.mem_filter.mpr ⟨huv, hcz⟩
      exact (satStep_spec (mem_unsatPairs.mp huv).2.2 hcz).2.1 t htpos.le (hqsmin _ hmem)
  have hf₁ : Feasible G f₁ := by
    refine ⟨fun u v => by simp only [f₁]; rw [hf₀.1 u v, hc u v]; ring, fun u v => ?_⟩
    by_cases h1 : (u, v) ∈ P
    · exact hfeasP u v h1
    by_cases h2 : (v, u) ∈ P
    · have := hfeasP v u h2
      have e1 : f₁ v u = -f₁ u v := by simp only [f₁]; rw [hf₀.1 u v, hc u v]; ring
      rwa [e1, abs_neg, G.symm] at this
    · have hz : c u v = 0 := comb_eq_zero P g h1 h2
      simp only [f₁, hz, mul_zero, add_zero]; exact hf₀.2 u v
  have hgood : Good f₁ := ⟨hf₁, fun x hx => by
    rw [netOut_add, netOut_smul, hgW x hx, mul_zero, add_zero, hnet₀ x hx]⟩
  -- The unsaturated pairs of `f₁` lie in `P` minus the newly saturated pair.
  have hsub : unsatPairs G W e f₁ ⊆ P.erase qs := by
    intro p hp
    have hp' := mem_unsatPairs.mp hp
    have hpP : p ∈ P := by
      by_cases hcz : c p.1 p.2 = 0
      · refine mem_unsatPairs.mpr ⟨hp'.1, hp'.2.1, ?_⟩
        have := hp'.2.2; simp only [f₁, hcz, mul_zero, add_zero] at this; exact this
      · by_contra hpP
        have hsw : (p.2, p.1) ∈ P := by
          by_contra hsw; exact hcz (comb_eq_zero P g hpP hsw)
        exact lt_asymm hp'.1 (hPord _ hsw)
    refine Finset.mem_erase.mpr ⟨fun hpq => ?_, hpP⟩
    subst hpq
    have := hp'.2.2
    simp only [f₁] at this
    rw [htsat] at this
    exact lt_irrefl _ this
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hqs.1] at hcard
  have := hmin f₁ hgood
  have hPpos : 0 < P.card := Finset.card_pos.mpr ⟨_, hqs.1⟩
  omega

/-! ### The certificate -/

/-- Saturated pairs leaving `x` in the flow direction. -/
noncomputable def satOut (G : WeightedGraph V) (f : V → V → ℝ) (x : V) : Finset V := by
  classical
  exact Finset.univ.filter fun u => ¬ |f x u| < G.w x u ∧ 0 < f x u

/-- Saturated pairs entering `x` in the flow direction. -/
noncomputable def satIn (G : WeightedGraph V) (f : V → V → ℝ) (x : V) : Finset V := by
  classical
  exact Finset.univ.filter fun u => ¬ |f x u| < G.w x u ∧ f x u < 0

/-- The shores of the flow certificate. -/
noncomputable def flowCertQueries (G : WeightedGraph V) (W : Finset V) (f : V → V → ℝ)
    (P : Finset (V × V)) : Finset (Finset V) :=
  W.image (fun x => {x}) ∪ W.image (satOut G f) ∪ W.image (fun x => insert x (satOut G f x)) ∪
    W.image (satIn G f) ∪ W.image (fun x => insert x (satIn G f x)) ∪
    P.image (fun p => {p.1}) ∪ P.image (fun p => {p.2}) ∪ P.image (fun p => {p.1, p.2})

theorem card_flowCertQueries_le (G : WeightedGraph V) (W : Finset V) (f : V → V → ℝ)
    (P : Finset (V × V)) :
    (flowCertQueries G W f P).card ≤ 5 * W.card + 3 * P.card := by
  unfold flowCertQueries
  refine (Finset.card_union_le _ _).trans ?_
  refine (Nat.add_le_add_right (Finset.card_union_le _ _) _).trans ?_
  refine (Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _).trans ?_
  refine (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
    (Finset.card_union_le _ _) _) _) _).trans ?_
  refine (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_right (Finset.card_union_le _ _) _) _) _) _).trans ?_
  refine (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _) _) _) _).trans ?_
  refine (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
      (Finset.card_union_le _ _) _) _) _) _) _) _).trans ?_
  have := Finset.card_image_le (s := W) (f := fun x => ({x} : Finset V))
  have := Finset.card_image_le (s := W) (f := satOut G f)
  have := Finset.card_image_le (s := W) (f := fun x => insert x (satOut G f x))
  have := Finset.card_image_le (s := W) (f := satIn G f)
  have := Finset.card_image_le (s := W) (f := fun x => insert x (satIn G f x))
  have := Finset.card_image_le (s := P) (f := fun p => ({p.1} : Finset V))
  have := Finset.card_image_le (s := P) (f := fun p => ({p.2} : Finset V))
  have := Finset.card_image_le (s := P) (f := fun p => ({p.1, p.2} : Finset V))
  omega

/-- The transferred flow in a consistent graph `G'`. -/
noncomputable def transferFlow (G G' : WeightedGraph V) (W : Finset V) (f : V → V → ℝ) :
    V → V → ℝ := by
  classical
  exact fun u v => if u ∈ W ∨ v ∈ W then
    (if |f u v| < G.w u v then f u v else f u v / G.w u v * G'.w u v) else 0

omit [Fintype V] [DecidableEq V] in
theorem abs_div_le_one {a w : ℝ} (h : |a| ≤ w) : |a / w| ≤ 1 := by
  rcases (abs_nonneg a).trans h |>.eq_or_lt with hw | hw
  · rw [← hw, div_zero, abs_zero]; exact zero_le_one
  · rw [abs_div, abs_of_pos hw]; exact (div_le_one hw).mpr h

/-- Lemma 5 / Remark 6: `8 |W|` shores transfer a feasible flow's net outflows on `W`. -/
theorem exists_flowCert (G : WeightedGraph V) (W : Finset V) {f : V → V → ℝ}
    (hf : Feasible G f) :
    ∃ Q : Finset (Finset V), Q.card ≤ 8 * W.card ∧ ∀ G' : WeightedGraph V,
      Consistent G G' Q → ∃ f', Feasible G' f' ∧ ∀ x ∈ W, netOut f' x = netOut f x := by
  classical
  set e : V → ℕ := fun v => (Fintype.equivFin V v : ℕ)
  have he : Function.Injective e := Fin.val_injective.comp (Fintype.equivFin V).injective
  obtain ⟨f₀, hf₀, hnet₀, hP⟩ := exists_sparse_flow G W e hf
  set P := unsatPairs G W e f₀
  refine ⟨flowCertQueries G W f₀ P, (card_flowCertQueries_le G W f₀ P).trans (by omega),
    fun G' hG' => ?_⟩
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
  -- Unsaturated touching pairs keep their capacity.
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
  refine ⟨f', ⟨fun u v => ?_, fun u v => ?_⟩, fun x hx => ?_⟩
  · -- antisymmetry
    simp only [f', transferFlow, or_comm (a := v ∈ W), hf₀.1 u v, abs_neg, G.symm v u,
      G'.symm v u]
    split_ifs <;> ring
  · -- capacities
    simp only [f', transferFlow]
    split_ifs with h1 h2
    · rw [hw u v h1 h2]; exact h2.le
    · rw [abs_mul, abs_of_nonneg (G'.nonneg u v)]
      exact mul_le_of_le_one_left (G'.nonneg u v) (abs_div_le_one (hf₀.2 u v))
    · simp [G'.nonneg]
  · -- net outflow at a vertex of `W`
    have hxO : x ∉ satOut G f₀ x := by simp [satOut, hf₀.1.self]
    have hxI : x ∉ satIn G f₀ x := by simp [satIn, hf₀.1.self]
    have hO := hG'.cross_eq (Finset.disjoint_singleton_left.mpr hxO) (mA x hx) (mB x hx)
      (by rw [← Finset.insert_eq]; exact mC x hx)
    have hI := hG'.cross_eq (Finset.disjoint_singleton_left.mpr hxI) (mA x hx) (mD x hx)
      (by rw [← Finset.insert_eq]; exact mE x hx)
    simp only [cross, Finset.sum_singleton] at hO hI
    -- Split each term into its unsaturated, outgoing, and incoming parts.
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
    rw [← hnet₀ x hx]
    simp only [netOut]
    rw [h1, h2, hO, hI]

/-! ### Separating cuts -/

/-- Lemma 5, terminal form: the minimum `A`–`B` separating cut value is certified. -/
theorem exists_cutCert (G : WeightedGraph V) (A B : Finset V) (hAB : Disjoint A B) :
    ∃ T : Finset V, A ⊆ T ∧ Disjoint T B ∧ ∃ Q : Finset (Finset V), T ∈ Q ∧
      Q.card ≤ 8 * Fintype.card V + 1 ∧ ∀ G' : WeightedGraph V, Consistent G G' Q →
        ∀ S, A ⊆ S → Disjoint S B → G'.cut T ≤ G'.cut S := by
  obtain ⟨f, S₀, hf, hcons, -, -, hS₀B, hval⟩ :=
    exists_maxFlow G A B hAB G.degree (fun x => Finset.sum_nonneg fun u _ => G.nonneg x u)
  set T := S₀ ∪ A
  have hTB : Disjoint T B := Finset.disjoint_union_left.mpr ⟨hS₀B, hAB⟩
  -- Flow through any separating shore equals the flow value.
  have hsum : ∀ S, A ⊆ S → Disjoint S B →
      ∑ x ∈ S, netOut f x = ∑ x ∈ A, netOut f x := by
    intro S hAS hSB
    refine (Finset.sum_subset hAS fun x hxS hxA => ?_).symm
    exact hcons x hxA (Finset.disjoint_left.mp hSB hxS)
  have hTval : G.cut T = ∑ x ∈ A, netOut f x := by
    refine le_antisymm ?_ ?_
    · rw [hval]; exact cut_union_le G S₀ A
    · rw [← hsum T Finset.subset_union_right hTB]; exact sum_netOut_le_cut hf T
  obtain ⟨Q₀, hQ₀, hcert⟩ := exists_flowCert G Finset.univ hf
  refine ⟨T, Finset.subset_union_right, hTB, insert T Q₀, Finset.mem_insert_self _ _, ?_,
    fun G' hG' S hAS hSB => ?_⟩
  · refine (Finset.card_insert_le _ _).trans ?_
    simp only [Finset.card_univ] at hQ₀; omega
  · obtain ⟨f', hf', hnet'⟩ := hcert G' (hG'.mono (Finset.subset_insert _ _))
    have hT' : G'.cut T = G.cut T := hG' T (Finset.mem_insert_self _ _)
    have := sum_netOut_le_cut hf' S
    rw [Finset.sum_congr rfl fun x _ => hnet' x (Finset.mem_univ x), hsum S hAS hSB] at this
    linarith

end Certificate
end CutQueryComplexity
