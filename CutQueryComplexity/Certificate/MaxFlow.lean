import CutQueryComplexity.Certificate.Flow
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Logic.Relation

/-! # Maximum flow and minimum cut with capacitated sources

A network has a source set `A`, a disjoint sink set `B`, and a source capacity
`cap x ≥ 0` bounding the net outflow at each `x ∈ A`. Vertices outside `A ∪ B`
conserve flow, and sinks have nonpositive net outflow.

* `exists_maxFlow`: some feasible network flow has value
  `∑ x ∈ A, netOut f x = c_G(S) + ∑ x ∈ A \ S, cap x` for a shore `S` avoiding `B`.

A maximum flow exists by compactness of the feasible set. The shore is the set
reachable from the unsaturated sources through residual pairs; an augmenting
walk to a sink would increase the value, so none exists. No termination
argument for augmenting paths over the reals is needed.
-/

namespace CutQueryComplexity
namespace Certificate

open WeightedGraph Filter Topology

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The unit flow along the ordered pair `(b, c)`. -/
def arc (b c : V) : V → V → ℝ := fun u v =>
  (if u = b ∧ v = c then 1 else 0) - (if u = c ∧ v = b then 1 else 0)

omit [Fintype V] in
theorem isFlow_arc (b c : V) : IsFlow (arc b c) := by
  intro u v
  simp only [arc, and_comm]
  ring

theorem netOut_arc (b c x : V) :
    netOut (arc b c) x = (if x = b then 1 else 0) - (if x = c then 1 else 0) := by
  simp only [netOut, arc, Finset.sum_sub_distrib, ite_and]
  by_cases h1 : x = b <;> by_cases h2 : x = c <;> simp [h1, h2]

omit [Fintype V] in
theorem arc_pos {b c u v : V} (h : 0 < arc b c u v) : u = b ∧ v = c := by
  simp only [arc] at h
  by_contra hne
  rw [ite_eq_right_iff.mpr (fun h' => absurd h' hne)] at h
  split at h <;> linarith

/-- A residual walk from `r` to `t` yields a unit flow from `r` to `t` on residual pairs. -/
theorem exists_walkFlow (R : V → V → Prop) {r t : V} (h : Relation.ReflTransGen R r t) :
    ∃ g : V → V → ℝ, IsFlow g ∧ (∀ u v, 0 < g u v → R u v) ∧
      ∀ x, netOut g x = (if x = r then 1 else 0) - (if x = t then 1 else 0) := by
  induction h with
  | refl =>
    refine ⟨fun _ _ => 0, fun _ _ => by simp, fun _ _ h => absurd h (lt_irrefl _), ?_⟩
    intro x; simp [netOut]
  | @tail b c _ hbc ih =>
    obtain ⟨g, hg, hpos, hnet⟩ := ih
    refine ⟨fun u v => g u v + arc b c u v, ?_, ?_, ?_⟩
    · intro u v
      show g v u + arc b c v u = -(g u v + arc b c u v)
      rw [hg u v, isFlow_arc b c u v]; ring
    · intro u v huv
      by_cases ha : 0 < arc b c u v
      · obtain ⟨rfl, rfl⟩ := arc_pos ha; exact hbc
      · exact hpos u v (by linarith)
    · intro x
      rw [netOut_add, hnet, netOut_arc]; ring

/-- A small positive perturbation stays below a strict upper bound. -/
theorem eventually_add_mul_lt {a b : ℝ} (h : a < b) (c : ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), a + ε * c < b := by
  have ht : Tendsto (fun ε : ℝ => a + ε * c) (𝓝 0) (𝓝 a) := by
    have : Continuous fun ε : ℝ => a + ε * c := by fun_prop
    simpa using this.tendsto 0
  exact (ht.eventually (gt_mem_nhds h)).filter_mono nhdsWithin_le_nhds

omit [DecidableEq V] in
/-- Pushing a little flow along residual pairs preserves feasibility. -/
theorem eventually_feasible_add {G : WeightedGraph V} {f g : V → V → ℝ}
    (hf : Feasible G f) (hg : IsFlow g) (hres : ∀ u v, 0 < g u v → f u v < G.w u v) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ u v, |f u v + ε * g u v| ≤ G.w u v := by
  rw [eventually_all]
  intro u
  rw [eventually_all]
  intro v
  have hε : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have hb := hf.2 u v
  rcases lt_trichotomy (g u v) 0 with hlt | heq | hgt
  · have hvu : f v u < G.w v u := hres v u (by rw [hg u v]; linarith)
    rw [hf.1 u v, G.symm v u] at hvu
    filter_upwards [hε, eventually_add_mul_lt hvu (-g u v)] with ε hε h
    rw [abs_le]
    constructor
    · linarith
    · nlinarith [le_abs_self (f u v)]
  · filter_upwards with ε
    rw [heq, mul_zero, add_zero]; exact hb
  · filter_upwards [hε, eventually_add_mul_lt (hres u v hgt) (g u v)] with ε hε h
    rw [abs_le]
    constructor
    · nlinarith [neg_abs_le (f u v)]
    · linarith

/-- Feasible network flows: conservation off `A ∪ B`, capacitated sources, absorbing sinks. -/
def NetworkFlows (G : WeightedGraph V) (A B : Finset V) (cap : V → ℝ) : Set (V → V → ℝ) :=
  {f | IsFlow f ∧ (∀ u v, |f u v| ≤ G.w u v) ∧ (∀ x, x ∉ A → x ∉ B → netOut f x = 0) ∧
    (∀ x ∈ A, netOut f x ≤ cap x) ∧ ∀ x ∈ B, netOut f x ≤ 0}

omit [DecidableEq V] in
theorem continuous_netOut (x : V) : Continuous fun f : V → V → ℝ => netOut f x := by
  unfold netOut
  fun_prop

omit [DecidableEq V] in
theorem isCompact_networkFlows (G : WeightedGraph V) (A B : Finset V) (cap : V → ℝ) :
    IsCompact (NetworkFlows G A B cap) := by
  have hbox : IsCompact (Set.univ.pi fun u : V => Set.univ.pi fun v : V =>
      Set.Icc (-G.w u v) (G.w u v)) :=
    isCompact_univ_pi fun u => isCompact_univ_pi fun v => isCompact_Icc
  refine hbox.of_isClosed_subset ?_ ?_
  · have hev : ∀ u v : V, Continuous fun f : V → V → ℝ => f u v := fun u v => by fun_prop
    simp only [NetworkFlows, IsFlow, Set.ofPred_and, Set.ofPred_forall]
    refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_)))
    · exact isClosed_iInter fun u => isClosed_iInter fun v =>
        isClosed_eq (hev v u) (hev u v).neg
    · exact isClosed_iInter fun u => isClosed_iInter fun v =>
        isClosed_le (hev u v).abs continuous_const
    · exact isClosed_iInter fun x => isClosed_iInter fun _ =>
        isClosed_iInter fun _ => isClosed_eq (continuous_netOut x) continuous_const
    · exact isClosed_iInter fun x => isClosed_iInter fun _ =>
        isClosed_le (continuous_netOut x) continuous_const
    · exact isClosed_iInter fun x => isClosed_iInter fun _ =>
        isClosed_le (continuous_netOut x) continuous_const
  · intro f hf
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies]
    exact fun u v => abs_le.mp (hf.2.1 u v)

/-- Max-flow/min-cut with capacitated sources `A` and absorbing sinks `B`. -/
theorem exists_maxFlow (G : WeightedGraph V) (A B : Finset V) (hAB : Disjoint A B)
    (cap : V → ℝ) (hcap : ∀ x, 0 ≤ cap x) :
    ∃ f : V → V → ℝ, ∃ S : Finset V, Feasible G f ∧
      (∀ x, x ∉ A → x ∉ B → netOut f x = 0) ∧ (∀ x ∈ A, netOut f x ≤ cap x) ∧
      (∀ x ∈ B, netOut f x ≤ 0) ∧ Disjoint S B ∧
      ∑ x ∈ A, netOut f x = G.cut S + ∑ x ∈ A \ S, cap x := by
  set K := NetworkFlows G A B cap
  have hK0 : (fun _ _ => (0 : ℝ)) ∈ K := by
    refine ⟨fun _ _ => by simp, fun u v => by simp [G.nonneg], fun _ _ _ => by simp [netOut],
      fun x _ => by simp [netOut, hcap x], fun _ _ => by simp [netOut]⟩
  have hcont : Continuous fun f : V → V → ℝ => ∑ x ∈ A, netOut f x :=
    continuous_finsetSum _ fun x _ => continuous_netOut x
  obtain ⟨f, hfK, hmax⟩ :=
    (isCompact_networkFlows G A B cap).exists_isMaxOn ⟨_, hK0⟩ hcont.continuousOn
  obtain ⟨hflow, hcapf, hcons, hsrc, hsink⟩ := hfK
  have hfeas : Feasible G f := ⟨hflow, hcapf⟩
  classical
  set Res : V → V → Prop := fun u v => f u v < G.w u v
  set Root : V → Prop := fun r => r ∈ A ∧ netOut f r < cap r
  set S : Finset V := Finset.univ.filter fun y => ∃ r, Root r ∧ Relation.ReflTransGen Res r y
  have hS : ∀ y, y ∈ S ↔ ∃ r, Root r ∧ Relation.ReflTransGen Res r y := by simp [S]
  -- No sink is reachable: otherwise augment along a residual walk.
  have hSB : Disjoint S B := by
    rw [Finset.disjoint_left]
    intro t htS htB
    obtain ⟨r, ⟨hrA, hrcap⟩, hrt⟩ := (hS t).mp htS
    have hrt' : r ≠ t := fun h => Finset.disjoint_left.mp hAB hrA (h ▸ htB)
    obtain ⟨g, hg, hgpos, hgnet⟩ := exists_walkFlow Res hrt
    have hev := (eventually_feasible_add hfeas hg hgpos).and
      ((eventually_add_mul_lt hrcap 1).and (self_mem_nhdsWithin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε))
    obtain ⟨ε, hεf, hεr, hε⟩ := hev.exists
    set f' : V → V → ℝ := fun u v => f u v + ε * g u v
    have hnet' : ∀ x, netOut f' x = netOut f x + ε * netOut g x := fun x => by
      rw [netOut_add, netOut_smul]
    have hf'K : f' ∈ K := by
      refine ⟨fun u v => ?_, hεf, fun x hxA hxB => ?_, fun x hxA => ?_, fun x hxB => ?_⟩
      · simp only [f']; rw [hflow u v, hg u v]; ring
      · have hxr : x ≠ r := fun h => hxA (h ▸ hrA)
        have hxt : x ≠ t := fun h => hxB (h ▸ htB)
        rw [hnet', hgnet, hcons x hxA hxB]; simp [hxr, hxt]
      · have hxt : x ≠ t := fun h => Finset.disjoint_left.mp hAB hxA (h ▸ htB)
        rw [hnet', hgnet]
        by_cases hxr : x = r
        · subst hxr; simp [hxt]; linarith
        · simp [hxr, hxt]; exact hsrc x hxA
      · have hxr : x ≠ r := fun h => Finset.disjoint_left.mp hAB (h ▸ hrA) hxB
        rw [hnet', hgnet]
        by_cases hxt : x = t
        · subst hxt; simp [hxr]; linarith [hsink _ hxB]
        · simp [hxr, hxt]; exact hsink x hxB
    have hval : ∑ x ∈ A, netOut f' x = ∑ x ∈ A, netOut f x + ε := by
      simp only [hnet', Finset.sum_add_distrib, ← Finset.mul_sum, hgnet, Finset.sum_sub_distrib,
        Finset.sum_ite_eq', hrA, ite_true]
      have htA : t ∉ A := fun h => Finset.disjoint_left.mp hAB h htB
      simp [htA]
    have := hmax hf'K
    simp only [Set.mem_ofPred_eq] at this
    linarith
  -- Unreached sources are saturated, and boundary pairs of `S` are saturated.
  have hsat : ∀ x ∈ A \ S, netOut f x = cap x := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    by_contra hne
    exact hx.2 ((hS x).mpr ⟨x, ⟨hx.1, lt_of_le_of_ne (hsrc x hx.1) hne⟩,
      Relation.ReflTransGen.refl⟩)
  have hbd : ∀ u ∈ S, ∀ v ∈ Sᶜ, f u v = G.w u v := by
    intro u hu v hv
    by_contra hne
    obtain ⟨r, hr, hru⟩ := (hS u).mp hu
    exact (Finset.mem_compl.mp hv) ((hS v).mpr ⟨r, hr, hru.tail
      (lt_of_le_of_ne (hfeas.le u v) hne)⟩)
  have hcutS : ∑ x ∈ S, netOut f x = G.cut S := by
    rw [sum_netOut_eq hflow, cut]
    exact Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => hbd u hu v hv
  have hSA : ∑ x ∈ S, netOut f x = ∑ x ∈ A ∩ S, netOut f x := by
    rw [Finset.inter_comm]
    refine (Finset.sum_subset Finset.inter_subset_left fun x hxS hx => ?_).symm
    have hxA : x ∉ A := fun h => hx (Finset.mem_inter.mpr ⟨hxS, h⟩)
    exact hcons x hxA (Finset.disjoint_left.mp hSB hxS)
  refine ⟨f, S, hfeas, hcons, hsrc, hsink, hSB, ?_⟩
  rw [← Finset.sum_inter_add_sum_sdiff A S, ← hSA, hcutS]
  congr 1
  exact Finset.sum_congr rfl hsat

end Certificate
end CutQueryComplexity
