import CutQueryComplexity.Certificate.MaxFlow
import CutQueryComplexity.Graph.WeightedDirected

/-! # Real-capacity directed max-flow/min-cut and supplies to a root set (W1)

Signed antisymmetric flows `f` with `f u v ≤ c u v`, following `DirectedMincut.FlowDuality`.

* `sum_netOut_le_out`, `netOut_le_out`: weak duality.
* `exists_maxFlow_network`: max-flow/min-cut with capacitated sources `A` and absorbing sinks
  `B`, by compactness and residual reachability (no integrality).
* `exists_maxFlow_minCut`, `maxFlow_minCut`: `s`–`t` strong duality.
* `supply_iff`: supplies `b ≥ 0` outside `R` can all be routed into `R` iff
  `b(S) ≤ F(S)` for every root-avoiding `S`.
* `demand_iff`: the reverse form, `R` feeding demands `b` outside `R`, iff `b(S) ≤ F(Sᶜ)`.
* `uniform_supply_iff`, `uniform_demand_iff`: the W4 shared-flow forms with `β |S|`.
-/

namespace CutQueryComplexity.DirectedCertificate

namespace WeightedDiGraph

open Finset Filter Topology Certificate

variable {V : Type*} [Fintype V] [DecidableEq V] (G : WeightedDiGraph V)

theorem out_nonneg (S : Finset V) : 0 ≤ G.out S :=
  sum_nonneg fun u _ => sum_nonneg fun v _ => G.nonneg u v

/-- A feasible signed flow: antisymmetric and below the capacity on every ordered pair. -/
def Feasible (f : V → V → ℝ) : Prop := IsFlow f ∧ ∀ u v, f u v ≤ G.c u v

/-- A feasible `s`–`t` flow: conservation at every vertex other than `s` and `t`. -/
def STFlow (s t : V) (f : V → V → ℝ) : Prop :=
  G.Feasible f ∧ ∀ x, x ≠ s → x ≠ t → netOut f x = 0

variable {G}

/-- **Weak duality**, set form: the net outflow of `S` is at most its outgoing cut. -/
theorem sum_netOut_le_out {f : V → V → ℝ} (hf : G.Feasible f) (S : Finset V) :
    ∑ x ∈ S, netOut f x ≤ G.out S := by
  rw [sum_netOut_eq hf.1]
  exact sum_le_sum fun u _ => sum_le_sum fun v _ => hf.2 u v

/-- **Weak duality** for `s`–`t` flows. -/
theorem netOut_le_out {s t : V} {f : V → V → ℝ} (hf : G.STFlow s t f) {S : Finset V}
    (hs : s ∈ S) (ht : t ∉ S) : netOut f s ≤ G.out S := by
  have hsum : ∑ x ∈ S, netOut f x = netOut f s := by
    rw [← sum_erase_add _ _ hs]
    have : ∑ x ∈ S.erase s, netOut f x = 0 := sum_eq_zero fun x hx =>
      hf.2 x (ne_of_mem_erase hx) fun h => ht (h ▸ mem_of_mem_erase hx)
    rw [this, zero_add]
  rw [← hsum]
  exact sum_netOut_le_out hf.1 S

omit [DecidableEq V] in
/-- The net outflows of a signed flow sum to zero. -/
theorem sum_univ_netOut {f : V → V → ℝ} (hf : IsFlow f) : ∑ x, netOut f x = 0 := by
  classical
  rw [sum_netOut_eq hf]
  simp

omit [DecidableEq V] in
/-- Pushing a little flow along residual pairs preserves feasibility. -/
theorem eventually_feasible_add {f g : V → V → ℝ} (hf : G.Feasible f) (hg : IsFlow g)
    (hres : ∀ u v, 0 < g u v → f u v < G.c u v) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), G.Feasible fun u v => f u v + ε * g u v := by
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ u v, f u v + ε * g u v ≤ G.c u v := by
    rw [eventually_all]; intro u
    rw [eventually_all]; intro v
    have hε : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
    by_cases hgv : 0 < g u v
    · filter_upwards [eventually_add_mul_lt (hres u v hgv) (g u v)] with ε h
      exact h.le
    · filter_upwards [hε] with ε hε
      nlinarith [hf.2 u v]
  filter_upwards [hev] with ε hε
  refine ⟨fun u v => ?_, hε⟩
  show f v u + ε * g v u = -(f u v + ε * g u v)
  rw [hf.1 u v, hg u v]; ring

variable (G)

/-- Feasible network flows: conservation off `A ∪ B`, capacitated sources, absorbing sinks. -/
def NetworkFlows (A B : Finset V) (cap : V → ℝ) : Set (V → V → ℝ) :=
  {f | G.Feasible f ∧ (∀ x, x ∉ A → x ∉ B → netOut f x = 0) ∧
    (∀ x ∈ A, netOut f x ≤ cap x) ∧ ∀ x ∈ B, netOut f x ≤ 0}

omit [DecidableEq V] in
theorem isCompact_networkFlows (A B : Finset V) (cap : V → ℝ) :
    IsCompact (G.NetworkFlows A B cap) := by
  have hbox : IsCompact (Set.univ.pi fun u : V => Set.univ.pi fun v : V =>
      Set.Icc (-G.c v u) (G.c u v)) :=
    isCompact_univ_pi fun u => isCompact_univ_pi fun v => isCompact_Icc
  refine hbox.of_isClosed_subset ?_ ?_
  · have hev : ∀ u v : V, Continuous fun f : V → V → ℝ => f u v := fun u v => by fun_prop
    simp only [NetworkFlows, Feasible, IsFlow, Set.ofPred_and, Set.ofPred_forall]
    refine IsClosed.inter (IsClosed.inter ?_ ?_) (IsClosed.inter ?_ (IsClosed.inter ?_ ?_))
    · exact isClosed_iInter fun u => isClosed_iInter fun v =>
        isClosed_eq (hev v u) (hev u v).neg
    · exact isClosed_iInter fun u => isClosed_iInter fun v =>
        isClosed_le (hev u v) continuous_const
    · exact isClosed_iInter fun x => isClosed_iInter fun _ =>
        isClosed_iInter fun _ => isClosed_eq (continuous_netOut x) continuous_const
    · exact isClosed_iInter fun x => isClosed_iInter fun _ =>
        isClosed_le (continuous_netOut x) continuous_const
    · exact isClosed_iInter fun x => isClosed_iInter fun _ =>
        isClosed_le (continuous_netOut x) continuous_const
  · intro f hf
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies]
    intro u v
    refine ⟨?_, hf.1.2 u v⟩
    have := hf.1.2 v u
    rw [hf.1.1 u v] at this
    linarith

/-- **Max-flow/min-cut** with capacitated sources `A` and absorbing sinks `B`, for arbitrary
nonnegative real capacities. -/
theorem exists_maxFlow_network (A B : Finset V) (hAB : Disjoint A B) (cap : V → ℝ)
    (hcap : ∀ x, 0 ≤ cap x) :
    ∃ f : V → V → ℝ, ∃ S : Finset V, f ∈ G.NetworkFlows A B cap ∧ Disjoint S B ∧
      ∑ x ∈ A, netOut f x = G.out S + ∑ x ∈ A \ S, cap x := by
  set K := G.NetworkFlows A B cap
  have hK0 : (fun _ _ => (0 : ℝ)) ∈ K := by
    refine ⟨⟨fun _ _ => by simp, fun u v => by simpa using G.nonneg u v⟩,
      fun _ _ _ => by simp [netOut], fun x _ => by simp [netOut, hcap x],
      fun _ _ => by simp [netOut]⟩
  have hcont : Continuous fun f : V → V → ℝ => ∑ x ∈ A, netOut f x :=
    continuous_finsetSum _ fun x _ => continuous_netOut x
  obtain ⟨f, hfK, hmax⟩ :=
    (G.isCompact_networkFlows A B cap).exists_isMaxOn ⟨_, hK0⟩ hcont.continuousOn
  obtain ⟨hfeas, hcons, hsrc, hsink⟩ := hfK
  obtain ⟨hflow, hcapf⟩ := hfeas
  classical
  set Res : V → V → Prop := fun u v => f u v < G.c u v
  set Root : V → Prop := fun r => r ∈ A ∧ netOut f r < cap r
  set S : Finset V := univ.filter fun y => ∃ r, Root r ∧ Relation.ReflTransGen Res r y
  have hS : ∀ y, y ∈ S ↔ ∃ r, Root r ∧ Relation.ReflTransGen Res r y := by simp [S]
  -- No sink is reachable: otherwise augment along a residual walk.
  have hSB : Disjoint S B := by
    rw [disjoint_left]
    intro t htS htB
    obtain ⟨r, ⟨hrA, hrcap⟩, hrt⟩ := (hS t).mp htS
    obtain ⟨g, hg, hgpos, hgnet⟩ := exists_walkFlow Res hrt
    have hev := (eventually_feasible_add ⟨hflow, hcapf⟩ hg hgpos).and
      ((eventually_add_mul_lt hrcap 1).and (self_mem_nhdsWithin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε))
    obtain ⟨ε, hεf, hεr, hε⟩ := hev.exists
    set f' : V → V → ℝ := fun u v => f u v + ε * g u v
    have hnet' : ∀ x, netOut f' x = netOut f x + ε * netOut g x := fun x => by
      rw [netOut_add, netOut_smul]
    have hf'K : f' ∈ K := by
      refine ⟨hεf, fun x hxA hxB => ?_, fun x hxA => ?_, fun x hxB => ?_⟩
      · have hxr : x ≠ r := fun h => hxA (h ▸ hrA)
        have hxt : x ≠ t := fun h => hxB (h ▸ htB)
        rw [hnet', hgnet, hcons x hxA hxB]; simp [hxr, hxt]
      · have hxt : x ≠ t := fun h => disjoint_left.mp hAB hxA (h ▸ htB)
        rw [hnet', hgnet]
        by_cases hxr : x = r
        · subst hxr; simp [hxt]; linarith
        · simp [hxr, hxt]; exact hsrc x hxA
      · have hxr : x ≠ r := fun h => disjoint_left.mp hAB (h ▸ hrA) hxB
        rw [hnet', hgnet]
        by_cases hxt : x = t
        · subst hxt; simp [hxr]; linarith [hsink _ hxB]
        · simp [hxr, hxt]; exact hsink x hxB
    have hval : ∑ x ∈ A, netOut f' x = ∑ x ∈ A, netOut f x + ε := by
      simp only [hnet', sum_add_distrib, ← mul_sum, hgnet, sum_sub_distrib,
        sum_ite_eq', hrA, ite_true]
      have htA : t ∉ A := fun h => disjoint_left.mp hAB h htB
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
  have hbd : ∀ u ∈ S, ∀ v ∈ Sᶜ, f u v = G.c u v := by
    intro u hu v hv
    by_contra hne
    obtain ⟨r, hr, hru⟩ := (hS u).mp hu
    exact (mem_compl.mp hv) ((hS v).mpr ⟨r, hr, hru.tail
      (lt_of_le_of_ne (hcapf u v) hne)⟩)
  have hcutS : ∑ x ∈ S, netOut f x = G.out S := by
    rw [sum_netOut_eq hflow, out]
    exact sum_congr rfl fun u hu => sum_congr rfl fun v hv => hbd u hu v hv
  have hSA : ∑ x ∈ S, netOut f x = ∑ x ∈ A ∩ S, netOut f x := by
    rw [inter_comm]
    refine (sum_subset inter_subset_left fun x hxS hx => ?_).symm
    have hxA : x ∉ A := fun h => hx (mem_inter.mpr ⟨hxS, h⟩)
    exact hcons x hxA (disjoint_left.mp hSB hxS)
  refine ⟨f, S, ⟨⟨hflow, hcapf⟩, hcons, hsrc, hsink⟩, hSB, ?_⟩
  rw [← sum_inter_add_sum_sdiff A S, ← hSA, hcutS]
  congr 1
  exact sum_congr rfl hsat

/-- **Max-flow/min-cut** for `s`–`t` flows with arbitrary nonnegative real capacities. -/
theorem exists_maxFlow_minCut {s t : V} (hst : s ≠ t) :
    ∃ f : V → V → ℝ, ∃ S : Finset V, G.STFlow s t f ∧ s ∈ S ∧ t ∉ S ∧
      netOut f s = G.out S := by
  obtain ⟨f, S, ⟨hfeas, hcons, -, -⟩, hSB, hval⟩ :=
    G.exists_maxFlow_network {s} {t} (disjoint_singleton.2 hst) (fun _ => G.out {s})
      (fun _ => G.out_nonneg _)
  have hst' : G.STFlow s t f :=
    ⟨hfeas, fun x hxs hxt => hcons x (by simpa using hxs) (by simpa using hxt)⟩
  have htS : t ∉ S := fun h => disjoint_left.mp hSB h (mem_singleton_self t)
  rw [sum_singleton] at hval
  by_cases hsS : s ∈ S
  · refine ⟨f, S, hst', hsS, htS, ?_⟩
    rw [hval, sdiff_eq_empty_iff_subset.mpr (singleton_subset_iff.mpr hsS), sum_empty,
      add_zero]
  · refine ⟨f, {s}, hst', mem_singleton_self s, by simpa using hst.symm, ?_⟩
    have hsd : ({s} : Finset V) \ S = {s} := by
      ext x; simp only [Finset.mem_sdiff, mem_singleton]
      constructor
      · exact fun h => h.1
      · rintro rfl; exact ⟨rfl, hsS⟩
    rw [hsd, sum_singleton] at hval
    have hle := netOut_le_out hst' (mem_singleton_self s) (by simpa using hst.symm)
    linarith [G.out_nonneg S]

/-- **Max-flow/min-cut**, with both optimality statements explicit. -/
theorem maxFlow_minCut {s t : V} (hst : s ≠ t) :
    ∃ f : V → V → ℝ, ∃ S : Finset V, G.STFlow s t f ∧ s ∈ S ∧ t ∉ S ∧
      netOut f s = G.out S ∧
      (∀ g, G.STFlow s t g → netOut g s ≤ netOut f s) ∧
      (∀ S' : Finset V, s ∈ S' → t ∉ S' → G.out S ≤ G.out S') := by
  obtain ⟨f, S, hf, hs, ht, hval⟩ := G.exists_maxFlow_minCut hst
  refine ⟨f, S, hf, hs, ht, hval, fun g hg => hval ▸ netOut_le_out hg hs ht,
    fun S' hs' ht' => hval ▸ netOut_le_out hf hs' ht'⟩

/-- **Supplies to a root set.** Supplies `b ≥ 0` at the vertices outside `R` can be routed
into `R` by one feasible flow (each root absorbs, `netOut ≤ 0`) iff every root-avoiding
shore satisfies `b(S) ≤ F(S)`. -/
theorem supply_iff (b : V → ℝ) (hb : ∀ v, 0 ≤ b v) (R : Finset V) :
    (∀ S : Finset V, Disjoint S R → ∑ v ∈ S, b v ≤ G.out S) ↔
      ∃ f : V → V → ℝ, G.Feasible f ∧ (∀ v, v ∉ R → netOut f v = b v) ∧
        ∀ v ∈ R, netOut f v ≤ 0 := by
  constructor
  · intro hcut
    obtain ⟨f, S, ⟨hfeas, hcons, hsrc, hsink⟩, hSR, hval⟩ :=
      G.exists_maxFlow_network Rᶜ R disjoint_compl_left b hb
    refine ⟨f, hfeas, fun v hv => ?_, hsink⟩
    have hSsub : S ⊆ Rᶜ := fun x hx => mem_compl.mpr (disjoint_left.mp hSR hx)
    have hge : ∑ x ∈ Rᶜ, b x ≤ ∑ x ∈ Rᶜ, netOut f x := by
      rw [hval, ← sum_sdiff hSsub]
      linarith [hcut S hSR]
    have heq : ∑ x ∈ Rᶜ, netOut f x = ∑ x ∈ Rᶜ, b x :=
      le_antisymm (sum_le_sum hsrc) hge
    exact (sum_eq_sum_iff_of_le hsrc).mp heq v (mem_compl.mpr hv)
  · rintro ⟨f, hfeas, hsup, -⟩ S hSR
    calc ∑ v ∈ S, b v = ∑ v ∈ S, netOut f v :=
          sum_congr rfl fun v hv => (hsup v (disjoint_left.mp hSR hv)).symm
      _ ≤ G.out S := sum_netOut_le_out hfeas S

/-- **Demands from a root set.** The roots `R` can feed demands `b ≥ 0` at the vertices
outside `R` by one feasible flow (each root emits, `0 ≤ netOut`) iff every root-avoiding
shore satisfies `b(S) ≤ F(Sᶜ)`. -/
theorem demand_iff (b : V → ℝ) (hb : ∀ v, 0 ≤ b v) (R : Finset V) :
    (∀ S : Finset V, Disjoint S R → ∑ v ∈ S, b v ≤ G.out Sᶜ) ↔
      ∃ f : V → V → ℝ, G.Feasible f ∧ (∀ v, v ∉ R → netOut f v = -b v) ∧
        ∀ v ∈ R, 0 ≤ netOut f v := by
  have hrevF : ∀ f : V → V → ℝ, G.rev.Feasible f → G.Feasible fun u v => f v u :=
    fun f hf => ⟨fun u v => hf.1 v u, fun u v => hf.2 v u⟩
  have hFrev : ∀ f : V → V → ℝ, G.Feasible f → G.rev.Feasible fun u v => f v u :=
    fun f hf => ⟨fun u v => hf.1 v u, fun u v => hf.2 v u⟩
  have hnet : ∀ f : V → V → ℝ, IsFlow f → ∀ x, netOut (fun u v => f v u) x = -netOut f x := by
    intro f hf x
    simp only [netOut, ← sum_neg_distrib]
    exact sum_congr rfl fun u _ => hf x u
  have key := G.rev.supply_iff b hb R
  simp only [rev_out] at key
  rw [key]
  constructor
  · rintro ⟨f, hf, hsup, hroot⟩
    refine ⟨_, hrevF f hf, fun v hv => ?_, fun v hv => ?_⟩
    · rw [hnet f hf.1, hsup v hv]
    · rw [hnet f hf.1]; linarith [hroot v hv]
  · rintro ⟨f, hf, hsup, hroot⟩
    refine ⟨_, hFrev f hf, fun v hv => ?_, fun v hv => ?_⟩
    · rw [hnet f hf.1, hsup v hv, neg_neg]
    · rw [hnet f hf.1]; linarith [hroot v hv]

/-- **W4 shared flow, forward direction.** If `β |S| ≤ F(S)` for every root-avoiding `S`,
one feasible flow sends `β` units out of every vertex outside `R` into `R`. -/
theorem uniform_supply_iff (β : ℝ) (hβ : 0 ≤ β) (R : Finset V) :
    (∀ S : Finset V, Disjoint S R → β * S.card ≤ G.out S) ↔
      ∃ f : V → V → ℝ, G.Feasible f ∧ (∀ v, v ∉ R → netOut f v = β) ∧
        ∀ v ∈ R, netOut f v ≤ 0 := by
  have := G.supply_iff (fun _ => β) (fun _ => hβ) R
  simp only [sum_const, nsmul_eq_mul] at this
  simpa only [mul_comm] using this

/-- **W4 shared flow, reverse direction.** If `β |S| ≤ F(Sᶜ)` for every root-avoiding `S`,
one feasible flow sends `β` units from `R` into every vertex outside `R`. -/
theorem uniform_demand_iff (β : ℝ) (hβ : 0 ≤ β) (R : Finset V) :
    (∀ S : Finset V, Disjoint S R → β * S.card ≤ G.out Sᶜ) ↔
      ∃ f : V → V → ℝ, G.Feasible f ∧ (∀ v, v ∉ R → netOut f v = -β) ∧
        ∀ v ∈ R, 0 ≤ netOut f v := by
  have := G.demand_iff (fun _ => β) (fun _ => hβ) R
  simp only [sum_const, nsmul_eq_mul] at this
  simpa only [mul_comm] using this

end WeightedDiGraph

end CutQueryComplexity.DirectedCertificate
