import CutQueryComplexity.Graph.Directed
import CutQueryComplexity.Certificate.MaxFlow

/-! # Directed max-flow and minimum `s`–`t` cut (D5)

A signed flow `f` (antisymmetric) is feasible in a directed multigraph when `f u v ≤ c u v` for
every ordered pair; antisymmetry then gives `−c v u ≤ f u v`. The minimum `s`–`t` cut value is
`stMin G s t`, the least outgoing cut over shores containing `s` and not `t`.

* `netOut_le_out`: weak duality, `netOut f s ≤ F(S)` for every `s`–`t` shore `S`.
* `exists_maxFlow_st`: some feasible flow conserving off `{s, t}` has `netOut f s = stMin G s t`.

The proof follows `Certificate.exists_maxFlow`. A maximum flow exists by compactness. The shore
reachable from `s` through residual ordered pairs `f u v < c u v` cannot contain `t`, since
augmenting along a residual walk would increase the value, and its boundary is saturated. This
is an offline existence proof and is not charged as an oracle algorithm.
-/

namespace CutQueryComplexity
namespace DirectedMincut

open Finset Filter Topology Certificate

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The minimum outgoing cut over shores containing `s` and not `t`. -/
noncomputable def stMin (G : DiGraph V) (s t : V) : ℕ :=
  sInf {k | ∃ S : Finset V, s ∈ S ∧ t ∉ S ∧ G.out S = k}

theorem stMin_le (G : DiGraph V) {s t : V} {S : Finset V} (hs : s ∈ S) (ht : t ∉ S) :
    stMin G s t ≤ G.out S :=
  Nat.sInf_le ⟨S, hs, ht, rfl⟩

theorem exists_stMin (G : DiGraph V) {s t : V} (hst : s ≠ t) :
    ∃ S : Finset V, s ∈ S ∧ t ∉ S ∧ G.out S = stMin G s t :=
  Nat.sInf_mem (s := {k | ∃ S : Finset V, s ∈ S ∧ t ∉ S ∧ G.out S = k})
    ⟨G.out {s}, {s}, mem_singleton_self s, by simpa using hst.symm, rfl⟩

/-- A feasible directed `s`–`t` flow. -/
def STFlow (G : DiGraph V) (s t : V) (f : V → V → ℝ) : Prop :=
  IsFlow f ∧ (∀ u v, f u v ≤ G.c u v) ∧ ∀ x, x ≠ s → x ≠ t → netOut f x = 0

/-- The outgoing cut as a real double sum. -/
theorem out_cast (G : DiGraph V) (S : Finset V) :
    (G.out S : ℝ) = ∑ u ∈ S, ∑ v ∈ Sᶜ, (G.c u v : ℝ) := by
  simp [DiGraph.out, DiGraph.arcs]

/-- **Weak duality.** -/
theorem netOut_le_out {G : DiGraph V} {s t : V} {f : V → V → ℝ} (hf : STFlow G s t f)
    {S : Finset V} (hs : s ∈ S) (ht : t ∉ S) : netOut f s ≤ G.out S := by
  have hsum : ∑ x ∈ S, netOut f x = netOut f s := by
    rw [← sum_erase_add _ _ hs]
    have : ∑ x ∈ S.erase s, netOut f x = 0 := sum_eq_zero fun x hx =>
      hf.2.2 x (ne_of_mem_erase hx) fun h => ht (h ▸ mem_of_mem_erase hx)
    rw [this, zero_add]
  rw [← hsum, sum_netOut_eq hf.1, out_cast]
  exact sum_le_sum fun u _ => sum_le_sum fun v _ => hf.2.1 u v

/-- The feasible `s`–`t` flows. -/
def STFlows (G : DiGraph V) (s t : V) : Set (V → V → ℝ) := {f | STFlow G s t f}

omit [DecidableEq V] in
theorem isCompact_stFlows (G : DiGraph V) (s t : V) : IsCompact (STFlows G s t) := by
  have hbox : IsCompact (Set.univ.pi fun u : V => Set.univ.pi fun v : V =>
      Set.Icc (-(G.c v u : ℝ)) (G.c u v)) :=
    isCompact_univ_pi fun u => isCompact_univ_pi fun v => isCompact_Icc
  refine hbox.of_isClosed_subset ?_ ?_
  · have hev : ∀ u v : V, Continuous fun f : V → V → ℝ => f u v := fun u v => by fun_prop
    simp only [STFlows, STFlow, IsFlow, Set.ofPred_and, Set.ofPred_forall]
    refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_)
    · exact isClosed_iInter fun u => isClosed_iInter fun v =>
        isClosed_eq (hev v u) (hev u v).neg
    · exact isClosed_iInter fun u => isClosed_iInter fun v =>
        isClosed_le (hev u v) continuous_const
    · exact isClosed_iInter fun x => isClosed_iInter fun _ =>
        isClosed_iInter fun _ => isClosed_eq (continuous_netOut x) continuous_const
  · intro f hf
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies]
    intro u v
    refine ⟨?_, hf.2.1 u v⟩
    have := hf.2.1 v u
    rw [hf.1 u v] at this
    linarith

/-- **Max-flow/min-cut** for directed multigraphs. -/
theorem exists_maxFlow_st (G : DiGraph V) {s t : V} (hst : s ≠ t) :
    ∃ f : V → V → ℝ, STFlow G s t f ∧ netOut f s = stMin G s t := by
  set K := STFlows G s t
  have hK0 : (fun _ _ => (0 : ℝ)) ∈ K :=
    ⟨fun _ _ => by simp, fun u v => by simp, fun _ _ _ => by simp [netOut]⟩
  obtain ⟨f, hfK, hmax⟩ := (isCompact_stFlows G s t).exists_isMaxOn ⟨_, hK0⟩
    (continuous_netOut s).continuousOn
  obtain ⟨hflow, hcap, hcons⟩ := hfK
  classical
  set Res : V → V → Prop := fun u v => f u v < G.c u v
  set S : Finset V := univ.filter fun y => Relation.ReflTransGen Res s y
  have hS : ∀ y, y ∈ S ↔ Relation.ReflTransGen Res s y := by simp [S]
  have hsS : s ∈ S := (hS s).mpr Relation.ReflTransGen.refl
  -- `t` is not reachable: otherwise augment along a residual walk
  have htS : t ∉ S := by
    intro htS
    obtain ⟨g, hg, hgpos, hgnet⟩ := exists_walkFlow Res ((hS t).mp htS)
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ u v, f u v + ε * g u v ≤ G.c u v := by
      rw [eventually_all]; intro u
      rw [eventually_all]; intro v
      have hε : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
      by_cases hgv : 0 < g u v
      · filter_upwards [eventually_add_mul_lt (hgpos u v hgv) (g u v)] with ε h
        exact h.le
      · filter_upwards [hε] with ε hε
        nlinarith [hcap u v]
    obtain ⟨ε, hεf, hε⟩ := (hev.and (self_mem_nhdsWithin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε)).exists
    set f' : V → V → ℝ := fun u v => f u v + ε * g u v
    have hnet' : ∀ x, netOut f' x = netOut f x + ε * netOut g x := fun x => by
      rw [netOut_add, netOut_smul]
    have hf'K : f' ∈ K := by
      refine ⟨fun u v => ?_, hεf, fun x hxs hxt => ?_⟩
      · simp only [f']; rw [hflow u v, hg u v]; ring
      · rw [hnet', hgnet, hcons x hxs hxt]; simp [hxs, hxt]
    have := hmax hf'K
    simp only [Set.mem_ofPred_eq] at this
    rw [hnet', hgnet] at this
    simp [hst] at this
    linarith
  -- the boundary of `S` is saturated
  have hbd : ∀ u ∈ S, ∀ v ∈ Sᶜ, f u v = G.c u v := by
    intro u hu v hv
    by_contra hne
    exact (mem_compl.mp hv) ((hS v).mpr (((hS u).mp hu).tail
      (lt_of_le_of_ne (hcap u v) hne)))
  have hval : netOut f s = G.out S := by
    have hsum : ∑ x ∈ S, netOut f x = netOut f s := by
      rw [← sum_erase_add _ _ hsS]
      have : ∑ x ∈ S.erase s, netOut f x = 0 := sum_eq_zero fun x hx =>
        hcons x (ne_of_mem_erase hx) fun h => htS (h ▸ mem_of_mem_erase hx)
      rw [this, zero_add]
    rw [← hsum, sum_netOut_eq hflow, out_cast]
    exact sum_congr rfl fun u hu => sum_congr rfl fun v hv => hbd u hu v hv
  refine ⟨f, ⟨hflow, hcap, hcons⟩, ?_⟩
  obtain ⟨S', hs', ht', hS'⟩ := exists_stMin G hst
  have hle : netOut f s ≤ G.out S' := netOut_le_out ⟨hflow, hcap, hcons⟩ hs' ht'
  have hge : (stMin G s t : ℝ) ≤ G.out S := by exact_mod_cast stMin_le G hsS htS
  rw [hS'] at hle
  linarith

end DirectedMincut
end CutQueryComplexity
