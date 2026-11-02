import CutQueryComplexity.DeterministicAPMCExpansion.Flow.ExactHistory

/-!
# Offline extraction of unit routes from the returned explicit flow

The producer takes a public signed matrix and an integer amount. It repeatedly
chooses a simple path in that matrix's positive support and subtracts one unit.
The hidden graph is not an argument. The path-existence and usage proofs are
derived from conservation and integrality of the explicit matrix, which the
actual exact-flow execution supplies.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.Flow

open Finset Certificate DirectedCertificate Prog
open scoped Classical
noncomputable section

variable {U : Type} [Fintype U] [DecidableEq U]

/-- Simple paths stored in reverse order, including both endpoints. -/
inductive RoutePath (R : U → U → Prop) (s : U) : U → List U → Prop
  | root : RoutePath R s s [s]
  | push {u : U} {rest : List U} (path : RoutePath R s u (u :: rest))
      (v : U) (edge : R u v) (fresh : v ∉ u :: rest) :
      RoutePath R s v (v :: u :: rest)

theorem RoutePath.head {R : U → U → Prop} {s t : U} {stack : List U}
    (hp : RoutePath R s t stack) : ∃ rest, stack = t :: rest := by
  cases hp <;> exact ⟨_, rfl⟩

theorem RoutePath.nodup {R : U → U → Prop} {s t : U} {stack : List U}
    (hp : RoutePath R s t stack) : stack.Nodup := by
  induction hp with
  | root => simp
  | push _ _ _ fresh ih => exact List.nodup_cons.mpr ⟨fresh, ih⟩

theorem RoutePath.source_mem {R : U → U → Prop} {s t : U} {stack : List U}
    (hp : RoutePath R s t stack) : s ∈ stack := by
  induction hp with
  | root => simp
  | push _ _ _ _ ih => exact List.mem_cons_of_mem _ ih

theorem RoutePath.mono {R T : U → U → Prop} {s t : U} {stack : List U}
    (hp : RoutePath R s t stack) (hRT : ∀ u v, R u v → T u v) : RoutePath T s t stack := by
  induction hp with
  | root => exact .root
  | push _ v edge fresh ih => exact .push ih v (hRT _ _ edge) fresh

/-- If an extension revisits a vertex, truncate at its previous occurrence. -/
theorem RoutePath.prefix {R : U → U → Prop} {s t : U} {stack : List U}
    (hp : RoutePath R s t stack) (v : U) (hv : v ∈ stack) :
    ∃ shorter, RoutePath R s v shorter := by
  induction hp with
  | root =>
      have h : v = s := List.mem_singleton.mp hv
      subst v
      exact ⟨[s], .root⟩
  | @push u rest path w edge fresh ih =>
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ⟨v :: u :: rest, .push path v edge fresh⟩
      · exact ih hv

theorem reachable_route {R : U → U → Prop} {s t : U}
    (h : Relation.ReflTransGen R s t) : ∃ stack, RoutePath R s t stack := by
  induction h with
  | refl => exact ⟨[s], .root⟩
  | @tail u v reach edge ih =>
      obtain ⟨stack, hp⟩ := ih
      by_cases hv : v ∈ stack
      · exact hp.prefix v hv
      · obtain ⟨rest, rfl⟩ := hp.head
        exact ⟨v :: u :: rest, .push hp v edge hv⟩

def routeArcs : List U → Finset (U × U)
  | child :: parent :: rest => insert (parent, child) (routeArcs (parent :: rest))
  | _ => ∅

theorem routeArcs_vertices (stack : List U) {u v : U}
    (he : (u, v) ∈ routeArcs stack) : u ∈ stack ∧ v ∈ stack := by
  induction stack with
  | nil => simp [routeArcs] at he
  | cons child tail ih =>
      cases tail with
      | nil => simp [routeArcs] at he
      | cons parent rest =>
          rcases mem_insert.mp he with he | he
          · cases he; simp
          · have h := ih he
            exact ⟨List.mem_cons_of_mem _ h.1, List.mem_cons_of_mem _ h.2⟩

theorem RoutePath.arc {R : U → U → Prop} {s t : U} {stack : List U}
    (hp : RoutePath R s t stack) {u v : U} (he : (u, v) ∈ routeArcs stack) : R u v := by
  induction hp with
  | root => simp [routeArcs] at he
  | push _ _ edge _ ih =>
      rcases mem_insert.mp he with he | he
      · cases he; exact edge
      · exact ih he

theorem RoutePath.no_enter_source {R : U → U → Prop} {s t : U} {stack : List U}
    (hp : RoutePath R s t stack) (u : U) : (u, s) ∉ routeArcs stack := by
  induction hp with
  | root => simp [routeArcs]
  | push path v _ fresh ih =>
      intro he
      rcases mem_insert.mp he with he | he
      · cases he
        exact fresh path.source_mem
      · exact ih he

theorem RoutePath.no_leave_target {R : U → U → Prop} {s t : U} {stack : List U}
    (hp : RoutePath R s t stack) (u : U) : (t, u) ∉ routeArcs stack := by
  cases hp with
  | root => simp [routeArcs]
  | @push v rest path w edge fresh =>
      intro he
      rcases mem_insert.mp he with he | he
      · have hwv : t = v := (Prod.mk.inj he).1
        exact fresh (by simp [hwv])
      · exact fresh (routeArcs_vertices _ he).1

def routeUse (stack : List U) (u v : U) : ℕ := if (u, v) ∈ routeArcs stack then 1 else 0

def routeDelta (stack : List U) (u v : U) : ℝ :=
  (routeUse stack u v : ℝ) - routeUse stack v u

theorem routeDelta_isFlow (stack : List U) : IsFlow (routeDelta stack) := by
  intro u v
  simp only [routeDelta]
  ring

theorem routeDelta_push {R : U → U → Prop} {s u v : U} {rest : List U}
    (hp : RoutePath R s u (u :: rest)) (hv : v ∉ u :: rest) :
    routeDelta (v :: u :: rest) = fun a b => arc u v a b + routeDelta (u :: rest) a b := by
  have hnew : (u, v) ∉ routeArcs (u :: rest) :=
    fun h => hv (routeArcs_vertices _ h).2
  have huse (a b : U) : routeUse (v :: u :: rest) a b =
      (if a = u ∧ b = v then 1 else 0) + routeUse (u :: rest) a b := by
    by_cases he : a = u ∧ b = v
    · obtain ⟨rfl, rfl⟩ := he
      simp [routeUse, routeArcs, hnew]
    · simp only [routeUse, routeArcs, mem_insert, Prod.mk.injEq, he, ↓reduceIte,
        false_or, Nat.zero_add]
  funext a b
  simp only [routeDelta, huse, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, arc]
  have hswap : (b = u ∧ a = v) ↔ (a = v ∧ b = u) := and_comm
  simp only [hswap]
  ring

theorem RoutePath.divergence {R : U → U → Prop} {s t : U} {stack : List U}
    (hp : RoutePath R s t stack) (v : U) :
    netOut (routeDelta stack) v = (if v = s then 1 else 0) - (if v = t then 1 else 0) := by
  induction hp with
  | root => simp [routeDelta, routeUse, routeArcs, netOut]
  | push path w _ fresh ih =>
      rw [routeDelta_push path fresh, netOut_add, netOut_arc, ih]
      ring

theorem RoutePath.source_sum {R : U → U → Prop} {s t : U} {stack : List U}
    (hp : RoutePath R s t stack) (hst : s ≠ t) : (∑ v, routeUse stack s v) = 1 := by
  have h := hp.divergence s
  have hz (v : U) : routeUse stack v s = 0 := by
    simp only [routeUse, hp.no_enter_source v, ↓reduceIte]
  simp only [netOut, routeDelta, hz, Nat.cast_zero, sub_zero, hst, ↓reduceIte] at h
  exact_mod_cast h

theorem RoutePath.sink_sum {R : U → U → Prop} {s t : U} {stack : List U}
    (hp : RoutePath R s t stack) (hst : s ≠ t) : (∑ v, routeUse stack v t) = 1 := by
  have h := hp.divergence t
  have hz (v : U) : routeUse stack t v = 0 := by
    simp only [routeUse, hp.no_leave_target v, ↓reduceIte]
  simp only [netOut, routeDelta, hz, Nat.cast_zero, zero_sub,
    Ne.symm hst, ↓reduceIte, sum_neg_distrib] at h
  have hs : (∑ v, (routeUse stack v t : ℝ)) = 1 := by linarith
  exact_mod_cast hs

def SignedIntegral (f : U → U → ℝ) : Prop := ∀ u v, ∃ k : ℤ, f u v = k

theorem SignedIntegral.one_le {f : U → U → ℝ} (hf : SignedIntegral f)
    {u v : U} (hpos : 0 < f u v) : 1 ≤ f u v := by
  obtain ⟨k, hk⟩ := hf u v
  rw [hk] at hpos ⊢
  have h : (0 : ℤ) < k := by exact_mod_cast hpos
  exact_mod_cast (show (1 : ℤ) ≤ k by omega)

def routeSubtract (f : U → U → ℝ) (stack : List U) : U → U → ℝ :=
  fun u v => f u v - routeDelta stack u v

theorem routeSubtract_isFlow {f : U → U → ℝ} (hf : IsFlow f) (stack : List U) :
    IsFlow (routeSubtract f stack) := by
  intro u v
  simp only [routeSubtract, hf u v, routeDelta_isFlow stack u v]
  ring

theorem routeSubtract_integral {f : U → U → ℝ} (hf : SignedIntegral f) (stack : List U) :
    SignedIntegral (routeSubtract f stack) := by
  intro u v
  obtain ⟨k, hk⟩ := hf u v
  refine ⟨k - routeUse stack u v + routeUse stack v u, ?_⟩
  simp only [routeSubtract, routeDelta, hk]
  push_cast
  ring

theorem routeSubtract_netOut {f : U → U → ℝ} {s t : U} {stack : List U}
    (hp : RoutePath (fun u v => 0 < f u v) s t stack) (v : U) :
    netOut (routeSubtract f stack) v = netOut f v -
      (if v = s then 1 else 0) + (if v = t then 1 else 0) := by
  change (∑ w, (f v w - routeDelta stack v w)) = _
  rw [sum_sub_distrib]
  change netOut f v - netOut (routeDelta stack) v =
    netOut f v - (if v = s then 1 else 0) + (if v = t then 1 else 0)
  rw [hp.divergence]
  ring

/-- Extracted usage plus the remaining positive part equals the initial
positive part, coordinate by coordinate. This retains all multiplicities. -/
theorem routeSubtract_balance {f : U → U → ℝ} (hf : IsFlow f) (hint : SignedIntegral f)
    {s t : U} {stack : List U} (hp : RoutePath (fun u v => 0 < f u v) s t stack)
    (u v : U) : (routeUse stack u v : ℝ) + max (routeSubtract f stack u v) 0 = max (f u v) 0 := by
  by_cases huv : (u, v) ∈ routeArcs stack
  · have hpos := hp.arc huv
    have hone := hint.one_le hpos
    have hvu : (v, u) ∉ routeArcs stack := by
      intro he
      have hback := hp.arc he
      rw [hf u v] at hback
      linarith
    simp only [routeSubtract, routeDelta, routeUse, huv, hvu, ↓reduceIte,
      Nat.cast_one, Nat.cast_zero, sub_zero]
    rw [max_eq_left (by linarith : 0 ≤ f u v - 1), max_eq_left hpos.le]
    ring
  · by_cases hvu : (v, u) ∈ routeArcs stack
    · have hone := hint.one_le (hp.arc hvu)
      rw [hf u v] at hone
      simp only [routeSubtract, routeDelta, routeUse, huv, hvu, ↓reduceIte,
        Nat.cast_one, Nat.cast_zero, zero_sub, sub_neg_eq_add, zero_add]
      rw [max_eq_right (by linarith : f u v + 1 ≤ 0), max_eq_right (by linarith : f u v ≤ 0)]
    · simp [routeSubtract, routeDelta, routeUse, huv, hvu]

theorem positive_flow_reachable (f : U → U → ℝ) (hf : IsFlow f) (s t : U)
    (hcons : ∀ v, v ≠ s → v ≠ t → netOut f v = 0) (hpos : 0 < netOut f s) :
    Relation.ReflTransGen (fun u v => 0 < f u v) s t := by
  let S : Finset U := univ.filter (fun v => Relation.ReflTransGen (fun u v => 0 < f u v) s v)
  have hS (v : U) : v ∈ S ↔ Relation.ReflTransGen (fun u v => 0 < f u v) s v := by simp [S]
  have hs : s ∈ S := (hS s).mpr .refl
  by_contra hreach
  have ht : t ∉ S := fun h => hreach ((hS t).mp h)
  have hsum : (∑ v ∈ S, netOut f v) = netOut f s := by
    rw [← sum_erase_add _ _ hs]
    have hz : (∑ v ∈ S.erase s, netOut f v) = 0 := by
      apply sum_eq_zero
      intro v hv
      exact hcons v (ne_of_mem_erase hv) (fun he => ht (he ▸ mem_of_mem_erase hv))
    rw [hz, zero_add]
  have hboundary : ∀ u ∈ S, ∀ v ∈ Sᶜ, f u v ≤ 0 := by
    intro u hu v hv
    by_contra h
    exact (mem_compl.mp hv) ((hS v).mpr (((hS u).mp hu).tail (lt_of_not_ge h)))
  rw [sum_netOut_eq hf] at hsum
  have hnonpos : (∑ u ∈ S, ∑ v ∈ Sᶜ, f u v) ≤ 0 :=
    sum_nonpos fun u hu => sum_nonpos fun v hv => hboundary u hu v hv
  linarith

def chooseRoute (f : U → U → ℝ) (s t : U) :
    Option {stack : List U // RoutePath (fun u v => 0 < f u v) s t stack} :=
  if h : ∃ stack, RoutePath (fun u v => 0 < f u v) s t stack then
    some ⟨Classical.choose h, Classical.choose_spec h⟩
  else none

theorem chooseRoute_not_none (f : U → U → ℝ) (hf : IsFlow f) (s t : U)
    (hcons : ∀ v, v ≠ s → v ≠ t → netOut f v = 0) (hpos : 0 < netOut f s) :
    chooseRoute f s t ≠ none := by
  have h := reachable_route (positive_flow_reachable f hf s t hcons hpos)
  simp only [chooseRoute, dite_eq_left h]
  intro hn
  cases hn

structure RouteResult (U : Type) where
  remaining : U → U → ℝ
  routes : List (List U)

def extractRoutes (s t : U) : ℕ → (U → U → ℝ) → RouteResult U
  | 0, f => ⟨f, []⟩
  | amount + 1, f =>
      match chooseRoute f s t with
      | none => ⟨f, []⟩
      | some chosen =>
          let rest := extractRoutes s t amount (routeSubtract f chosen.val)
          ⟨rest.remaining, chosen.val :: rest.routes⟩

def routeLoad (routes : List (List U)) (u v : U) : ℕ :=
  (routes.map fun stack => routeUse stack u v).sum

structure RouteSpec (f : U → U → ℝ) (s t : U) (amount : ℕ) (result : RouteResult U) : Prop where
  flow : IsFlow result.remaining
  integral : SignedIntegral result.remaining
  conservation : ∀ v, v ≠ s → v ≠ t → netOut result.remaining v = 0
  exhausted : netOut result.remaining s = 0
  count : result.routes.length = amount
  paths : ∀ stack ∈ result.routes, RoutePath (fun u v => 0 < f u v) s t stack
  balance : ∀ u v, (routeLoad result.routes u v : ℝ) + max (result.remaining u v) 0 = max (f u v) 0

theorem extractRoutes_correct (s t : U) (hst : s ≠ t) (amount : ℕ) (f : U → U → ℝ)
    (hf : IsFlow f) (hint : SignedIntegral f)
    (hcons : ∀ v, v ≠ s → v ≠ t → netOut f v = 0)
    (hvalue : netOut f s = (amount : ℝ)) :
    RouteSpec f s t amount (extractRoutes s t amount f) := by
  induction amount generalizing f with
  | zero =>
      refine ⟨hf, hint, hcons, ?_, rfl, ?_, ?_⟩
      · simpa only [Nat.cast_zero, extractRoutes] using hvalue
      · simp [extractRoutes]
      · intro u v; simp [extractRoutes, routeLoad]
  | succ amount ih =>
      have hpos : 0 < netOut f s := by rw [hvalue]; positivity
      rw [extractRoutes]
      cases hc : chooseRoute f s t with
      | none => exact False.elim ((chooseRoute_not_none f hf s t hcons hpos) hc)
      | some chosen =>
          have hp := chosen.property
          have hf' := routeSubtract_isFlow hf chosen.val
          have hint' := routeSubtract_integral hint chosen.val
          have hcons' : ∀ v, v ≠ s → v ≠ t → netOut (routeSubtract f chosen.val) v = 0 := by
            intro v hvs hvt
            rw [routeSubtract_netOut hp v, hcons v hvs hvt]
            simp [hvs, hvt]
          have hvalue' : netOut (routeSubtract f chosen.val) s = (amount : ℝ) := by
            rw [routeSubtract_netOut hp s, hvalue]
            simp only [hst, ↓reduceIte, Nat.cast_add, Nat.cast_one]
            ring
          have hi := ih _ hf' hint' hcons' hvalue'
          refine ⟨hi.flow, hi.integral, hi.conservation, hi.exhausted, ?_, ?_, ?_⟩
          · simp only [List.length_cons, hi.count]
          · intro stack hs
            rcases List.mem_cons.mp hs with rfl | hs
            · exact hp
            · apply (hi.paths stack hs).mono
              intro u v huv
              have hb := routeSubtract_balance hf hint hp u v
              have huse : (0 : ℝ) ≤ routeUse chosen.val u v := Nat.cast_nonneg _
              rw [max_eq_left huv.le] at hb
              by_contra h
              rw [max_eq_right (le_of_not_gt h)] at hb
              linarith
          · intro u v
            have hstep := routeSubtract_balance hf hint hp u v
            have htail := hi.balance u v
            simp only [routeLoad, List.map_cons, List.sum_cons, Nat.cast_add]
            change (routeUse chosen.val u v : ℝ) +
              (routeLoad (extractRoutes s t amount (routeSubtract f chosen.val)).routes u v : ℝ) +
              max ((extractRoutes s t amount (routeSubtract f chosen.val)).remaining u v) 0 = max (f u v) 0
            linarith

theorem RouteSpec.load_le {f : U → U → ℝ} {s t : U} {amount : ℕ} {result : RouteResult U}
    (h : RouteSpec f s t amount result) (u v : U) :
    (routeLoad result.routes u v : ℝ) ≤ max (f u v) 0 := by
  have hb := h.balance u v
  have hn : 0 ≤ max (result.remaining u v) 0 := le_max_right _ _
  linarith

/-- Undirected congestion counts both route orientations. Conformal extraction
never charges cancelling flow twice. -/
theorem RouteSpec.undirected_load_le {f : U → U → ℝ} {s t : U} {amount : ℕ}
    {result : RouteResult U} (h : RouteSpec f s t amount result)
    {G : WeightedGraph U} (hf : (directed G).Feasible f) (u v : U) :
    ((routeLoad result.routes u v + routeLoad result.routes v u : ℕ) : ℝ) ≤ G.w u v := by
  have huv := h.load_le u v
  have hvu := h.load_le v u
  have hcap := hf.2 u v
  have hcap' := hf.2 v u
  change f u v ≤ G.w u v at hcap
  change f v u ≤ G.w v u at hcap'
  rw [hf.1 u v] at hvu hcap'
  rw [G.symm v u] at hcap'
  push_cast
  by_cases hpos : 0 ≤ f u v
  · rw [max_eq_left hpos] at huv
    rw [max_eq_right (by linarith : -f u v ≤ 0)] at hvu
    linarith
  · have hneg : f u v ≤ 0 := le_of_not_ge hpos
    rw [max_eq_right hneg] at huv
    rw [max_eq_left (by linarith : 0 ≤ -f u v)] at hvu
    linarith

variable {V : Type} [Fintype V] [DecidableEq V]

def exactRoutes (result : ExactResult V) : RouteResult (NetworkVertex V) :=
  extractRoutes source sink (eventValue result.events) result.flow

/-- Retain the minimum shore as well as the extracted routes. All extraction
uses the returned public matrix and causes no additional oracle queries. -/
def routedFlowProg (C : ℕ) (a z : V → ℕ) :
    Prog (Finset V) ℝ (ExactResult V × RouteResult (NetworkVertex V)) :=
  (scaledExactProg C a z).map (fun result => (result, exactRoutes result))

theorem routedFlowProg_cost (read : Finset V → ℝ) (C : ℕ) (a z : V → ℕ) :
    (routedFlowProg C a z).cost read = (scaledExactProg C a z).cost read := by
  simp only [routedFlowProg, Prog.cost_map]

theorem routedFlowProg_correct (G : WeightedGraph V) (hG : AllPairsAudit.Unweighted G)
    (C : ℕ) (a z : V → ℕ) :
    let result := (routedFlowProg C a z).eval G.cut
    ExactCertificate (directed (twoStar (scaledInternal G C) a z)) result.1 ∧
      RouteSpec result.1.flow source sink (eventValue result.1.events) result.2 := by
  have hc := scaledExactProg_correct G hG C a z
  have hh := (scaledExactProg_history G hG C a z).1
  simp only [routedFlowProg, Prog.eval_map]
  refine ⟨hc, ?_⟩
  apply extractRoutes_correct source sink source_ne_sink _ _ hc.feasible.1.1
  · exact fun u v => hc.flow_integer (twoStar_integral (scaledInternal_integral hG C) a z) u v
  · exact hc.feasible.2
  · have h := hh.value_difference
    simpa only [netOut, sum_const_zero, sub_zero] using h

end
end CutQueryComplexity.DeterministicAPMCExpansion.Flow

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.positive_flow_reachable
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.extractRoutes_correct
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.routedFlowProg_correct
