import CutQueryComplexity.DeterministicAPMCExpansion.Flow.Routes

/-!
# Original endpoints and available clone slots of extracted routes

A simple source-sink route uses exactly one source-star edge and one sink-star
edge. These public edges identify the original endpoints, including the case
where both are the same vertex. Its original route may therefore be a singleton.
No original edge is needed for that case.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.Flow

open Finset Certificate DirectedCertificate
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

def chooseUnit (p : V → ℕ) : Option V :=
  if h : ∃ v, p v = 1 then some (Classical.choose h) else none

theorem chooseUnit_spec (p : V → ℕ) (hsum : ∑ v, p v = 1) :
    ∃ v, chooseUnit p = some v ∧ ∀ w, p w = if w = v then 1 else 0 := by
  have hex : ∃ v, p v = 1 := by
    have hnonzero : ∃ v, p v ≠ 0 := by
      by_contra h
      have hz : ∀ v, p v = 0 := fun v => by
        by_contra hv
        exact h ⟨v, hv⟩
      simp only [hz, sum_const_zero] at hsum
      omega
    obtain ⟨v, hv⟩ := hnonzero
    have hle : p v ≤ ∑ w, p w := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ v)
    exact ⟨v, by omega⟩
  let v := Classical.choose hex
  have hv : p v = 1 := Classical.choose_spec hex
  refine ⟨v, ?_, ?_⟩
  · simp only [chooseUnit, dite_eq_left hex]
    rfl
  · intro w
    by_cases hw : w = v
    · simpa only [hw, ↓reduceIte] using hv
    · have hsplit := sum_erase_add (univ : Finset V) p (mem_univ v)
      have hzero : (∑ u ∈ (univ : Finset V).erase v, p u) = 0 := by omega
      have hmem : w ∈ (univ : Finset V).erase v := mem_erase.mpr ⟨hw, mem_univ w⟩
      have hle : p w ≤ ∑ u ∈ (univ : Finset V).erase v, p u :=
        single_le_sum (fun _ _ => Nat.zero_le _) hmem
      simp only [hw, ↓reduceIte]
      omega

theorem route_original_source_sum (G : WeightedGraph V) (a z : V → ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ)
    (hf : (directed (twoStar G a z)).Feasible f) {stack : List (NetworkVertex V)}
    (hp : RoutePath (fun u v => 0 < f u v) source sink stack) :
    (∑ v : V, routeUse stack source (.inl v)) = 1 := by
  have h := hp.source_sum source_ne_sink
  have hz (i : Fin 2) : routeUse stack source (.inr i) = 0 := by
    by_cases he : (source, Sum.inr i) ∈ routeArcs stack
    · have hpos := hp.arc he
      have hcap := hf.2 source (.inr i)
      change f source (.inr i) ≤ (twoStar G a z).w source (.inr i) at hcap
      simp only [twoStar, source, embedded, knownStars, zero_add] at hcap
      exact False.elim ((not_lt_of_ge hcap) hpos)
    · simp only [routeUse, he, ↓reduceIte]
  simpa only [Fintype.sum_sum_type, hz, sum_const_zero, Nat.add_zero] using h

theorem route_original_sink_sum (G : WeightedGraph V) (a z : V → ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ)
    (hf : (directed (twoStar G a z)).Feasible f) {stack : List (NetworkVertex V)}
    (hp : RoutePath (fun u v => 0 < f u v) source sink stack) :
    (∑ v : V, routeUse stack (.inl v) sink) = 1 := by
  have h := hp.sink_sum source_ne_sink
  have hz (i : Fin 2) : routeUse stack (.inr i) sink = 0 := by
    by_cases he : (Sum.inr i, sink) ∈ routeArcs stack
    · have hpos := hp.arc he
      have hcap := hf.2 (.inr i) sink
      change f (.inr i) sink ≤ (twoStar G a z).w (.inr i) sink at hcap
      simp only [twoStar, sink, embedded, knownStars, zero_add] at hcap
      exact False.elim ((not_lt_of_ge hcap) hpos)
    · simp only [routeUse, he, ↓reduceIte]
  simpa only [Fintype.sum_sum_type, hz, sum_const_zero, Nat.add_zero] using h

structure LocatedRoute (V : Type) where
  start : V
  finish : V
  nodes : List (NetworkVertex V)

def locateRoute (stack : List (NetworkVertex V)) : Option (LocatedRoute V) := do
  let start ← chooseUnit (fun v => routeUse stack source (.inl v))
  let finish ← chooseUnit (fun v => routeUse stack (.inl v) sink)
  pure ⟨start, finish, stack⟩

def LocatedCorrect (route : LocatedRoute V) : Prop :=
  (∀ v, routeUse route.nodes source (.inl v) = if v = route.start then 1 else 0) ∧
  (∀ v, routeUse route.nodes (.inl v) sink = if v = route.finish then 1 else 0)

theorem locateRoute_correct (G : WeightedGraph V) (a z : V → ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ)
    (hf : (directed (twoStar G a z)).Feasible f) {stack : List (NetworkVertex V)}
    (hp : RoutePath (fun u v => 0 < f u v) source sink stack) :
    ∃ route, locateRoute stack = some route ∧ route.nodes = stack ∧ LocatedCorrect route := by
  obtain ⟨start, hstart, hs⟩ := chooseUnit_spec _ (route_original_source_sum G a z f hf hp)
  obtain ⟨finish, hfinish, ht⟩ := chooseUnit_spec _ (route_original_sink_sum G a z f hf hp)
  refine ⟨⟨start, finish, stack⟩, ?_, rfl, hs, ht⟩
  simp only [locateRoute, hstart, hfinish]
  rfl

def locateRoutes : List (List (NetworkVertex V)) → Option (List (LocatedRoute V))
  | [] => some []
  | stack :: rest => do
      let route ← locateRoute stack
      let routes ← locateRoutes rest
      pure (route :: routes)

theorem locateRoutes_correct (G : WeightedGraph V) (a z : V → ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ)
    (hf : (directed (twoStar G a z)).Feasible f) («stacks» : List (List (NetworkVertex V)))
    (hpaths : ∀ stack ∈ «stacks», RoutePath (fun u v => 0 < f u v) source sink stack) :
    ∃ routes, locateRoutes «stacks» = some routes ∧ routes.map LocatedRoute.nodes = «stacks» ∧
      ∀ route ∈ routes, LocatedCorrect route := by
  induction «stacks» with
  | nil => exact ⟨[], rfl, rfl, by simp⟩
  | cons stack rest ih =>
      obtain ⟨route, hroute, hnodes, hcorrect⟩ :=
        locateRoute_correct G a z f hf (hpaths stack (by simp))
      obtain ⟨routes, hroutes, hrest, hrestCorrect⟩ :=
        ih (fun p hp => hpaths p (List.mem_cons_of_mem _ hp))
      refine ⟨route :: routes, ?_, ?_, ?_⟩
      · simp only [locateRoutes, hroute, hroutes]
        rfl
      · simp only [List.map_cons, hnodes, hrest]
      · intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact hcorrect
        · exact hrestCorrect r hr

def startCount (routes : List (LocatedRoute V)) (v : V) : ℕ :=
  (routes.map (fun r => if v = r.start then 1 else 0)).sum

def finishCount (routes : List (LocatedRoute V)) (v : V) : ℕ :=
  (routes.map (fun r => if v = r.finish then 1 else 0)).sum

theorem located_start_load (routes : List (LocatedRoute V))
    (h : ∀ r ∈ routes, LocatedCorrect r) (v : V) :
    startCount routes v = routeLoad (routes.map LocatedRoute.nodes) source (.inl v) := by
  simp only [startCount, routeLoad, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro r hr
  exact ((h r hr).1 v).symm

theorem located_finish_load (routes : List (LocatedRoute V))
    (h : ∀ r ∈ routes, LocatedCorrect r) (v : V) :
    finishCount routes v = routeLoad (routes.map LocatedRoute.nodes) (.inl v) sink := by
  simp only [finishCount, routeLoad, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro r hr
  exact ((h r hr).2 v).symm

/-- The available clone slots follow from the actual terminal capacities,
not a matching-saturation premise. Source and sink totals may differ. -/
theorem located_terminal_bounds (G : WeightedGraph V) (a z : V → ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ)
    (hf : (directed (twoStar G a z)).Feasible f) (amount : ℕ)
    (result : RouteResult (NetworkVertex V)) (hspec : RouteSpec f source sink amount result)
    (routes : List (LocatedRoute V)) (hmap : routes.map LocatedRoute.nodes = result.routes)
    (hc : ∀ r ∈ routes, LocatedCorrect r) (v : V) :
    startCount routes v ≤ a v ∧ finishCount routes v ≤ z v := by
  have hs := hspec.load_le source (.inl v)
  have ht := hspec.load_le (.inl v) sink
  have hscap := hf.2 source (.inl v)
  have htcap := hf.2 (.inl v) sink
  change f source (.inl v) ≤ (twoStar G a z).w source (.inl v) at hscap
  rw [twoStar_source] at hscap
  change f (.inl v) sink ≤ (twoStar G a z).w (.inl v) sink at htcap
  rw [(twoStar G a z).symm, twoStar_sink] at htcap
  have hs' : (routeLoad result.routes source (.inl v) : ℝ) ≤ a v :=
    hs.trans (max_le hscap (Nat.cast_nonneg _))
  have ht' : (routeLoad result.routes (.inl v) sink : ℝ) ≤ z v :=
    ht.trans (max_le htcap (Nat.cast_nonneg _))
  rw [located_start_load routes hc v, hmap, located_finish_load routes hc v, hmap]
  exact ⟨by exact_mod_cast hs', by exact_mod_cast ht'⟩

end
end CutQueryComplexity.DeterministicAPMCExpansion.Flow

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.locateRoutes_correct
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.located_terminal_bounds
