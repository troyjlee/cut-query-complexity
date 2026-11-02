import CutQueryComplexity.DeterministicAPMCExpansion.Flow.RouteEndpoints
import Mathlib.Data.Fin.VecNotation

/-!
# Original endpoint crossings are paid for by actual routed edges

Delete the two public terminal coordinates from a route's signed unit flow.
Its original divergence is exactly source-endpoint minus sink-endpoint. Weak
duality then bounds each separated routed pair by its internal edge uses.
Summing the actual congestion bound pays for all separated real pairs, with
either path orientation and with repeated routes retained.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.Flow

open Finset Certificate AllPairsAudit
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

def originalRouteFlow (route : LocatedRoute V) (u v : V) : ℝ :=
  routeDelta route.nodes (.inl u) (.inl v)

theorem originalRouteFlow_isFlow (route : LocatedRoute V) : IsFlow (originalRouteFlow route) :=
  fun u v => routeDelta_isFlow route.nodes (.inl u) (.inl v)

theorem originalRouteFlow_divergence (route : LocatedRoute V)
    {R : NetworkVertex V → NetworkVertex V → Prop}
    (hp : RoutePath R source sink route.nodes) (hc : LocatedCorrect route) (v : V) :
    netOut (originalRouteFlow route) v =
      (if v = route.start then 1 else 0) - (if v = route.finish then 1 else 0) := by
  have hsourceZero : routeUse route.nodes (.inl v) source = 0 := by
    simp only [routeUse, hp.no_enter_source (.inl v), ↓reduceIte]
  have hsinkZero : routeUse route.nodes sink (.inl v) = 0 := by
    simp only [routeUse, hp.no_leave_target (.inl v), ↓reduceIte]
  have hs : routeDelta route.nodes (.inl v) source =
      -(if v = route.start then (1 : ℝ) else 0) := by
    simp only [routeDelta, hsourceZero, hc.1 v, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero, zero_sub]
  have ht : routeDelta route.nodes (.inl v) sink =
      (if v = route.finish then (1 : ℝ) else 0) := by
    simp only [routeDelta, hsinkZero, hc.2 v, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero, sub_zero]
  have hfull : netOut (routeDelta route.nodes) (.inl v) = 0 := by
    simpa only [source, sink, Sum.inl_ne_inr, ↓reduceIte, sub_self] using hp.divergence (.inl v)
  rw [netOut, Fintype.sum_sum_type, Fin.sum_univ_two] at hfull
  change netOut (originalRouteFlow route) v +
    (routeDelta route.nodes (.inl v) source + routeDelta route.nodes (.inl v) sink) = 0 at hfull
  rw [hs, ht] at hfull
  linarith

def routeCross (route : LocatedRoute V) (T : Finset V) : ℝ :=
  ∑ u ∈ T, ∑ v ∈ Tᶜ,
    ((routeUse route.nodes (.inl u) (.inl v) : ℝ) +
      (routeUse route.nodes (.inl v) (.inl u) : ℝ))

theorem routeCross_nonneg (route : LocatedRoute V) (T : Finset V) : 0 ≤ routeCross route T :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem route_separated_le_cross (route : LocatedRoute V)
    {R : NetworkVertex V → NetworkVertex V → Prop}
    (hp : RoutePath R source sink route.nodes) (hc : LocatedCorrect route) (T : Finset V) :
    separated T route.start route.finish ≤ routeCross route T := by
  have hsum : (∑ u ∈ T, netOut (originalRouteFlow route) u) =
      (if route.start ∈ T then (1 : ℝ) else 0) -
        (if route.finish ∈ T then (1 : ℝ) else 0) := by
    simp_rw [originalRouteFlow_divergence route hp hc]
    simp only [sum_sub_distrib]
    simp
  have hflux : (∑ u ∈ T, ∑ v ∈ Tᶜ, originalRouteFlow route u v) =
      (if route.start ∈ T then (1 : ℝ) else 0) -
        (if route.finish ∈ T then (1 : ℝ) else 0) :=
    (sum_netOut_eq (originalRouteFlow_isFlow route) T).symm.trans hsum
  have hpos : (∑ u ∈ T, ∑ v ∈ Tᶜ, originalRouteFlow route u v) ≤ routeCross route T := by
    apply sum_le_sum
    intro u _
    apply sum_le_sum
    intro v _
    dsimp [originalRouteFlow, routeDelta]
    linarith [Nat.cast_nonneg (α := ℝ) (routeUse route.nodes (.inl v) (.inl u))]
  have hneg : -(∑ u ∈ T, ∑ v ∈ Tᶜ, originalRouteFlow route u v) ≤ routeCross route T := by
    rw [← sum_neg_distrib]
    apply sum_le_sum
    intro u _
    rw [← sum_neg_distrib]
    apply sum_le_sum
    intro v _
    dsimp [originalRouteFlow, routeDelta]
    linarith [Nat.cast_nonneg (α := ℝ) (routeUse route.nodes (.inl u) (.inl v))]
  have hn := routeCross_nonneg route T
  by_cases hs : route.start ∈ T <;> by_cases ht : route.finish ∈ T <;>
    simp only [separated, hs, ht, ↓reduceIte] at hflux ⊢ <;> linarith

def routesCross (routes : List (LocatedRoute V)) (T : Finset V) : ℝ :=
  ∑ u ∈ T, ∑ v ∈ Tᶜ,
    ((routeLoad (routes.map LocatedRoute.nodes) (.inl u) (.inl v) : ℝ) +
      (routeLoad (routes.map LocatedRoute.nodes) (.inl v) (.inl u) : ℝ))

theorem routesCross_nil (T : Finset V) : routesCross ([] : List (LocatedRoute V)) T = 0 := by
  simp [routesCross, routeLoad]

theorem routesCross_cons (route : LocatedRoute V) (routes : List (LocatedRoute V)) (T : Finset V) :
    routesCross (route :: routes) T = routeCross route T + routesCross routes T := by
  simp only [routesCross, routeCross, List.map_cons, routeLoad, List.sum_cons,
    Nat.cast_add, sum_add_distrib]
  ring

theorem sum_routeCross (routes : List (LocatedRoute V)) (T : Finset V) :
    (routes.map (fun route => routeCross route T)).sum = routesCross routes T := by
  induction routes with
  | nil => simp [routesCross_nil]
  | cons route routes ih =>
      simp only [List.map_cons, List.sum_cons, routesCross_cons, ih]

theorem sum_separated_le_routesCross (routes : List (LocatedRoute V))
    (R : NetworkVertex V → NetworkVertex V → Prop)
    (hpaths : ∀ route ∈ routes, RoutePath R source sink route.nodes)
    (hlocated : ∀ route ∈ routes, LocatedCorrect route) (T : Finset V) :
    (routes.map (fun route => separated T route.start route.finish)).sum ≤ routesCross routes T := by
  induction routes with
  | nil => simp [routesCross_nil]
  | cons route routes ih =>
      have hhead := route_separated_le_cross route (hpaths _ (by simp)) (hlocated _ (by simp)) T
      have htail := ih (fun r hr => hpaths r (List.mem_cons_of_mem _ hr))
        (fun r hr => hlocated r (List.mem_cons_of_mem _ hr))
      simpa only [List.map_cons, List.sum_cons, routesCross_cons] using add_le_add hhead htail

/-- The full cut bound follows from the actual per-edge congestion, rather
than treating a matching as if it were already embedded in the hidden graph. -/
theorem routes_cut_domination (G : WeightedGraph V) (routes : List (LocatedRoute V))
    (R : NetworkVertex V → NetworkVertex V → Prop)
    (hpaths : ∀ route ∈ routes, RoutePath R source sink route.nodes)
    (hlocated : ∀ route ∈ routes, LocatedCorrect route)
    (hcongestion : ∀ u v,
      ((routeLoad (routes.map LocatedRoute.nodes) (.inl u) (.inl v) +
        routeLoad (routes.map LocatedRoute.nodes) (.inl v) (.inl u) : ℕ) : ℝ) ≤ G.w u v)
    (T : Finset V) :
    (routes.map (fun route => separated T route.start route.finish)).sum ≤ G.cut T := by
  apply (sum_separated_le_routesCross routes R hpaths hlocated T).trans
  apply sum_le_sum
  intro u _
  apply sum_le_sum
  intro v _
  simpa only [Nat.cast_add] using hcongestion u v

end
end CutQueryComplexity.DeterministicAPMCExpansion.Flow

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.originalRouteFlow_divergence
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.routes_cut_domination
