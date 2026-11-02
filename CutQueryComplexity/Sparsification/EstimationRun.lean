import CutQueryComplexity.Sparsification.Merge
import CutQueryComplexity.Sparsification.Window
import CutQueryComplexity.Primitive.BinarySearch

/-! # The adaptive estimation run as an iterated query program

The state holds the public data of the run: the block labeling, the cached block
cuts, the current scale, the regions still pending in the current batch, the merge
events (needed later for output sampling), and a log of all estimation calls.

One step of `estStep` does one of the following:

* **Batch boundary** (no pending region, no queries). If no remaining pair exists,
  the run is done. Otherwise it computes `D = topLevel H π` and the scale
  `κ' = min(κ/2, n²D/2)`, and lists the active regions: the components of the
  forest above `D/n²` that contain at least two blocks.
* **Region call.** It runs `estimateCall` on the next pending region. On `none` the
  run fails. On `some X` it merges by `mergeMap`, queries the original cut
  `cut(pull π K)` of each new nontrivial group `K` with `queryCuts`, and updates the
  cache by `mergeCache`.

The step budget is `R·residualDrawCost k k + 1 + n`, with `k = searchDepth V`.
The program chooses everything from public data; the graph enters only through
cut queries. Correctness, termination, and query accounting are proved separately.
-/

namespace CutQueryComplexity.WeightedGraph
noncomputable section
open scoped Classical
open Probability
variable {V : Type} [Fintype V]

/-! ### Querying a list of cuts -/

/-- Query the cut of every set in the list; unlisted sets get zero. -/
def queryCuts : (L : List (Finset V)) → RTree (Finset V) ℝ (Finset V → ℝ) L.length
  | [] => RTree.pure (PMF.pure fun _ => 0)
  | K :: L => RTree.query K fun a => (queryCuts L).map (fun g => Function.update g K a)

omit [Fintype V] in
theorem queryCuts_eval (read : Finset V → ℝ) (L : List (Finset V)) :
    (queryCuts L).eval read = PMF.pure (fun K => if K ∈ L then read K else 0) := by
  induction L with
  | nil => simp [queryCuts]
  | cons K L ih =>
      rw [queryCuts, RTree.eval_query, RTree.eval_map, ih, PMF.pure_map]
      congr 1
      funext K'
      by_cases h : K' = K
      · subst h; simp
      · simp [h]

/-! ### Regions -/

/-- The forest component of `v` above threshold `t`. -/
def forestRegion (H : WeightedGraph V) (t : ℝ) (v : V) : Finset V :=
  Finset.univ.filter ((H.threshold t).Reachable v)

/-- Forest components above `t` containing at least two blocks. -/
def activeRegions (H : WeightedGraph V) (π : V → V) (t : ℝ) : Finset (Finset V) :=
  (Finset.univ.image (forestRegion H t)).filter (fun S => ∃ u ∈ S, ∃ v ∈ S, π u ≠ π v)

/-! ### State -/

/-- A recorded merge: the labeling and cache before it, the merged old labels, and the label. -/
structure MergeEvent (V : Type) where
  π : V → V
  cache : V → ℝ
  group : Finset V
  β : ℝ

/-- A recorded estimation call: the labeling and cache, the region labels, and the scale. -/
structure CallRecord (V : Type) where
  π : V → V
  cache : V → ℝ
  T : Finset V
  κ : ℝ
  groups : ℕ

inductive RunStatus
  | running
  | done
  | failed
  deriving DecidableEq

structure EstState (V : Type) where
  π : V → V
  cache : V → ℝ
  κ : ℝ
  pending : List (Finset V)
  events : List (MergeEvent V)
  calls : List (CallRecord V)
  status : RunStatus

/-- Budget of one step. -/
abbrev estStepBudget (V : Type) [Fintype V] (R : ℕ) : ℕ :=
  R * residualDrawCost (searchDepth V) (searchDepth V) + 1 + Fintype.card V

/-- The batch boundary, without queries. -/
def boundary (H : WeightedGraph V) (s : EstState V) : EstState V :=
  if (remaining H s.π).Nonempty then
    let D := topLevel H s.π
    { s with κ := min (s.κ / 2) ((Fintype.card V : ℝ) ^ 2 / 2 * D)
             pending := (activeRegions H s.π (D / (Fintype.card V : ℝ) ^ 2)).toList }
  else { s with status := .done }

/-- The state after a successful call on region `S` with sampled block graph `X`. -/
def afterCall (s : EstState V) (S : Finset V) (rest : List (Finset V)) (X : WeightedGraph V)
    (ans : Finset V → ℝ) : EstState V :=
  let T := S.image s.π
  let θ := 3 * s.κ / 4
  { π := mergeMap s.π T X θ
    cache := mergeCache T X θ s.cache ans
    κ := s.κ
    pending := rest
    events := s.events ++ (nontrivialGroups T X θ).toList.map
      (fun K => ⟨s.π, s.cache, K, s.κ / 2⟩)
    calls := s.calls ++ [⟨s.π, s.cache, T, s.κ, (nontrivialGroups T X θ).card⟩]
    status := .running }

theorem groups_length_le (T : Finset V) (X : WeightedGraph V) (θ : ℝ) :
    (nontrivialGroups T X θ).toList.length ≤ Fintype.card V := by
  rw [Finset.length_toList]
  calc
    _ ≤ (mergeGroups T X θ).card := Finset.card_filter_le _ _
    _ ≤ T.card := Finset.card_image_le
    _ ≤ Fintype.card V := Finset.card_le_univ T

/-- One region call, followed by the merge and the cache queries. -/
def regionStep (ρ : ℝ) (R : ℕ) (s : EstState V) (S : Finset V) (rest : List (Finset V))
    (hκ : 0 < s.κ) : RTree (Finset V) ℝ (EstState V) (estStepBudget V R) :=
  ((estimateCall (searchDepth V) (searchDepth V) s.π s.cache (S.image s.π) hκ ρ R).bind
    fun o => match o with
    | none => (RTree.pure (PMF.pure { s with
          status := .failed, calls := s.calls ++ [⟨s.π, s.cache, S.image s.π, s.κ, 0⟩] }) :
        RTree (Finset V) ℝ (EstState V) (Fintype.card V))
    | some X =>
        ((queryCuts ((nontrivialGroups (S.image s.π) X (3 * s.κ / 4)).toList.map (pull s.π))).map
          (fun g => afterCall s S rest X (fun K => g (pull s.π K)))).weaken
            (by rw [List.length_map]; exact groups_length_le _ _ _))

/-- One step of the run. -/
def estStep (H : WeightedGraph V) (ρ : ℝ) (R : ℕ) (s : EstState V) :
    RTree (Finset V) ℝ (EstState V) (estStepBudget V R) :=
  match s.status with
  | .running =>
      match s.pending with
      | [] => RTree.pure (PMF.pure (boundary H s))
      | S :: rest =>
          if hκ : 0 < s.κ then regionStep ρ R s S rest hκ
          else RTree.pure (PMF.pure { s with status := .failed })
  | _ => RTree.pure (PMF.pure s)

/-- The whole estimation run with `N` steps of fuel. -/
def estRun (H : WeightedGraph V) (ρ : ℝ) (R N : ℕ) (s : EstState V) :
    RTree (Finset V) ℝ (EstState V) (N * estStepBudget V R) :=
  RTree.iterate (estStep H ρ R) N s

end
end CutQueryComplexity.WeightedGraph
