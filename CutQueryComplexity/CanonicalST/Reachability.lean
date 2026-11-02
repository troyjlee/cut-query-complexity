import CutQueryComplexity.CanonicalST.Augmentation.MaxFlow
import CutQueryComplexity.Primitive.CrossSearch
import CutQueryComplexity.Primitive.Reductions

/-!
# Original residual reachability from an explicit integral flow

Used edges and their reverse residual arcs are public. Unused edges remain
undirected and are searched by subtracting the public used-edge graph from
each original cut query. No pure orientation of unknown pairs is assumed.
All loops have fixed vertex-count fuel, including on arbitrary answers.
-/

set_option autoImplicit false

namespace CutQueryComplexity.CanonicalST.Reachability

open Finset WeightedGraph Certificate
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Symmetrize the public used-pair predicate even for malformed input flows. -/
def usedGraph (g : V → V → ℝ) : WeightedGraph V where
  w u v := if u = v then 0 else if |g u v| = 1 ∨ |g v u| = 1 then 1 else 0
  symm u v := by
    by_cases h : u = v
    · subst v; rfl
    · simp only [h, Ne.symm h, ↓reduceIte, or_comm]
  nonneg u v := by split_ifs <;> norm_num
  diag u := by simp

theorem usedGraph_weight {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G)
    {s t : V} {r : ℝ} {g : V → V → ℝ} (hg : Augmentation.FlowSpec G s t r g)
    (u v : V) : (usedGraph g).w u v = |g u v| := by
  by_cases huv : u = v
  · subst v
    simp only [usedGraph, ↓reduceIte, hg.1.1.self, abs_zero]
  · have hswap := hg.1.1 u v
    rcases hg.unit_values hG u v with h | h | h <;>
      simp [usedGraph, huv, hswap, h]

theorem usedGraph_le {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G)
    {s t : V} {r : ℝ} {g : V → V → ℝ} (hg : Augmentation.FlowSpec G s t r g) :
    (usedGraph g).IsSubgraph G := by
  intro u v
  rw [usedGraph_weight hG hg]
  exact hg.1.2 u v

theorem unused_positive {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G)
    {s t : V} {r : ℝ} {g : V → V → ℝ} (hg : Augmentation.FlowSpec G s t r g)
    {u v : V} (hpos : 0 < (G.subtract (usedGraph g)).w u v) :
    G.w u v = 1 ∧ g u v = 0 := by
  change 0 < max 0 (G.w u v - (usedGraph g).w u v) at hpos
  rw [usedGraph_weight hG hg] at hpos
  have hlt : |g u v| < G.w u v := by
    rcases lt_max_iff.mp hpos with h | h
    · exact False.elim ((lt_irrefl 0) h)
    · linarith
  have hactual : G.w u v = 1 := (hG u v).resolve_left (by
    intro hz
    rw [hz] at hlt
    exact (not_lt_of_ge (abs_nonneg _)) hlt)
  refine ⟨hactual, ?_⟩
  rcases hg.unit_values hG u v with h | h | h
  · rw [hactual, h] at hlt; norm_num at hlt
  · exact h
  · rw [hactual, h] at hlt; norm_num at hlt

/-- The actual residual relation splits into known reverse arcs and unused
undirected edges. The compatibility is proved from integral unit feasibility. -/
theorem residual_iff {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G)
    {s t : V} {r : ℝ} {g : V → V → ℝ} (hg : Augmentation.FlowSpec G s t r g)
    (u v : V) :
    g u v < G.w u v ↔ g u v < 0 ∨ 0 < (G.subtract (usedGraph g)).w u v := by
  constructor
  · intro hres
    rcases hg.unit_values hG u v with h | h | h
    · exact Or.inl (by rw [h]; norm_num)
    · right
      change 0 < max 0 (G.w u v - (usedGraph g).w u v)
      rw [usedGraph_weight hG hg, h, abs_zero, sub_zero]
      exact lt_max_of_lt_right (by simpa only [h] using hres)
    · have hle := AllPairsAudit.unweighted_edge_le_one hG u v
      rw [h] at hres
      linarith
  · rintro (hneg | hpos)
    · exact hneg.trans_le (G.nonneg u v)
    · obtain ⟨hactual, hzero⟩ := unused_positive hG hg hpos
      rw [hactual, hzero]
      norm_num

def closure (g : V → V → ℝ) (S : Finset V) : Finset V :=
  univ.filter fun v => ∃ u ∈ S, Relation.ReflTransGen (fun x y => g x y < 0) u v

theorem mem_closure (g : V → V → ℝ) (S : Finset V) (v : V) :
    v ∈ closure g S ↔ ∃ u ∈ S, Relation.ReflTransGen (fun x y => g x y < 0) u v := by
  simp only [closure, mem_filter, mem_univ, true_and]

theorem subset_closure (g : V → V → ℝ) (S : Finset V) : S ⊆ closure g S := by
  intro v hv
  exact (mem_closure g S v).mpr ⟨v, hv, .refl⟩

theorem closure_closed (g : V → V → ℝ) (S : Finset V) {u v : V}
    (hu : u ∈ closure g S) (huv : g u v < 0) : v ∈ closure g S := by
  obtain ⟨x, hx, hpath⟩ := (mem_closure g S u).mp hu
  exact (mem_closure g S v).mpr ⟨x, hx, hpath.tail huv⟩

theorem closure_reachable (G : WeightedGraph V) (g : V → V → ℝ) (s : V)
    {S : Finset V} (hS : ∀ u ∈ S, Relation.ReflTransGen (fun x y => g x y < G.w x y) s u) :
    ∀ v ∈ closure g S, Relation.ReflTransGen (fun x y => g x y < G.w x y) s v := by
  intro v hv
  obtain ⟨u, hu, hpath⟩ := (mem_closure g S v).mp hv
  have hlift : Relation.ReflTransGen (fun x y => g x y < G.w x y) u v := by
    exact Relation.ReflTransGen.mono (fun a b hab => hab.trans_le (G.nonneg a b)) u v hpath
  exact (hS u hu).trans hlift

structure Invariant (G : WeightedGraph V) (g : V → V → ℝ) (s : V) (S : Finset V) : Prop where
  root : s ∈ S
  reachable : ∀ v ∈ S, Relation.ReflTransGen (fun x y => g x y < G.w x y) s v
  reverse_closed : ∀ u ∈ S, ∀ v, g u v < 0 → v ∈ S

theorem initial_invariant (G : WeightedGraph V) (g : V → V → ℝ) (s : V) :
    Invariant G g s (closure g {s}) := by
  refine ⟨subset_closure g {s} (mem_singleton_self s), ?_, ?_⟩
  · apply closure_reachable
    intro u hu
    have he : u = s := mem_singleton.mp hu
    subst u
    exact .refl
  · intro u hu v huv
    exact closure_closed g {s} hu huv

theorem extend_invariant {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G)
    {s t : V} {r : ℝ} {g : V → V → ℝ} (hg : Augmentation.FlowSpec G s t r g)
    {S : Finset V} (hS : Invariant G g s S) {u v : V} (hu : u ∈ S)
    (hpos : 0 < (G.subtract (usedGraph g)).w u v) :
    Invariant G g s (closure g (insert v S)) := by
  have hvpath := (hS.reachable u hu).tail ((residual_iff hG hg u v).mpr (Or.inr hpos))
  refine ⟨subset_closure g (insert v S) (mem_insert_of_mem hS.root), ?_, ?_⟩
  · apply closure_reachable
    intro x hx
    rcases mem_insert.mp hx with hx | hx
    · simpa only [hx] using hvpath
    · exact hS.reachable x hx
  · intro x hx y hxy
    exact closure_closed g (insert v S) hx hxy

def stepBudget (V : Type) [Fintype V] : ℕ := 6 * (searchDepth V + 1)

def searchUnused (g : V → V → ℝ) (S : Finset V) :
    DTree (Finset V) ℝ (Option (V × V)) (stepBudget V) :=
  ((findCross (searchDepth V) S Sᶜ).substitute (deletionQuery (usedGraph g))).cast
    (Nat.mul_one _)

theorem searchUnused_correct {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G)
    {s t : V} {r : ℝ} {g : V → V → ℝ} (hg : Augmentation.FlowSpec G s t r g)
    (S : Finset V) :
    CrossResult (G.subtract (usedGraph g)) S Sᶜ ((searchUnused g S).eval G.cut) := by
  have he : (fun T => (deletionQuery (usedGraph g) T).eval G.cut) =
      (G.subtract (usedGraph g)).cut := funext (deletionQuery_eval G _ (usedGraph_le hG hg))
  have hcast : (searchUnused g S).eval G.cut =
      ((findCross (searchDepth V) S Sᶜ).substitute
        (deletionQuery (usedGraph g))).eval G.cut :=
    DTree.eval_cast (Nat.mul_one (stepBudget V))
      ((findCross (searchDepth V) S Sᶜ).substitute
        (deletionQuery (usedGraph g))) G.cut
  rw [hcast, DTree.eval_substitute, he]
  exact findCross_logarithmic _ disjoint_compl_right

def run (g : V → V → ℝ) : (steps : ℕ) → Finset V →
    DTree (Finset V) ℝ (Finset V) (steps * stepBudget V)
  | 0, S => DTree.pure S
  | steps + 1, S =>
      ((searchUnused g S).bind fun answer => match answer with
        | none => DTree.pure S
        | some (u, v) =>
            if u ∈ S ∧ v ∉ S then run g steps (closure g (insert v S))
            else DTree.pure S).cast (by ring)

def queryBudget (V : Type) [Fintype V] : ℕ := Fintype.card V * stepBudget V

def program (g : V → V → ℝ) (s : V) :
    DTree (Finset V) ℝ (Finset V) (queryBudget V) := run g (Fintype.card V) (closure g {s})

theorem program_cost (g : V → V → ℝ) (s : V) (read : Finset V → ℝ) :
    (program g s).cost read ≤ 6 * Fintype.card V * (Nat.clog 2 (Fintype.card V) + 1) := by
  calc
    _ ≤ queryBudget V := DTree.cost_le (program g s) read
    _ = _ := by unfold queryBudget stepBudget searchDepth; ring

theorem saturated_of_no_unused {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G)
    {s t : V} {r : ℝ} {g : V → V → ℝ} (hg : Augmentation.FlowSpec G s t r g)
    {S : Finset V} (hS : Invariant G g s S)
    (hz : (G.subtract (usedGraph g)).cross S Sᶜ = 0) :
    ∀ u ∈ S, ∀ v ∉ S, g u v = G.w u v := by
  intro u hu v hv
  apply le_antisymm ((le_abs_self _).trans (hg.1.2 u v))
  by_contra hnot
  have hres : g u v < G.w u v := lt_of_not_ge hnot
  rcases (residual_iff hG hg u v).mp hres with hneg | hpos
  · exact hv (hS.reverse_closed u hu v hneg)
  · have hp : 0 < (G.subtract (usedGraph g)).cross S Sᶜ :=
      ((G.subtract (usedGraph g)).cross_pos_iff S Sᶜ).mpr
        ⟨u, hu, v, mem_compl.mpr hv, hpos⟩
    rw [hz] at hp
    exact (lt_irrefl 0) hp

theorem run_correct {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G)
    {s t : V} {r : ℝ} {g : V → V → ℝ} (hg : Augmentation.FlowSpec G s t r g)
    (steps : ℕ) (S : Finset V) (hS : Invariant G g s S)
    (hsteps : Fintype.card V - S.card < steps) :
    let T := (run g steps S).eval G.cut
    Invariant G g s T ∧ ∀ u ∈ T, ∀ v ∉ T, g u v = G.w u v := by
  induction steps generalizing S with
  | zero => omega
  | succ steps ih =>
      have hs := searchUnused_correct hG hg S
      simp only [run, DTree.eval_cast, DTree.eval_bind]
      cases he : (searchUnused g S).eval G.cut with
      | none =>
          simp only [he, CrossResult] at hs
          simp only [DTree.eval_pure]
          exact ⟨hS, saturated_of_no_unused hG hg hS hs⟩
      | some e =>
          rcases e with ⟨u, v⟩
          simp only [he, CrossResult] at hs
          have hv : v ∉ S := mem_compl.mp hs.2.1
          have hguard : u ∈ S ∧ v ∉ S := ⟨hs.1, hv⟩
          simp only [hguard]
          have hi := extend_invariant hG hg hS hs.1 hs.2.2
          have hcard : S.card + 1 ≤ (closure g (insert v S)).card := by
            rw [← card_insert_of_notMem hv]
            exact card_le_card (subset_closure g (insert v S))
          have hsmall : (closure g (insert v S)).card ≤ Fintype.card V := card_le_univ _
          apply ih _ hi
          omega

theorem program_reaches {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G)
    {s t : V} {r : ℝ} {g : V → V → ℝ} (hg : Augmentation.FlowSpec G s t r g) :
    let S := (program g s).eval G.cut
    Invariant G g s S ∧ (∀ u ∈ S, ∀ v ∉ S, g u v = G.w u v) ∧
      ∀ v, v ∈ S ↔ Relation.ReflTransGen (fun x y => g x y < G.w x y) s v := by
  have hi := initial_invariant G g s
  have hpos : 0 < (closure g {s}).card := card_pos.mpr ⟨s, hi.root⟩
  have hcard : (closure g {s}).card ≤ Fintype.card V := card_le_univ _
  obtain ⟨hs, hsat⟩ := run_correct hG hg (Fintype.card V) (closure g {s}) hi (by omega)
  refine ⟨hs, hsat, ?_⟩
  intro v
  constructor
  · exact hs.reachable v
  · intro hpath
    induction hpath with
    | refl => exact hs.root
    | @tail u v _ huv ih =>
        by_contra hnot
        rw [hsat u ih v hnot] at huv
        exact (lt_irrefl _) huv

/-- A maximum flow from the learned graph is interpreted in the original
graph by its proved feasibility and value equality. The actual query program
then computes the original residual reachable shore. -/
theorem program_correct {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G)
    {s t : V} (hst : s ≠ t) {r : ℝ} {g : V → V → ℝ}
    (hg : Augmentation.FlowSpec G s t r g) (hoptimal : r = Augmentation.terminalValue G s t) :
    let S := (program g s).eval G.cut
    s ∈ S ∧ t ∉ S ∧ G.cut S = r ∧
      (∀ T : Finset V, s ∈ T → t ∉ T → G.cut S ≤ G.cut T) ∧
      ∀ v, v ∈ S ↔ Relation.ReflTransGen (fun x y => g x y < G.w x y) s v := by
  obtain ⟨hi, hsat, hreach⟩ := program_reaches hG hg
  have ht : t ∉ (program g s).eval G.cut := by
    intro ht
    exact hg.no_residual_path hst hoptimal (hi.reachable t ht)
  have hcut : G.cut ((program g s).eval G.cut) = r := by
    calc
      _ = ∑ u ∈ (program g s).eval G.cut, ∑ v ∈ ((program g s).eval G.cut)ᶜ, g u v := by
        apply sum_congr rfl
        intro u hu
        apply sum_congr rfl
        intro v hv
        exact (hsat u hu v (mem_compl.mp hv)).symm
      _ = r := hg.cut_flow hi.root ht
  refine ⟨hi.root, ht, hcut, ?_, hreach⟩
  intro T hsT htT
  rw [hcut]
  exact hg.value_le_cut hsT htT

end
end CutQueryComplexity.CanonicalST.Reachability

#print axioms CutQueryComplexity.CanonicalST.Reachability.usedGraph_le
#print axioms CutQueryComplexity.CanonicalST.Reachability.residual_iff
#print axioms CutQueryComplexity.CanonicalST.Reachability.searchUnused_correct
#print axioms CutQueryComplexity.CanonicalST.Reachability.program_cost
#print axioms CutQueryComplexity.CanonicalST.Reachability.run_correct
#print axioms CutQueryComplexity.CanonicalST.Reachability.program_reaches
#print axioms CutQueryComplexity.CanonicalST.Reachability.program_correct
