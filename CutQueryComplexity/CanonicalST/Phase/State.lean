import CutQueryComplexity.CanonicalST.Basic
import CutQueryComplexity.Graph.EdgeSum

/-!
# Public learned state and guarded core-edge insertion

The state contains only the explicit learned core graph. The fixed outside
graph and canonical core are supplied by `CoreData`. The hidden input occurs
only in `Invariant` and in the correctness statements below. In particular,
neither an unknown edge set nor a target-feasibility witness is public data.

This module uses only frozen core and graph algebra. Its insertion is
definitionally the same graph addition used by the padded-witness layer.
-/

set_option autoImplicit false

namespace CutQueryComplexity.CanonicalST.Phase

open Finset WeightedGraph
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

structure State (V : Type) where
  L : WeightedGraph V

def State.initial (A : CoreData V) : State V := ⟨A.J⟩

def State.graph (P : State V) (A : CoreData V) : WeightedGraph V := A.K.add P.L

def State.insert (P : State V) (e : EdgeIndex V) : State V :=
  ⟨P.L.add (edgeGraph e 1 (by norm_num))⟩

/-- Public guards reject loops, noncore endpoints, and already learned pairs. -/
def Guard (A : CoreData V) (P : State V) (u v : V) : Prop :=
  u ≠ v ∧ u ∈ A.C ∧ v ∈ A.C ∧ (P.graph A).w u v = 0

def learn (A : CoreData V) (P : State V) (u v : V) : Option (State V) :=
  if h : Guard A P u v then some (P.insert ⟨(u, v), h.1⟩) else none

/-- Proof-only interpretation of the explicit learned graph. -/
structure Invariant (G : WeightedGraph V) (A : CoreData V) (P : State V) : Prop where
  seed_le : A.J.IsSubgraph P.L
  supported : ∀ u v, u ∉ A.C ∨ v ∉ A.C → P.L.w u v = 0
  unit : AllPairsAudit.Unweighted (P.graph A)
  subgraph : (P.graph A).IsSubgraph G

theorem initial_invariant {G : WeightedGraph V} {D : ℕ} {A : CoreData V}
    (hA : CoreSpec G D A) : Invariant G A (State.initial A) := by
  exact ⟨fun _ _ => le_rfl, hA.J_supported, hA.K_add_J_unit, hA.K_add_J_le⟩

omit [DecidableEq V] in
theorem State.graph_insert (P : State V) (A : CoreData V) (e : EdgeIndex V) :
    (P.insert e).graph A = (P.graph A).add (edgeGraph e 1 (by norm_num)) := by
  ext u v
  simp only [State.graph, State.insert, add_w, _root_.add_assoc]

omit [Fintype V] [DecidableEq V] in
theorem State.insert_mono (P : State V) (e : EdgeIndex V) :
    P.L.IsSubgraph (P.insert e).L := by
  intro u v
  exact le_add_of_nonneg_right ((edgeGraph e 1 (by norm_num)).nonneg u v)

theorem State.graph_insert_mono (P : State V) (A : CoreData V) (e : EdgeIndex V) :
    (P.graph A).IsSubgraph ((P.insert e).graph A) := by
  rw [State.graph_insert]
  intro u v
  exact le_add_of_nonneg_right ((edgeGraph e 1 (by norm_num)).nonneg u v)

omit [Fintype V] in
private theorem unitEdge_weight (e : EdgeIndex V) (u v : V) :
    (edgeGraph e 1 (by norm_num)).w u v =
      if (u, v) = e.val ∨ (v, u) = e.val then 1 else 0 := by
  have hn : ¬ ((u, v) = e.val ∧ (v, u) = e.val) := by
    rintro ⟨h₁, h₂⟩
    apply e.property
    exact (congrArg Prod.fst h₁).symm.trans (congrArg Prod.snd h₂)
  by_cases h₁ : (u, v) = e.val <;> by_cases h₂ : (v, u) = e.val <;>
    simp_all [edgeGraph]

omit [Fintype V] [DecidableEq V] in
private theorem weight_of_match (H : WeightedGraph V) (e : EdgeIndex V) {u v : V}
    (h : (u, v) = e.val ∨ (v, u) = e.val) : H.w u v = H.w e.val.1 e.val.2 := by
  rcases h with h | h
  · exact congrArg (fun p : V × V => H.w p.1 p.2) h
  · exact (H.symm u v).trans (congrArg (fun p : V × V => H.w p.1 p.2) h)

theorem insert_supported (A : CoreData V) (P : State V)
    (hsupp : ∀ u v, u ∉ A.C ∨ v ∉ A.C → P.L.w u v = 0)
    (e : EdgeIndex V) (hu : e.val.1 ∈ A.C) (hv : e.val.2 ∈ A.C) :
    ∀ x y, x ∉ A.C ∨ y ∉ A.C → (P.insert e).L.w x y = 0 := by
  intro x y hxy
  have hm : ¬ ((x, y) = e.val ∨ (y, x) = e.val) := by
    intro he
    rcases he with he | he
    · have hx : x ∈ A.C := (show x = e.val.1 from congrArg Prod.fst he).symm ▸ hu
      have hy : y ∈ A.C := (show y = e.val.2 from congrArg Prod.snd he).symm ▸ hv
      exact hxy.elim (fun h => h hx) (fun h => h hy)
    · have hy : y ∈ A.C := (show y = e.val.1 from congrArg Prod.fst he).symm ▸ hu
      have hx : x ∈ A.C := (show x = e.val.2 from congrArg Prod.snd he).symm ▸ hv
      exact hxy.elim (fun h => h hx) (fun h => h hy)
  change P.L.w x y + (edgeGraph e 1 (by norm_num)).w x y = 0
  rw [hsupp x y hxy, unitEdge_weight, ite_eq_right hm]
  norm_num

theorem insert_unit (A : CoreData V) (P : State V)
    (hunit : AllPairsAudit.Unweighted (P.graph A)) (e : EdgeIndex V)
    (hzero : (P.graph A).w e.val.1 e.val.2 = 0) :
    AllPairsAudit.Unweighted ((P.insert e).graph A) := by
  rw [State.graph_insert]
  intro u v
  change (P.graph A).w u v + (edgeGraph e 1 (by norm_num)).w u v = 0 ∨
    (P.graph A).w u v + (edgeGraph e 1 (by norm_num)).w u v = 1
  rw [unitEdge_weight]
  by_cases hm : (u, v) = e.val ∨ (v, u) = e.val
  · rw [ite_eq_left hm, weight_of_match (P.graph A) e hm, hzero]
    simp
  · simpa only [ite_eq_right hm, _root_.add_zero] using hunit u v

theorem insert_subgraph (A : CoreData V) (P : State V) (G : WeightedGraph V)
    (hPG : (P.graph A).IsSubgraph G) (e : EdgeIndex V)
    (hzero : (P.graph A).w e.val.1 e.val.2 = 0)
    (hactual : G.w e.val.1 e.val.2 = 1) :
    ((P.insert e).graph A).IsSubgraph G := by
  rw [State.graph_insert]
  intro u v
  change (P.graph A).w u v + (edgeGraph e 1 (by norm_num)).w u v ≤ G.w u v
  rw [unitEdge_weight]
  by_cases hm : (u, v) = e.val ∨ (v, u) = e.val
  · rw [ite_eq_left hm, weight_of_match (P.graph A) e hm, weight_of_match G e hm,
      hzero, hactual]
    norm_num
  · simpa only [ite_eq_right hm, _root_.add_zero] using hPG u v

theorem insert_invariant {G : WeightedGraph V} {A : CoreData V} {P : State V}
    (hP : Invariant G A P) (e : EdgeIndex V)
    (hu : e.val.1 ∈ A.C) (hv : e.val.2 ∈ A.C)
    (hzero : (P.graph A).w e.val.1 e.val.2 = 0)
    (hactual : G.w e.val.1 e.val.2 = 1) : Invariant G A (P.insert e) := by
  refine ⟨fun u v => (hP.seed_le u v).trans (P.insert_mono e u v),
    insert_supported A P hP.supported e hu hv,
    insert_unit A P hP.unit e hzero,
    insert_subgraph A P G hP.subgraph e hzero hactual⟩

/-- A genuine unknown edge passes the public core-membership guard because
the fixed outside graph was learned exactly during preprocessing. -/
theorem guard_of_actual {G : WeightedGraph V} {D : ℕ} {A : CoreData V}
    (hA : CoreSpec G D A) (P : State V) {u v : V}
    (hactual : G.w u v = 1) (hzero : (P.graph A).w u v = 0) : Guard A P u v := by
  have hne : u ≠ v := by
    intro he
    subst v
    rw [G.diag] at hactual
    norm_num at hactual
  have hcore : u ∈ A.C ∧ v ∈ A.C := by
    by_contra hnot
    have hK : A.K.w u v = 1 := by
      rw [hA.K_exact, ite_eq_right hnot, hactual]
    change A.K.w u v + P.L.w u v = 0 at hzero
    rw [hK] at hzero
    linarith [P.L.nonneg u v]
  exact ⟨hne, hcore.1, hcore.2, hzero⟩

omit [DecidableEq V] in
theorem learn_eq_some (A : CoreData V) (P : State V) (u v : V)
    (h : Guard A P u v) :
    learn A P u v = some (P.insert ⟨(u, v), h.1⟩) := by
  simp only [learn, dite_eq_left h]

omit [DecidableEq V] in
theorem learn_eq_none (A : CoreData V) (P : State V) (u v : V)
    (h : ¬ Guard A P u v) : learn A P u v = none := by
  simp only [learn, dite_eq_right h]

omit [DecidableEq V] in
theorem learn_success {A : CoreData V} {P Q : State V} {u v : V}
    (h : learn A P u v = some Q) :
    ∃ e : EdgeIndex V, e.val = (u, v) ∧ Guard A P u v ∧ Q = P.insert e := by
  unfold learn at h
  split_ifs at h with hg
  · exact ⟨⟨(u, v), hg.1⟩, rfl, hg, (Option.some.inj h).symm⟩

theorem learn_invariant {G : WeightedGraph V} {A : CoreData V} {P Q : State V}
    (hP : Invariant G A P) {u v : V}
    (hactual : G.w u v = 1) (hlearn : learn A P u v = some Q) :
    Invariant G A Q := by
  obtain ⟨e, he, hg, hQ⟩ := learn_success hlearn
  rw [hQ]
  apply insert_invariant hP e
  · simpa only [he] using hg.2.1
  · simpa only [he] using hg.2.2.1
  · simpa only [he] using hg.2.2.2
  · simpa only [he] using hactual

theorem learn_mono {A : CoreData V} {P Q : State V} {u v : V}
    (h : learn A P u v = some Q) : (P.graph A).IsSubgraph (Q.graph A) := by
  obtain ⟨e, _, _, rfl⟩ := learn_success h
  exact P.graph_insert_mono A e

/-- On a true search result the guarded branch cannot reject, and it returns
an explicit state preserving every learned-graph invariant. -/
theorem learn_actual {G : WeightedGraph V} {D : ℕ} {A : CoreData V}
    (hA : CoreSpec G D A) {P : State V} (hP : Invariant G A P) {u v : V}
    (hactual : G.w u v = 1) (hzero : (P.graph A).w u v = 0) :
    ∃ Q, learn A P u v = some Q ∧ Invariant G A Q ∧
      (P.graph A).IsSubgraph (Q.graph A) := by
  have hg := guard_of_actual hA P hactual hzero
  have he := learn_eq_some A P u v hg
  exact ⟨_, he, learn_invariant hP hactual he, learn_mono he⟩

end
end CutQueryComplexity.CanonicalST.Phase

#print axioms CutQueryComplexity.CanonicalST.Phase.initial_invariant
#print axioms CutQueryComplexity.CanonicalST.Phase.State.graph_insert
#print axioms CutQueryComplexity.CanonicalST.Phase.insert_invariant
#print axioms CutQueryComplexity.CanonicalST.Phase.guard_of_actual
#print axioms CutQueryComplexity.CanonicalST.Phase.learn_invariant
#print axioms CutQueryComplexity.CanonicalST.Phase.learn_mono
#print axioms CutQueryComplexity.CanonicalST.Phase.learn_actual
