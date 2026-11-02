import CutQueryComplexity.Certificate.TreePattern.Costs
import CutQueryComplexity.Certificate.MaxFlow
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.List.Nodup

/-!
# Public tree potentials and the zero-cost forest

Tree potentials are fixed integral sums along unique tree paths. Nonzero
signed sums of the public costs imply that every zero-reduced-cost graph is
acyclic, for arbitrary real potentials. In particular the zeros of a public
tree potential are exactly its tree edges.
-/

set_option autoImplicit false

namespace CutQueryComplexity.Certificate.TreePattern

open Finset _root_.SimpleGraph
open scoped Classical
noncomputable section

abbrev LabelledTree (n : ℕ) := {T : SimpleGraph (Fin n) // T.IsTree}

variable {n : ℕ}

def dartPair {G : SimpleGraph (Fin n)} (d : G.Dart) : Pair n :=
  if h : d.fst < d.snd then ⟨(d.fst, d.snd), h⟩
  else ⟨(d.snd, d.fst), lt_of_le_of_ne (le_of_not_gt h) d.snd_ne_fst⟩

theorem dartPair_edge {G : SimpleGraph (Fin n)} (d : G.Dart) :
    s((dartPair d).val.1, (dartPair d).val.2) = d.edge := by
  unfold dartPair
  split_ifs
  · rfl
  · exact Sym2.eq_swap

def dartSign {G : SimpleGraph (Fin n)} (d : G.Dart) : ℤ :=
  if d.fst < d.snd then 1 else -1

theorem abs_dartSign {G : SimpleGraph (Fin n)} (d : G.Dart) : |dartSign d| = 1 := by
  simp only [dartSign]
  split_ifs <;> norm_num

theorem publicCost_dart {G : SimpleGraph (Fin n)} (d : G.Dart) :
    publicCost d.fst d.snd = dartSign d * pairCost (dartPair d) := by
  by_cases h : d.fst < d.snd
  · simp [dartPair, dartSign, h, publicCost, pairCost, pairIndex]
  · have hr : d.snd < d.fst := lt_of_le_of_ne (le_of_not_gt h) d.snd_ne_fst
    simp [dartPair, dartSign, h, hr, publicCost, pairCost, pairIndex]

def walkCost {G : SimpleGraph (Fin n)} {u v : Fin n} (p : G.Walk u v) : ℤ :=
  (p.darts.map fun d => publicCost d.fst d.snd).sum

@[simp] theorem walkCost_nil {G : SimpleGraph (Fin n)} (u : Fin n) :
    walkCost (G := G) (.nil : G.Walk u u) = 0 := by simp [walkCost]

@[simp] theorem walkCost_cons {G : SimpleGraph (Fin n)} {u v w : Fin n}
    (h : G.Adj u v) (p : G.Walk v w) :
    walkCost (.cons h p) = publicCost u v + walkCost p := by simp [walkCost]

theorem walkCost_append {G : SimpleGraph (Fin n)} {u v w : Fin n}
    (p : G.Walk u v) (q : G.Walk v w) :
    walkCost (p.append q) = walkCost p + walkCost q := by
  simp [walkCost, SimpleGraph.Walk.darts_append]

theorem walkCost_concat {G : SimpleGraph (Fin n)} {u v w : Fin n}
    (p : G.Walk u v) (h : G.Adj v w) :
    walkCost (p.concat h) = walkCost p + publicCost v w := by
  simp [walkCost, SimpleGraph.Walk.darts_concat]

/-- Every nonempty trail has nonzero signed public cost. -/
theorem walkCost_ne_zero_of_isTrail {G : SimpleGraph (Fin n)} {u v : Fin n}
    (p : G.Walk u v) (hp : p.IsTrail) (hne : ¬p.Nil) : walkCost p ≠ 0 := by
  have hmap : (p.darts.map SimpleGraph.Dart.edge).Nodup := hp.edges_nodup
  have hd : p.darts.Nodup := List.Nodup.of_map _ hmap
  have hS : p.darts.toFinset.Nonempty := by
    apply (List.toFinset_nonempty_iff _).mpr
    exact fun h => hne (SimpleGraph.Walk.darts_eq_nil.mp h)
  have hinj : Set.InjOn (fun d : G.Dart => pairIndex (dartPair d)) p.darts.toFinset := by
    intro d hd e he h
    have hpair := pairIndex_injective h
    have hedge : d.edge = e.edge := by
      rw [← dartPair_edge d, ← dartPair_edge e, hpair]
    exact List.inj_on_of_nodup_map hmap (List.mem_toFinset.mp hd)
      (List.mem_toFinset.mp he) hedge
  have hs := signed_two_pow_sum_ne_zero p.darts.toFinset hS
    (fun d => pairIndex (dartPair d)) dartSign hinj (fun d _ => abs_dartSign d)
  have heq : ∑ d ∈ p.darts.toFinset,
      dartSign d * (2 : ℤ) ^ pairIndex (dartPair d) = walkCost p := by
    rw [List.sum_toFinset _ hd]
    unfold walkCost
    congr 1
    apply List.map_congr_left
    intro d _
    exact (publicCost_dart d).symm
  rwa [heq] at hs

theorem walkCost_of_potential {G : SimpleGraph (Fin n)} (p : Fin n → ℝ)
    (hp : ∀ u v, G.Adj u v → (publicCost u v : ℝ) = p u - p v)
    {u v : Fin n} (w : G.Walk u v) : (walkCost w : ℝ) = p u - p v := by
  induction w with
  | nil => simp
  | @cons u v w h q ih =>
      rw [walkCost_cons, Int.cast_add, hp u v h, ih]
      ring

/-- The equality graph of an arbitrary real potential. -/
def zeroGraph (p : Fin n → ℝ) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ (publicCost u v : ℝ) = p u - p v
  symm := ⟨by
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    rw [publicCost_reverse, Int.cast_neg, h.2]
    ring⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

theorem zeroGraph_isAcyclic (p : Fin n → ℝ) : (zeroGraph p).IsAcyclic := by
  intro v c hc
  have hne := walkCost_ne_zero_of_isTrail c hc.isTrail hc.not_nil
  have heq := walkCost_of_potential (G := zeroGraph p) p (fun _ _ h => h.2) c
  have hz : (walkCost c : ℝ) = 0 := by simpa using heq
  exact hne (by exact_mod_cast hz)

def treeRoot (hn : 2 ≤ n) : Fin n := ⟨0, by omega⟩

def treePath (T : LabelledTree n) (u v : Fin n) : T.val.Walk u v :=
  (T.property.existsUnique_path u v).choose

theorem treePath_isPath (T : LabelledTree n) (u v : Fin n) :
    (treePath T u v).IsPath :=
  (T.property.existsUnique_path u v).choose_spec.1

/-- A public integral potential obtained from the unique rooted paths. -/
def treePotential (hn : 2 ≤ n) (T : LabelledTree n) (v : Fin n) : ℤ :=
  -walkCost (treePath T (treeRoot hn) v)

theorem treePotential_root (hn : 2 ≤ n) (T : LabelledTree n) :
    treePotential hn T (treeRoot hn) = 0 := by
  have heq : treePath T (treeRoot hn) (treeRoot hn) = .nil :=
    ((T.property.existsUnique_path _ _).choose_spec.2 _ SimpleGraph.Walk.IsPath.nil).symm
  simp [treePotential, heq]

theorem treePotential_edge (hn : 2 ≤ n) (T : LabelledTree n) {u v : Fin n}
    (h : T.val.Adj u v) : treePotential hn T u - treePotential hn T v = publicCost u v := by
  let pu := treePath T (treeRoot hn) u
  let pv := treePath T (treeRoot hn) v
  have hu := treePath_isPath T (treeRoot hn) u
  have hv := treePath_isPath T (treeRoot hn) v
  change -walkCost pu - -walkCost pv = publicCost u v
  by_cases huin : u ∈ pv.support
  · have heq : pv = pu.concat h := T.property.isAcyclic.path_concat hu hv h huin
    rw [heq, walkCost_concat]
    ring
  · have hvin : v ∈ pu.support :=
      T.property.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath hu hv h huin
    have heq : pu = pv.concat h.symm := T.property.isAcyclic.path_concat hv hu h.symm hvin
    rw [heq, walkCost_concat, publicCost_reverse]
    ring

theorem treePotential_unique (hn : 2 ≤ n) (T : LabelledTree n) (p : Fin n → ℝ)
    (hp : ∀ u v, T.val.Adj u v → (publicCost u v : ℝ) = p u - p v) (v : Fin n) :
    (treePotential hn T v : ℝ) = p v - p (treeRoot hn) := by
  rw [treePotential, Int.cast_neg, walkCost_of_potential p hp]
  ring

theorem zeroGraph_treePotential (hn : 2 ≤ n) (T : LabelledTree n) :
    zeroGraph (fun v => (treePotential hn T v : ℝ)) = T.val := by
  have hle : T.val ≤ zeroGraph (fun v => (treePotential hn T v : ℝ)) := by
    intro u v h
    refine ⟨h.ne, ?_⟩
    change (publicCost u v : ℝ) = (treePotential hn T u : ℝ) -
      (treePotential hn T v : ℝ)
    exact_mod_cast (treePotential_edge hn T h).symm
  have hm := (SimpleGraph.isTree_iff_maximal_isAcyclic.mp T.property).2
  exact (hm.eq_of_le (zeroGraph_isAcyclic _) hle).symm

def reducedCost (hn : 2 ≤ n) (T : LabelledTree n) (u v : Fin n) : ℤ :=
  publicCost u v - (treePotential hn T u - treePotential hn T v)

@[simp] theorem reducedCost_self (hn : 2 ≤ n) (T : LabelledTree n) (v : Fin n) :
    reducedCost hn T v v = 0 := by simp [reducedCost]

theorem reducedCost_reverse (hn : 2 ≤ n) (T : LabelledTree n) (u v : Fin n) :
    reducedCost hn T v u = -reducedCost hn T u v := by
  rw [reducedCost, reducedCost, publicCost_reverse]
  ring

theorem reducedCost_eq_zero_iff (hn : 2 ≤ n) (T : LabelledTree n) {u v : Fin n}
    (huv : u ≠ v) : reducedCost hn T u v = 0 ↔ T.val.Adj u v := by
  have hzero := zeroGraph_treePotential hn T
  constructor
  · intro h
    rw [← hzero]
    refine ⟨huv, ?_⟩
    have heq : publicCost u v = treePotential hn T u - treePotential hn T v := by
      simpa only [reducedCost, sub_eq_zero] using h
    change (publicCost u v : ℝ) = (treePotential hn T u : ℝ) -
      (treePotential hn T v : ℝ)
    exact_mod_cast heq
  · intro h
    simp [reducedCost, treePotential_edge hn T h]

/-- A fixed root is available from a tree's nonempty vertex type. -/
def correctionRoot (T : LabelledTree n) : Fin n :=
  ⟨0, by simpa using (Fintype.card_pos_iff.mpr T.property.nonempty)⟩

/-- A unit route on the public tree, constructed by the existing walk lemma. -/
def treeRoute (T : LabelledTree n) (u v : Fin n) : Fin n → Fin n → ℝ :=
  (exists_walkFlow T.val.Adj ((T.val.reachable_iff_reflTransGen u v).mp
    (T.property.connected u v))).choose

theorem treeRoute_spec (T : LabelledTree n) (u v : Fin n) :
    IsFlow (treeRoute T u v) ∧
      (∀ a b, 0 < treeRoute T u v a b → T.val.Adj a b) ∧
      ∀ x, netOut (treeRoute T u v) x = (if x = u then 1 else 0) -
        (if x = v then 1 else 0) :=
  (exists_walkFlow T.val.Adj ((T.val.reachable_iff_reflTransGen u v).mp
    (T.property.connected u v))).choose_spec

theorem treeRoute_eq_zero (T : LabelledTree n) (u v a b : Fin n)
    (hab : ¬T.val.Adj a b) : treeRoute T u v a b = 0 := by
  have h := treeRoute_spec T u v
  rcases lt_trichotomy (treeRoute T u v a b) 0 with hneg | hz | hpos
  · have hr : 0 < treeRoute T u v b a := by rw [h.1 a b]; linarith
    exact (hab (h.2.1 b a hr).symm).elim
  · exact hz
  · exact (hab (h.2.1 a b hpos)).elim

/-- Explicit linear tree solver: route each vertex's demand to the root. -/
def treeCorrection (T : LabelledTree n) (d : Fin n → ℝ) (a b : Fin n) : ℝ :=
  ∑ v, d v * treeRoute T v (correctionRoot T) a b

theorem treeCorrection_isFlow (T : LabelledTree n) (d : Fin n → ℝ) :
    IsFlow (treeCorrection T d) := by
  intro a b
  unfold treeCorrection
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro v _
  rw [(treeRoute_spec T v (correctionRoot T)).1 a b]
  ring

theorem treeCorrection_eq_zero (T : LabelledTree n) (d : Fin n → ℝ)
    (a b : Fin n) (hab : ¬T.val.Adj a b) : treeCorrection T d a b = 0 := by
  apply sum_eq_zero
  intro v _
  rw [treeRoute_eq_zero T v (correctionRoot T) a b hab, mul_zero]

theorem treeCorrection_netOut (T : LabelledTree n) (d : Fin n → ℝ)
    (hd : ∑ v, d v = 0) (x : Fin n) : netOut (treeCorrection T d) x = d x := by
  calc
    netOut (treeCorrection T d) x =
        ∑ v, d v * netOut (treeRoute T v (correctionRoot T)) x := by
      simp only [netOut, treeCorrection, mul_sum]
      exact sum_comm
    _ = ∑ v, d v * ((if x = v then 1 else 0) -
        (if x = correctionRoot T then 1 else 0)) := by
      apply sum_congr rfl
      intro v _
      rw [(treeRoute_spec T v (correctionRoot T)).2.2 x]
    _ = d x := by
      by_cases hx : x = correctionRoot T
      · simp [hx, mul_sub, sum_sub_distrib, hd]
      · simp [hx]

/-- The component at u after deleting the public tree edge uv. -/
def edgeSide (T : LabelledTree n) (u v : Fin n) : Finset (Fin n) :=
  univ.filter fun x => (T.val.deleteEdges {s(u,v)}).Reachable u x

@[simp] theorem mem_edgeSide (T : LabelledTree n) (u v x : Fin n) :
    x ∈ edgeSide T u v ↔ (T.val.deleteEdges {s(u,v)}).Reachable u x := by
  simp [edgeSide]

theorem self_mem_edgeSide (T : LabelledTree n) (u v : Fin n) :
    u ∈ edgeSide T u v := by
  exact (mem_edgeSide T u v u).mpr (.refl u)

theorem other_not_mem_edgeSide (T : LabelledTree n) {u v : Fin n}
    (huv : T.val.Adj u v) : v ∉ edgeSide T u v := by
  have hb := (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp T.property.isAcyclic) huv
  exact fun h => (SimpleGraph.isBridge_iff.mp hb) ((mem_edgeSide T u v v).mp h)

theorem edgeSide_cross (T : LabelledTree n) {u v a b : Fin n}
    (huv : T.val.Adj u v) (ha : a ∈ edgeSide T u v) (hb : b ∉ edgeSide T u v)
    (hab : T.val.Adj a b) : a = u ∧ b = v := by
  have he : s(a,b) = s(u,v) := by
    by_contra hne
    have hdel : (T.val.deleteEdges {s(u,v)}).Adj a b :=
      SimpleGraph.deleteEdges_adj.mpr ⟨hab, by simpa using hne⟩
    exact hb ((mem_edgeSide T u v b).mpr
      (((mem_edgeSide T u v a).mp ha).trans hdel.reachable))
  rcases Sym2.eq_iff.mp he with h | h
  · exact h
  · exact (other_not_mem_edgeSide T huv (h.1 ▸ ha)).elim

/-- A tree-supported flow is recovered on each edge by one fundamental cut. -/
theorem edgeSide_netOut (T : LabelledTree n) {f : Fin n → Fin n → ℝ}
    (hf : IsFlow f) (hs : ∀ a b, ¬T.val.Adj a b → f a b = 0)
    {u v : Fin n} (huv : T.val.Adj u v) :
    ∑ x ∈ edgeSide T u v, netOut f x = f u v := by
  rw [sum_netOut_eq hf]
  rw [sum_eq_single u]
  · rw [sum_eq_single v]
    · intro b hb hbv
      apply hs
      intro hub
      exact hbv (edgeSide_cross T huv (self_mem_edgeSide T u v)
        (mem_compl.mp hb) hub).2
    · intro hv
      exact (hv (mem_compl.mpr (other_not_mem_edgeSide T huv))).elim
  · intro a ha hau
    apply sum_eq_zero
    intro b hb
    apply hs
    intro hab
    exact hau (edgeSide_cross T huv ha (mem_compl.mp hb) hab).1
  · intro hu
    exact (hu (self_mem_edgeSide T u v)).elim

theorem treeSupported_flow_unique (T : LabelledTree n)
    {f g : Fin n → Fin n → ℝ} (hf : IsFlow f) (hg : IsFlow g)
    (hsf : ∀ a b, ¬T.val.Adj a b → f a b = 0)
    (hsg : ∀ a b, ¬T.val.Adj a b → g a b = 0)
    (hdiv : ∀ v, netOut f v = netOut g v) : f = g := by
  funext u v
  by_cases huv : T.val.Adj u v
  · rw [← edgeSide_netOut T hf hsf huv, ← edgeSide_netOut T hg hsg huv]
    exact sum_congr rfl fun x _ => hdiv x
  · rw [hsf u v huv, hsg u v huv]

theorem treeCorrection_unique (T : LabelledTree n) (d : Fin n → ℝ)
    (hd : ∑ v, d v = 0) {f : Fin n → Fin n → ℝ}
    (hf : IsFlow f) (hs : ∀ a b, ¬T.val.Adj a b → f a b = 0)
    (hdiv : ∀ v, netOut f v = d v) : f = treeCorrection T d := by
  apply treeSupported_flow_unique T hf (treeCorrection_isFlow T d) hs
    (treeCorrection_eq_zero T d)
  intro v
  rw [hdiv v, treeCorrection_netOut T d hd v]

end
end CutQueryComplexity.Certificate.TreePattern

#print axioms CutQueryComplexity.Certificate.TreePattern.walkCost_ne_zero_of_isTrail
#print axioms CutQueryComplexity.Certificate.TreePattern.zeroGraph_isAcyclic
#print axioms CutQueryComplexity.Certificate.TreePattern.treePotential_root
#print axioms CutQueryComplexity.Certificate.TreePattern.treePotential_edge
#print axioms CutQueryComplexity.Certificate.TreePattern.treePotential_unique
#print axioms CutQueryComplexity.Certificate.TreePattern.zeroGraph_treePotential
#print axioms CutQueryComplexity.Certificate.TreePattern.reducedCost_eq_zero_iff
#print axioms CutQueryComplexity.Certificate.TreePattern.treeCorrection_netOut
#print axioms CutQueryComplexity.Certificate.TreePattern.edgeSide_netOut
#print axioms CutQueryComplexity.Certificate.TreePattern.treeSupported_flow_unique
#print axioms CutQueryComplexity.Certificate.TreePattern.treeCorrection_unique
