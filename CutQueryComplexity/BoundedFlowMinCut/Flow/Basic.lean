import CutQueryComplexity.BoundedFlowMinCut.Basic
import CutQueryComplexity.CanonicalST.Reachability

/-! # Unit flows, augmenting paths and their support (M3)

A maintained flow is a signed integral `FlowSpec` of a unit graph `G`; its values
are in `{-1, 0, 1}`. A residual arc `u → v` is `f u v < G.w u v`.

`pathFlow p` is the signed unit flow along a vertex list `p`. Along a simple
residual path from `s` to `t` it is a feasible integral augmentation of value one
(`augment_flowSpec`, through the existing `add_residual_flow`). The support
`usedCount f`, the number of unordered edges carrying flow, grows by at most the
path's edge length: reversing a used edge cancels it rather than adding one.
-/

set_option autoImplicit false

namespace CutQueryComplexity.BoundedFlowMinCut
noncomputable section
open scoped Classical
open WeightedGraph Certificate CanonicalST DirectedUnitST.Repair

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A residual arc of the flow `f` in `G`. -/
def Res (G : WeightedGraph V) (f : V → V → ℝ) (u v : V) : Prop := f u v < G.w u v

/-- The indicator of `w = a`, as a real number. -/
def unitAt (a w : V) : ℝ := if w = a then 1 else 0

/-- One signed unit arc `x → y`. -/
def arcFlow (x y : V) (u v : V) : ℝ :=
  (if u = x ∧ v = y then 1 else 0) - (if u = y ∧ v = x then 1 else 0)

/-- The signed unit flow along a vertex list. -/
def pathFlow : List V → V → V → ℝ
  | x :: y :: rest => fun u v => arcFlow x y u v + pathFlow (y :: rest) u v
  | _ => fun _ _ => 0

/-- `(u, v)` are consecutive in `p`. -/
def Consec : List V → V → V → Prop
  | x :: y :: rest, u, v => (u = x ∧ v = y) ∨ Consec (y :: rest) u v
  | _, _, _ => False

omit [Fintype V] in
theorem arcFlow_isFlow (x y : V) : IsFlow (arcFlow x y) := by
  intro u v
  unfold arcFlow
  by_cases hxy : x = y
  · subst hxy
    simp
  · by_cases h1 : u = x <;> by_cases h2 : v = y <;> by_cases h3 : u = y <;> by_cases h4 : v = x <;>
      simp [h1, h2, h3, h4, hxy, Ne.symm hxy]

omit [Fintype V] in
theorem pathFlow_isFlow : ∀ p : List V, IsFlow (pathFlow p)
  | x :: y :: rest => by
      intro u v
      simp only [pathFlow]
      rw [arcFlow_isFlow x y u v, pathFlow_isFlow (y :: rest) u v]
      ring
  | [] => fun _ _ => by simp [pathFlow]
  | [_] => fun _ _ => by simp [pathFlow]

theorem netOut_arcFlow (x y w : V) : netOut (arcFlow x y) w = unitAt x w - unitAt y w := by
  simp only [netOut, arcFlow, unitAt, Finset.sum_sub_distrib]
  congr 1
  · by_cases h : w = x <;> simp [h]
  · by_cases h : w = y <;> simp [h]

theorem netOut_pathFlow : ∀ (p : List V) (hp : p ≠ []) (w : V),
    netOut (pathFlow p) w = unitAt (p.head hp) w - unitAt (p.getLast hp) w
  | [x], _, w => by
      simp only [pathFlow, netOut, Finset.sum_const_zero, List.head_cons, List.getLast_singleton,
        sub_self]
  | x :: y :: rest, _, w => by
      have h := netOut_pathFlow (y :: rest) (List.cons_ne_nil _ _) w
      have hsplit : netOut (pathFlow (x :: y :: rest)) w =
          netOut (arcFlow x y) w + netOut (pathFlow (y :: rest)) w := by
        simp only [pathFlow]
        exact netOut_add _ _ w
      rw [hsplit, netOut_arcFlow, h]
      simp only [List.head_cons, List.getLast_cons_cons]
      ring

omit [Fintype V] [DecidableEq V] in
theorem consec_mem : ∀ {p : List V} {u v : V}, Consec p u v → u ∈ p ∧ v ∈ p
  | x :: y :: rest, u, v, h => by
      rcases h with ⟨rfl, rfl⟩ | h
      · simp
      · obtain ⟨hu, hv⟩ := consec_mem h
        exact ⟨List.mem_cons_of_mem _ hu, List.mem_cons_of_mem _ hv⟩

omit [Fintype V] [DecidableEq V] in
theorem consec_rel {R : V → V → Prop} : ∀ {p : List V}, p.IsChain R → ∀ {u v : V},
    Consec p u v → R u v
  | x :: y :: rest, hc, u, v, h => by
      rw [List.isChain_cons_cons] at hc
      rcases h with ⟨rfl, rfl⟩ | h
      · exact hc.1
      · exact consec_rel hc.2 h

omit [Fintype V] in
/-- On a simple path, the flow is `+1` on its arcs, `-1` on their reverses, `0` elsewhere. -/
theorem pathFlow_eq : ∀ {p : List V}, p.Nodup → ∀ u v : V,
    pathFlow p u v = (if Consec p u v then 1 else 0) - (if Consec p v u then 1 else 0)
  | x :: y :: rest, hnd, u, v => by
      have hnd' : (y :: rest).Nodup := (List.nodup_cons.mp hnd).2
      have hx : x ∉ y :: rest := (List.nodup_cons.mp hnd).1
      simp only [pathFlow, Consec, arcFlow, pathFlow_eq hnd' u v]
      have h1 : ¬ (u = x ∧ v = y ∧ Consec (y :: rest) u v) := fun ⟨hu, _, hc⟩ =>
        hx (hu ▸ (consec_mem hc).1)
      have h2 : ¬ (v = x ∧ u = y ∧ Consec (y :: rest) v u) := fun ⟨hv, _, hc⟩ =>
        hx (hv ▸ (consec_mem hc).1)
      by_cases a : u = x ∧ v = y <;> by_cases b : Consec (y :: rest) u v <;>
        by_cases c : u = y ∧ v = x <;> by_cases d : Consec (y :: rest) v u <;>
        simp_all <;> aesop
  | [], _, u, v => by simp [pathFlow, Consec]
  | [_], _, u, v => by simp [pathFlow, Consec]

omit [Fintype V] in
theorem pathFlow_integer (p : List V) (hnd : p.Nodup) (u v : V) : IntegerValue (pathFlow p u v) := by
  rw [pathFlow_eq hnd]
  split_ifs
  · exact ⟨0, by norm_num⟩
  · exact ⟨1, by norm_num⟩
  · exact ⟨-1, by norm_num⟩
  · exact ⟨0, by norm_num⟩

/-- A simple residual path from `s` to `t`. -/
structure IsAugPath (G : WeightedGraph V) (f : V → V → ℝ) (s t : V) (p : List V) : Prop where
  ne_nil : p ≠ []
  head : p.head ne_nil = s
  last : p.getLast ne_nil = t
  nodup : p.Nodup
  chain : p.IsChain (Res G f)

/-- **Augmentation.** Adding the unit flow along a simple residual path keeps an
integral feasible flow and raises its value by one. -/
theorem augment_flowSpec {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G) {s t : V}
    {i : ℝ} {f : V → V → ℝ} (hf : Augmentation.FlowSpec G s t i f) {p : List V}
    (hp : IsAugPath G f s t p) :
    Augmentation.FlowSpec G s t (i + 1) (fun u v => f u v + pathFlow p u v) := by
  apply Augmentation.add_residual_flow hG hf (pathFlow_isFlow p)
  · intro u v
    rw [pathFlow_eq hp.nodup]
    by_cases hc : Consec p u v
    · have hres : f u v < G.w u v := consec_rel hp.chain hc
      have hcast := Augmentation.residualCapacity_cast hG hf u v
      have hpos : (0 : ℝ) < Augmentation.residualCapacity G f u v := by rw [hcast]; linarith
      have hone : (1 : ℝ) ≤ Augmentation.residualCapacity G f u v := by
        have : 0 < Augmentation.residualCapacity G f u v := by exact_mod_cast hpos
        exact_mod_cast this
      split_ifs <;> linarith
    · have := Nat.cast_nonneg (α := ℝ) (Augmentation.residualCapacity G f u v)
      simp only [hc, ite_false, zero_sub]
      split_ifs <;> linarith
  · intro x
    rw [netOut_pathFlow p hp.ne_nil x, hp.head, hp.last]
    rfl
  · exact pathFlow_integer p hp.nodup

/-! ### The support -/

/-- The number of unordered edges carrying flow, `q(f)`. -/
def usedCount (f : V → V → ℝ) : ℝ := (Reachability.usedGraph f).edgeMass

/-- The number of ordered consecutive pairs of a list is its edge length. -/
theorem card_consec_le : ∀ (p : List V),
    ((Finset.univ ×ˢ Finset.univ).filter (fun e : V × V => Consec p e.1 e.2)).card ≤ p.length - 1
  | x :: y :: rest => by
      have h := card_consec_le (y :: rest)
      have hsub : (Finset.univ ×ˢ Finset.univ).filter (fun e : V × V => Consec (x :: y :: rest) e.1 e.2) ⊆
          insert (x, y) ((Finset.univ ×ˢ Finset.univ).filter
            (fun e : V × V => Consec (y :: rest) e.1 e.2)) := by
        intro e he
        obtain ⟨-, hc⟩ := Finset.mem_filter.mp he
        rcases (show (e.1 = x ∧ e.2 = y) ∨ Consec (y :: rest) e.1 e.2 from hc) with ⟨h1, h2⟩ | h
        · exact Finset.mem_insert.mpr (Or.inl (Prod.ext h1 h2))
        · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨by simp, h⟩)
      calc
        _ ≤ _ := Finset.card_le_card hsub
        _ ≤ _ := Finset.card_insert_le _ _
        _ ≤ (y :: rest).length - 1 + 1 := Nat.add_le_add_right h 1
        _ = _ := by simp
  | [] => by
      have h : (Finset.univ ×ˢ Finset.univ).filter (fun e : V × V => Consec [] e.1 e.2) = ∅ :=
        Finset.filter_eq_empty_iff.mpr (fun _ _ h => h)
      rw [h]
      simp
  | [x] => by
      have h : (Finset.univ ×ˢ Finset.univ).filter (fun e : V × V => Consec [x] e.1 e.2) = ∅ :=
        Finset.filter_eq_empty_iff.mpr (fun _ _ h => h)
      rw [h]
      simp

/-- Augmenting along a simple path raises the support by at most its edge length. -/
theorem usedCount_augment_le {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G) {s t : V}
    {i : ℝ} {f : V → V → ℝ} (hf : Augmentation.FlowSpec G s t i f) {p : List V}
    (hp : IsAugPath G f s t p) :
    usedCount (fun u v => f u v + pathFlow p u v) ≤ usedCount f + (p.length - 1 : ℕ) := by
  have hf' := augment_flowSpec hG hf hp
  set ind : V → V → ℝ := fun u v => if Consec p u v ∨ Consec p v u then 1 else 0
  have hpoint : ∀ u v, (Reachability.usedGraph (fun u v => f u v + pathFlow p u v)).w u v ≤
      (Reachability.usedGraph f).w u v + ind u v := by
    intro u v
    rw [Reachability.usedGraph_weight hG hf', Reachability.usedGraph_weight hG hf]
    by_cases hc : Consec p u v ∨ Consec p v u
    · have h1 : |f u v + pathFlow p u v| ≤ 1 :=
        (hf'.1.2 u v).trans (AllPairsAudit.unweighted_edge_le_one hG u v)
      simp only [ind, hc, ite_true]
      linarith [abs_nonneg (f u v)]
    · have h0 : pathFlow p u v = 0 := by
        rw [pathFlow_eq hp.nodup]
        push Not at hc
        simp [hc.1, hc.2]
      simp only [ind, hc, ite_false, h0, add_zero, le_refl]
  have hind : ∑ u, ∑ v, ind u v ≤ 2 * ((p.length - 1 : ℕ) : ℝ) := by
    have hle : ∀ u v, ind u v ≤ (if Consec p u v then 1 else 0) + (if Consec p v u then 1 else 0) := by
      intro u v
      simp only [ind]
      split_ifs <;> simp_all
    have hcount : ∑ u, ∑ v, (if Consec p u v then (1 : ℝ) else 0) ≤ ((p.length - 1 : ℕ) : ℝ) := by
      have h := card_consec_le p
      rw [← Finset.sum_product' (f := fun u v => if Consec p u v then (1 : ℝ) else 0)]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast h
    have hcount' : ∑ u, ∑ v, (if Consec p v u then (1 : ℝ) else 0) ≤ ((p.length - 1 : ℕ) : ℝ) := by
      rw [Finset.sum_comm]
      exact hcount
    calc
      _ ≤ ∑ u, ∑ v, ((if Consec p u v then (1 : ℝ) else 0) + (if Consec p v u then 1 else 0)) :=
        Finset.sum_le_sum (fun u _ => Finset.sum_le_sum (fun v _ => hle u v))
      _ = (∑ u, ∑ v, if Consec p u v then (1 : ℝ) else 0) +
          ∑ u, ∑ v, (if Consec p v u then (1 : ℝ) else 0) := by
        simp only [Finset.sum_add_distrib]
      _ ≤ _ := by linarith
  unfold usedCount WeightedGraph.edgeMass
  have hsum : ∑ u, ∑ v, (Reachability.usedGraph (fun u v => f u v + pathFlow p u v)).w u v ≤
      ∑ u, ∑ v, (Reachability.usedGraph f).w u v + ∑ u, ∑ v, ind u v := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun u _ => by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum (fun v _ => hpoint u v))
  linarith

end
end CutQueryComplexity.BoundedFlowMinCut
