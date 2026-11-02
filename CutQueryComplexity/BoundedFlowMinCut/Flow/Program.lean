import CutQueryComplexity.BoundedFlowMinCut.Flow.Repair
import CutQueryComplexity.BoundedFlowMinCut.Flow.Shortcut
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # The bounded max-flow routine (M6)

`boundedFlow deg d s t` takes public terminals, a threshold `d ≥ 1` and the
cached degrees. It builds one spanning forest of `G` (the unused graph of the
zero flow), then repeats with flow value `i`:

* no witness path: return the witness-reachable set and the value `i`, an exact
  minimum `s`–`t` shore (`witnessPath_none`);
* a witness path and `i = d`: report overflow; augmenting along that known path
  gives a flow of value `d + 1`, so every `s`–`t` cut is at least `d + 1`;
* a witness path and `i < d`: shorten it (`shortcutLoop`), augment, and repair
  the forest (`repairForest`).

**Support recurrence.** A shortened path has `d (|π| - 1) ≤ 8 (n + q_i)` and
augmenting adds at most `|π| - 1` used edges, so
`n + q_{i+1} ≤ (n + q_i)(1 + 8/d)` and `n + q_i ≤ n (1 + 8/d)^i ≤ 3^8 n` for
`i ≤ d` (`support_step`, `growth_le`, through `(1 + 8/d)^d ≤ e^8`). The bound
holds at every step, not only for the final flow, so every augmented path has
at most `1 + 8 · 3^8 n / d` vertices even when later augmentations cancel earlier
flow; the at most `d` augmented paths have at most `d + 8 · 3^8 n` vertices in all.

**Cost.** Per augmentation, shortening costs `13 L (3 n L / d + 1)` and repair
`6 L (1 + 8 · 3^8 n / d)` (`augCharge`); with `d ≤ n` the `d` augmentations and the
initial forest cost at most `flowCap n = (70 + 48 · 3^8) n L²`
(`boundedFlow_spec`). `boundedFlowTree` compiles the program with that cap.
-/

set_option autoImplicit false

namespace CutQueryComplexity.BoundedFlowMinCut
noncomputable section
open scoped Classical
open WeightedGraph Certificate CanonicalST DirectedUnitST.Repair GHReduction

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The two certified outcomes of the bounded flow. -/
inductive FlowOutcome (V : Type) where
  /-- A minimum `s`–`t` shore and its value. -/
  | cut (S : Finset V) (value : ℕ)
  /-- Every `s`–`t` cut exceeds the threshold. -/
  | overflow

/-- What each outcome certifies. -/
def FlowOutcome.Valid (G : WeightedGraph V) (d : ℕ) (s t : V) : FlowOutcome V → Prop
  | .cut S v => IsSTMinCut G s t S ∧ G.cut S = v ∧ v ≤ d
  | .overflow => ∀ S : Finset V, s ∈ S → t ∉ S → (d : ℝ) + 1 ≤ G.cut S

/-- The witness-reachable set from `s`. -/
def witnessSet (T : _root_.SimpleGraph V) (f : V → V → ℝ) (s : V) : Finset V :=
  Finset.univ.filter (fun v => Relation.ReflTransGen (Witness T f) s v)

/-- The augmentation loop from flow value `i` with `fuel = d - i` augmentations left:
search the witness offline; with no path return the witness set; with a path and
no fuel left (value `d`) report overflow; otherwise shorten, augment and repair. -/
def flowLoop (deg : V → ℕ) (d : ℕ) (s t : V) :
    ℕ → ℕ → (V → V → ℝ) → _root_.SimpleGraph V → Prog (Finset V) ℝ (FlowOutcome V)
  | 0, i, f, T => .pure (match witnessPath T f s t with
      | none => .cut (witnessSet T f s) i
      | some _ => .overflow)
  | fuel + 1, i, f, T => match witnessPath T f s t with
      | none => .pure (.cut (witnessSet T f s) i)
      | some π => (shortcutLoop deg d f (Fintype.card V) π).bind fun π' =>
          (repairForest T f π').bind fun T' =>
            flowLoop deg d s t fuel (i + 1) (fun u v => f u v + pathFlow π' u v) T'

/-- **Bounded max-flow.** One spanning forest, then at most `d` augmentations. -/
def boundedFlow (deg : V → ℕ) (d : ℕ) (s t : V) : Prog (Finset V) ℝ (FlowOutcome V) :=
  (liftDTree spanningForest).bind fun T => flowLoop deg d s t d 0 (fun _ _ => 0) T

/-! ### The support recurrence -/

/-- `(1 + 8/d)^i ≤ 3^8` for `i ≤ d`, through `(1 + 8/d)^d ≤ e^8`. -/
theorem growth_le {d i : ℕ} (hd : 1 ≤ d) (hi : i ≤ d) : (1 + 8 / (d : ℝ)) ^ i ≤ 3 ^ 8 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : (1 : ℝ) ≤ 1 + 8 / d := le_add_of_nonneg_right (by positivity)
  calc (1 + 8 / (d : ℝ)) ^ i ≤ (1 + 8 / (d : ℝ)) ^ d := pow_le_pow_right₀ h1 hi
    _ ≤ Real.exp (8 / d) ^ d := by
        apply pow_le_pow_left₀ (by linarith)
        have := Real.add_one_le_exp (8 / (d : ℝ))
        linarith
    _ = Real.exp 8 := by rw [← Real.exp_nat_mul]; congr 1; field_simp
    _ = Real.exp 1 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ 3 ^ 8 := by
        apply pow_le_pow_left₀ (Real.exp_pos 1).le
        exact Real.exp_one_lt_three.le

/-- One augmentation along a short path multiplies `n + q` by at most `1 + 8/d`. -/
theorem support_step {n q q' r d : ℝ} (hd : 0 < d) (hq' : q' ≤ q + (r - 1))
    (hshort : d * (r - 1) ≤ 8 * (n + q)) : n + q' ≤ (n + q) * (1 + 8 / d) := by
  have : r - 1 ≤ 8 * (n + q) / d := by rw [le_div_iff₀ hd]; linarith
  have h2 : (n + q) * (1 + 8 / d) = n + q + 8 * (n + q) / d := by field_simp
  linarith

/-- The charge of one augmentation: shortening plus repair. -/
def augCharge (n L d : ℕ) : ℝ :=
  13 * L * (3 * n * L / d + 1) + 6 * L * (1 + 8 * 3 ^ 8 * n / d)

theorem zero_flowSpec (G : WeightedGraph V) (s t : V) :
    Augmentation.FlowSpec G s t 0 (fun _ _ => 0) := by
  refine ⟨⟨fun u v => by simp, fun u v => by simpa using G.nonneg u v⟩, fun x => ?_,
    fun u v => IntegerValue.zero⟩
  simp [netOut]

theorem usedCount_zero : usedCount (fun _ _ : V => (0 : ℝ)) = 0 := by
  simp [usedCount, WeightedGraph.edgeMass, Reachability.usedGraph]

omit [Fintype V] in
theorem unusedGraph_zero (G : WeightedGraph V) : unusedGraph G (fun _ _ => 0) = G := by
  ext u v
  simp [unusedGraph, WeightedGraph.subtract, Reachability.usedGraph, G.nonneg u v]

theorem augCharge_nonneg (n L d : ℕ) : 0 ≤ augCharge n L d := by
  unfold augCharge
  positivity

/-- **The augmentation loop.** From an integral flow of value `i` with
`i + fuel = d`, a spanning forest of its unused graph and the support bound
`n + q ≤ n (1 + 8/d)^i`, the outcome is valid and the loop spends at most `fuel`
augmentation charges. -/
theorem flowLoop_spec {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G) {d : ℕ}
    (hd : 1 ≤ d) (hδ : ∀ v, d ≤ natDegree G v) {deg : V → ℕ} (hdeg : ∀ v, deg v = natDegree G v)
    {s t : V} :
    ∀ (fuel i : ℕ) (f : V → V → ℝ) (T : _root_.SimpleGraph V), i + fuel = d →
      Augmentation.FlowSpec G s t i f → IsSpanningForest (unusedGraph G f) T →
      (Fintype.card V : ℝ) + usedCount f ≤ Fintype.card V * (1 + 8 / (d : ℝ)) ^ i →
      (Prog.eval G.cut (flowLoop deg d s t fuel i f T)).Valid G d s t ∧
        (Prog.cost G.cut (flowLoop deg d s t fuel i f T) : ℝ) ≤
          fuel * augCharge (Fintype.card V) (logFactor (Fintype.card V)) d := by
  intro fuel
  induction fuel with
  | zero =>
      intro i f T hid hf hT _
      have hi : i = d := by omega
      subst hi
      cases hw : witnessPath T f s t with
      | none =>
          obtain ⟨hcut, hmin⟩ := witnessPath_none hG hf hT hw
          simp only [flowLoop, hw, Prog.eval_pure, Prog.cost_pure, FlowOutcome.Valid,
            Nat.cast_zero, zero_mul, le_refl, and_true]
          exact ⟨hmin, hcut⟩
      | some π =>
          have hf' := augment_flowSpec hG hf (witnessPath_some hG hf hT.1 hw)
          simp only [flowLoop, hw, Prog.eval_pure, Prog.cost_pure, FlowOutcome.Valid,
            Nat.cast_zero, zero_mul, le_refl, and_true]
          exact fun S hs ht => hf'.value_le_cut hs ht
  | succ fuel ih =>
      intro i f T hid hf hT hsupp
      cases hw : witnessPath T f s t with
      | none =>
          obtain ⟨hcut, hmin⟩ := witnessPath_none hG hf hT hw
          simp only [flowLoop, hw, Prog.eval_pure, Prog.cost_pure, FlowOutcome.Valid,
            Nat.cast_zero]
          exact ⟨⟨hmin, hcut, by omega⟩,
            mul_nonneg (Nat.cast_nonneg _) (augCharge_nonneg _ _ _)⟩
      | some π =>
          have hπ := witnessPath_some hG hf hT.1 hw
          have hlen : π.length ≤ Fintype.card V + 1 :=
            hπ.nodup.length_le_card.trans (Nat.le_succ _)
          have heval : Prog.eval G.cut (flowLoop deg d s t (fuel + 1) i f T) =
              Prog.eval G.cut (flowLoop deg d s t fuel (i + 1)
                (fun u v => f u v +
                  pathFlow (Prog.eval G.cut (shortcutLoop deg d f (Fintype.card V) π)) u v)
                (Prog.eval G.cut (repairForest T f
                  (Prog.eval G.cut (shortcutLoop deg d f (Fintype.card V) π))))) := by
            simp only [flowLoop, hw, Prog.eval_bind]
          have hcost : Prog.cost G.cut (flowLoop deg d s t (fuel + 1) i f T) =
              Prog.cost G.cut (shortcutLoop deg d f (Fintype.card V) π) +
                (Prog.cost G.cut (repairForest T f
                  (Prog.eval G.cut (shortcutLoop deg d f (Fintype.card V) π))) +
                Prog.cost G.cut (flowLoop deg d s t fuel (i + 1)
                  (fun u v => f u v +
                    pathFlow (Prog.eval G.cut (shortcutLoop deg d f (Fintype.card V) π)) u v)
                  (Prog.eval G.cut (repairForest T f
                    (Prog.eval G.cut (shortcutLoop deg d f (Fintype.card V) π)))))) := by
            simp only [flowLoop, hw, Prog.cost_bind]
          obtain ⟨hπ', -, hshort, -⟩ := shortcutLoop_spec hG hδ hdeg hf _ π hπ hlen
          have hcs := shortcutLoop_cost_le hG hδ hdeg hf hπ hlen
          generalize Prog.eval G.cut (shortcutLoop deg d f (Fintype.card V) π) = π' at *
          have hT' := repairForest_spec hG hf hT hπ'
          have hcr := repairForest_cost_le T f π' G.cut
          generalize Prog.eval G.cut (repairForest T f π') = T' at *
          set n := Fintype.card V
          set L := logFactor n
          have hdR : (0 : ℝ) < d := by exact_mod_cast hd
          have hf' : Augmentation.FlowSpec G s t ((i + 1 : ℕ) : ℝ)
              (fun u v => f u v + pathFlow π' u v) := by
            have := augment_flowSpec hG hf hπ'
            push_cast
            exact this
          have hr1 : 1 ≤ π'.length := List.length_pos_iff.mpr hπ'.ne_nil
          have hq' := usedCount_augment_le hG hf hπ'
          rw [Nat.cast_sub hr1, Nat.cast_one] at hq'
          have hgrow : (1 + 8 / (d : ℝ)) ^ i ≤ 3 ^ 8 := growth_le hd (by omega)
          have hpow0 : (0 : ℝ) ≤ (1 + 8 / (d : ℝ)) ^ i := by positivity
          have hsupp' : (n : ℝ) + usedCount (fun u v => f u v + pathFlow π' u v) ≤
              n * (1 + 8 / (d : ℝ)) ^ (i + 1) := by
            have hstep := support_step hdR hq' hshort
            have h8 : (0 : ℝ) ≤ 1 + 8 / d := by positivity
            calc _ ≤ ((n : ℝ) + usedCount f) * (1 + 8 / d) := hstep
              _ ≤ (n * (1 + 8 / (d : ℝ)) ^ i) * (1 + 8 / d) :=
                  mul_le_mul_of_nonneg_right hsupp h8
              _ = n * (1 + 8 / (d : ℝ)) ^ (i + 1) := by rw [pow_succ]; ring
          obtain ⟨hvalid, hrest⟩ := ih (i + 1) _ T' (by omega) hf' hT' hsupp'
          refine ⟨heval ▸ hvalid, ?_⟩
          rw [hcost]
          push_cast
          -- the shortened path is short
          have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          have hpath : (π'.length : ℝ) ≤ 1 + 8 * 3 ^ 8 * n / d := by
            have h1 : (d : ℝ) * ((π'.length : ℝ) - 1) ≤ 8 * 3 ^ 8 * n := by
              have : (n : ℝ) + usedCount f ≤ n * 3 ^ 8 :=
                hsupp.trans (mul_le_mul_of_nonneg_left hgrow hn0)
              linarith
            have h2 : (π'.length : ℝ) - 1 ≤ 8 * 3 ^ 8 * n / d := by
              rw [le_div_iff₀ hdR]
              linarith
            linarith
          have hkL : ((searchDepth V + 1 : ℕ) : ℝ) ≤ L := by
            exact_mod_cast searchDepth_add_one_le_logFactor
          have hcr' : (Prog.cost G.cut (repairForest T f π') : ℝ) ≤
              (1 + 8 * 3 ^ 8 * n / d) * (6 * L) := by
            have : (Prog.cost G.cut (repairForest T f π') : ℝ) ≤
                π'.length * (6 * ((searchDepth V + 1 : ℕ) : ℝ)) := by exact_mod_cast hcr
            refine this.trans (mul_le_mul hpath (by linarith) (by positivity) (by positivity))
          unfold augCharge at hrest ⊢
          nlinarith

/-- The bounded-flow query cap `C n L²`, with `C = 70 + 48 · 3^8` and
`L = logFactor n`; it does not depend on the threshold. -/
def flowCap (n : ℕ) : ℕ := (70 + 48 * 3 ^ 8) * n * logFactor n ^ 2

/-- **Bounded max-flow (M6).** For an unweighted graph, a threshold `1 ≤ d` bounding
every degree from below, and cached degrees equal to the true degrees, the
outcome is valid: either an exact minimum `s`–`t` shore with its value `≤ d`, or a
certificate that every `s`–`t` cut is at least `d + 1`. The actual query cost is
at most `flowCap n`. -/
theorem boundedFlow_spec {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G) {d : ℕ}
    (hd : 1 ≤ d) (hδ : ∀ v, d ≤ natDegree G v) {deg : V → ℕ} (hdeg : ∀ v, deg v = natDegree G v)
    (s t : V) :
    (Prog.eval G.cut (boundedFlow deg d s t)).Valid G d s t ∧
      Prog.cost G.cut (boundedFlow deg d s t) ≤ flowCap (Fintype.card V) := by
  have hT0 : IsSpanningForest (unusedGraph G (fun _ _ => 0)) (spanningForest.eval G.cut) := by
    rw [unusedGraph_zero]
    exact spanningForest_correct G
  obtain ⟨hvalid, hcost⟩ := flowLoop_spec hG hd hδ hdeg d 0 (fun _ _ => 0)
    (spanningForest.eval G.cut) (by omega) (by rw [Nat.cast_zero]; exact zero_flowSpec G s t) hT0
    (by rw [usedCount_zero, pow_zero, mul_one, add_zero])
  have heval : Prog.eval G.cut (boundedFlow deg d s t) =
      Prog.eval G.cut (flowLoop deg d s t d 0 (fun _ _ => 0) (spanningForest.eval G.cut)) := by
    rw [boundedFlow, Prog.eval_bind, liftDTree_eval]
  have hc : Prog.cost G.cut (boundedFlow deg d s t) =
      Prog.cost G.cut (liftDTree (spanningForest (V := V))) +
        Prog.cost G.cut (flowLoop deg d s t d 0 (fun _ _ => 0) (spanningForest.eval G.cut)) := by
    rw [boundedFlow, Prog.cost_bind, liftDTree_eval]
  refine ⟨heval ▸ hvalid, ?_⟩
  have h0 := liftDTree_cost_le (spanningForest (V := V)) G.cut
  set n := Fintype.card V
  set L := logFactor n
  have hdn : (d : ℝ) ≤ n := by
    have := (hδ s).trans (natDegree_le G s)
    exact_mod_cast this.trans (Nat.sub_le _ _)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast one_le_logFactor n
  have hkL : ((searchDepth V + 1 : ℕ) : ℝ) ≤ L := by
    exact_mod_cast searchDepth_add_one_le_logFactor
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h0' : (Prog.cost G.cut (liftDTree (spanningForest (V := V))) : ℝ) ≤ 12 * n * L := by
    have : (Prog.cost G.cut (liftDTree (spanningForest (V := V))) : ℝ) ≤
        12 * n * ((searchDepth V + 1 : ℕ) : ℝ) := by exact_mod_cast h0
    exact this.trans (mul_le_mul_of_nonneg_left hkL (by positivity))
  have hcharge : (d : ℝ) * augCharge n L d =
      13 * L * (3 * n * L + d) + 6 * L * (d + 8 * 3 ^ 8 * n) := by
    unfold augCharge
    field_simp
  have hnL : (n : ℝ) * L ≤ n * L ^ 2 := by
    have := mul_le_mul_of_nonneg_left hL1 (mul_nonneg hn0 (by linarith : (0 : ℝ) ≤ L))
    nlinarith
  have hLd : (L : ℝ) * d ≤ L * n := mul_le_mul_of_nonneg_left hdn (by linarith)
  have hreal : (Prog.cost G.cut (boundedFlow deg d s t) : ℝ) ≤ ((flowCap n : ℕ) : ℝ) := by
    rw [hc, Nat.cast_add]
    simp only [flowCap]
    push_cast
    nlinarith
  exact_mod_cast hreal

/-- The bounded flow as one public decision tree with the cap `flowCap n`: every
run on every oracle stays within it, and `none` reports an exhausted budget. -/
def boundedFlowTree (deg : V → ℕ) (d : ℕ) (s t : V) :
    DTree (Finset V) ℝ (Option (FlowOutcome V)) (flowCap (Fintype.card V)) :=
  (boundedFlow deg d s t).toDTree _

/-- On every promised input the tree completes with a valid outcome. -/
theorem boundedFlowTree_correct {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G) {d : ℕ}
    (hd : 1 ≤ d) (hδ : ∀ v, d ≤ natDegree G v) {deg : V → ℕ} (hdeg : ∀ v, deg v = natDegree G v)
    (s t : V) :
    ∃ o, (boundedFlowTree deg d s t).eval G.cut = some o ∧ o.Valid G d s t := by
  obtain ⟨hvalid, hcost⟩ := boundedFlow_spec hG hd hδ hdeg s t
  exact ⟨_, Prog.toDTree_eval G.cut _ _ hcost, hvalid⟩

end
end CutQueryComplexity.BoundedFlowMinCut
