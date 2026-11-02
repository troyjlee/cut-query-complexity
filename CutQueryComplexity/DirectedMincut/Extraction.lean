import CutQueryComplexity.DirectedMincut.LPReduction
import CutQueryComplexity.Primitive.OrderedSearch
import CutQueryComplexity.Model.Composition
import CutQueryComplexity.Model.Reduction
import CutQueryComplexity.Probability.Events

/-! # Extracting the exact terminal cut (D5; source `lem:extraction`, `thm:st`)

**The threshold argument** (`extraction`). Let `τ > 0` with `8 n² τ ≤ 1`, let `ε ≤ τ/16`, and let
`p` be a feasible point of objective at most `−λ + ε`. Let `p̂` approximate the per-copy
capacities within `τ/4` on actual pairs, and let `J` be the arcs `uv` with an actual pair and
`p̂_uv > τ`. Then every set `W` containing `s`, closed under `J`, and reachable from `s` along
`J` excludes `t` and is an exact minimum `s`–`t` cut.

**The search** (`bfs`). An implicit graph search over a public arc predicate `ok`. Each step
picks an unfinished discovered vertex `u` and runs the ordered search (`firstNbr`) on the public
list of undiscovered `v` with `ok u v`. A hit discovers a new vertex, and a miss finishes `u`.
The potential `|W| + |D|` rises each step, so `2n` steps suffice. Each step costs `3 + 3k`
queries (`bfs_correct`).

**The terminal reduction** (`terminal_solves`). Compose any LP solver whose output is, with
probability at least `1 − ζ`, a feasible point of objective at most `−λ + ε`. Then search, query
the value of the shore, and return `{s}` if the search reached `t`. The result is an exact
minimum `s`–`t` cut with its queried value, with probability at least `1 − ζ`, using
`q_LP + 2n(3 + 3⌈log₂ n⌉) + 1` queries. This is a conditional result; D8 supplies the solver.
-/

namespace CutQueryComplexity
namespace DirectedMincut

open Finset

noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]
variable {G : DiGraph V} {s t : V}

/-! ## The threshold argument -/

theorem term_le_Pz {z : V → V → ℝ} (hz : ∀ u v, u < v → -1 ≤ z u v ∧ z u v ≤ 1) {S : Finset V}
    {u v : V} (hu : u ∈ S) (hv : v ∉ S) : mult G u v * pc z u v ≤ Pz G z S := by
  have hnn : ∀ a b, 0 ≤ mult G a b * pc z a b := fun a b =>
    mul_nonneg (mult_nonneg a b) (pc_mem hz a b).1
  calc mult G u v * pc z u v ≤ ∑ v' ∈ Sᶜ, mult G u v' * pc z u v' :=
        single_le_sum (f := fun v' => mult G u v' * pc z u v') (fun b _ => hnn u b)
          (mem_compl.mpr hv)
    _ ≤ Pz G z S :=
        single_le_sum (f := fun u' => ∑ v' ∈ Sᶜ, mult G u' v' * pc z u' v')
          (fun a _ => sum_nonneg fun b _ => hnn a b) hu

/-- **The threshold argument** (source `lem:extraction`). -/
theorem extraction (hG : G.Simple) (hst : s ≠ t) {p : LPPoint V} (hp : Feasible G s t p)
    {τ ε : ℝ} (hτ : 0 < τ) (hn : 8 * (Fintype.card V : ℝ) ^ 2 * τ ≤ 1) (hε : ε ≤ τ / 16)
    (hopt : obj p ≤ -(stMin G s t : ℝ) + ε) (phat : V → V → ℝ)
    (hphat : ∀ u v, 0 < G.sym u v → |phat u v - pc p.z u v| ≤ τ / 4)
    {W : Finset V} (hsW : s ∈ W)
    (hclosed : ∀ u ∈ W, ∀ v, 0 < G.sym u v → τ < phat u v → v ∈ W)
    (hreach : ∀ w ∈ W, Relation.ReflTransGen (fun u v => 0 < G.sym u v ∧ τ < phat u v) s w) :
    t ∉ W ∧ G.out W = stMin G s t := by
  obtain ⟨hR, hq⟩ := near_opt hp hst hopt
  rw [abs_le] at hq
  have hR0 := Rsum_nonneg hp
  obtain ⟨S, hs, ht, hS⟩ := exists_stMin G hst
  -- no threshold arc leaves a minimum cut
  have hPS : Pz G p.z S ≤ 2 * ε := by
    have h := residual_cut hp S
    rw [sum_chi hs ht, mul_one, hS] at h
    have hr := abs_le.mp (abs_r_le hp S)
    linarith
  have hnoJ : ∀ u ∈ S, ∀ v, v ∉ S → ¬ (0 < G.sym u v ∧ τ < phat u v) := by
    rintro u hu v hv ⟨hpos, hgt⟩
    have hm : (1 : ℝ) ≤ mult G u v := by
      have : (1 : ℕ) ≤ G.sym u v := hpos
      simp only [mult]; exact_mod_cast this
    have hterm := term_le_Pz (G := G) hp.1 hu hv
    have hpc0 := (pc_mem hp.1 u v).1
    have hpc : pc p.z u v ≤ 2 * ε := by nlinarith
    have := abs_le.mp (hphat u v hpos)
    linarith
  have hWS : W ⊆ S := by
    intro w hw
    have hr := hreach w hw
    clear hw
    induction hr with
    | refl => exact hs
    | tail _ hbc ih =>
        by_contra hc
        exact hnoJ _ ih _ hc hbc
  have htW : t ∉ W := fun h => ht (hWS h)
  refine ⟨htW, ?_⟩
  -- the search shore is nearly saturated
  have hPW : Pz G p.z W ≤ 5 / 2 * (Fintype.card V : ℝ) ^ 2 * τ := by
    have hterm : ∀ u ∈ W, ∀ v ∈ Wᶜ, mult G u v * pc p.z u v ≤ 5 / 2 * τ := by
      intro u hu v hv
      by_cases hpos : 0 < G.sym u v
      · have hle : phat u v ≤ τ := by
          by_contra hgt
          exact (mem_compl.mp hv) (hclosed u hu v hpos (lt_of_not_ge hgt))
        have := abs_le.mp (hphat u v hpos)
        have hm2 : mult G u v ≤ 2 := by
          have : G.sym u v ≤ 2 := by
            have := hG u v; have := hG v u; simp only [DiGraph.sym]; omega
          simp only [mult]; exact_mod_cast this
        have hpc0 := (pc_mem hp.1 u v).1
        have hm0 := mult_nonneg (G := G) u v
        nlinarith
      · have : G.sym u v = 0 := Nat.eq_zero_of_not_pos hpos
        simp [mult, this]; positivity
    calc Pz G p.z W ≤ ∑ u ∈ W, ∑ v ∈ Wᶜ, 5 / 2 * τ :=
          sum_le_sum fun u hu => sum_le_sum fun v hv => hterm u hu v hv
      _ = (W.card : ℝ) * (Wᶜ.card : ℝ) * (5 / 2 * τ) := by simp; ring
      _ ≤ (Fintype.card V : ℝ) * (Fintype.card V : ℝ) * (5 / 2 * τ) := by
          have h1 : (W.card : ℝ) ≤ Fintype.card V := by exact_mod_cast card_le_univ W
          have h2 : (Wᶜ.card : ℝ) ≤ Fintype.card V := by exact_mod_cast card_le_univ Wᶜ
          have : 0 ≤ 5 / 2 * τ := by positivity
          have h3 : (W.card : ℝ) * (Wᶜ.card : ℝ) ≤ (Fintype.card V : ℝ) * (Fintype.card V : ℝ) :=
            mul_le_mul h1 h2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
          nlinarith
      _ = _ := by ring
  have hFW := residual_cut hp W
  rw [sum_chi hsW htW, mul_one] at hFW
  have hrW := abs_le.mp (abs_r_le hp W)
  have hN : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨s⟩
  have hN2 : (1 : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by nlinarith
  have h8 : 8 * τ ≤ 1 := by nlinarith
  have hPW' : Pz G p.z W ≤ 5 / 16 := by
    have : 5 / 2 * (Fintype.card V : ℝ) ^ 2 * τ = 5 / 16 * (8 * (Fintype.card V : ℝ) ^ 2 * τ) := by
      ring
    linarith
  have hlt : (G.out W : ℝ) < stMin G s t + 1 := by linarith
  have hge : stMin G s t ≤ G.out W := stMin_le G hsW htW
  have : G.out W < stMin G s t + 1 := by exact_mod_cast hlt
  omega

/-! ## The implicit graph search -/

/-- The arcs of the implicit graph: an actual pair whose public predicate holds. -/
def JArc (G : DiGraph V) (ok : V → V → Bool) (u v : V) : Prop := 0 < G.sym u v ∧ ok u v = true

/-- The public candidates of a search from `u`. -/
def cand (ok : V → V → Bool) (W : Finset V) (u : V) : List V :=
  (univ.filter fun v => v ∉ W ∧ ok u v = true).toList

/-- The search with `fuel` steps, discovered set `W`, and finished set `D`. -/
def bfs (k : ℕ) (ok : V → V → Bool) :
    (fuel : ℕ) → Finset V → Finset V → DTree (Finset V) ℕ (Finset V) (fuel * (3 + 3 * k))
  | 0, W, _ => DTree.pure W
  | fuel + 1, W, D =>
      if h : (W \ D).Nonempty then
        ((firstNbr ((W \ D).min' h) k (cand ok W ((W \ D).min' h))).bind fun r =>
          match r with
          | some (v, _) => bfs k ok fuel (insert v W) D
          | none => bfs k ok fuel W (insert ((W \ D).min' h) D)).cast (by ring)
      else DTree.pure W

/-- The search invariant. -/
structure BfsInv (G : DiGraph V) (ok : V → V → Bool) (s : V) (W D : Finset V) : Prop where
  mem : s ∈ W
  sub : D ⊆ W
  reach : ∀ w ∈ W, Relation.ReflTransGen (JArc G ok) s w
  closed : ∀ u ∈ D, ∀ v, JArc G ok u v → v ∈ W

theorem bfs_correct (G : DiGraph V) (ok : V → V → Bool) (s : V) {k : ℕ}
    (hk : Fintype.card V ≤ 2 ^ k) :
    ∀ (fuel : ℕ) (W D : Finset V), BfsInv G ok s W D →
      2 * Fintype.card V ≤ fuel + W.card + D.card →
      let W' := (bfs k ok fuel W D).eval G.out
      s ∈ W' ∧ (∀ w ∈ W', Relation.ReflTransGen (JArc G ok) s w) ∧
        ∀ u ∈ W', ∀ v, JArc G ok u v → v ∈ W' := by
  intro fuel
  induction fuel with
  | zero =>
      intro W D hI hpot
      simp only [bfs, DTree.eval_pure]
      have hW : W.card ≤ Fintype.card V := card_le_univ W
      have hD : D.card ≤ Fintype.card V := card_le_univ D
      have hWu : W = univ := eq_univ_of_card W (by omega)
      refine ⟨hI.mem, hI.reach, fun u _ v _ => hWu ▸ mem_univ v⟩
  | succ fuel ih =>
      intro W D hI hpot
      simp only [bfs]
      split_ifs with h
      · set u := (W \ D).min' h
        have huWD : u ∈ W \ D := min'_mem _ h
        have huW : u ∈ W := (mem_sdiff.mp huWD).1
        have huD : u ∉ D := (mem_sdiff.mp huWD).2
        have hnd : (cand ok W u).Nodup := nodup_toList _
        have hu : u ∉ cand ok W u := by simp [cand, huW]
        have hlen : (cand ok W u).length ≤ 2 ^ k := by
          rw [cand, length_toList]; exact (card_le_univ _).trans hk
        rw [DTree.eval_cast, DTree.eval_bind, firstNbr_correct G u k hnd hu hlen]
        cases hf : firstPos (G.sym u) (cand ok W u) with
        | some r =>
            obtain ⟨v, m⟩ := r
            simp only
            -- a newly discovered vertex
            have hfind : (cand ok W u).find? (fun x => decide (0 < G.sym u x)) = some v := by
              unfold firstPos at hf
              cases hx : (cand ok W u).find? (fun x => decide (0 < G.sym u x)) with
              | none => rw [hx] at hf; cases hf
              | some x => rw [hx] at hf; simp at hf; rw [hf.1]
            have hvc : v ∈ cand ok W u := List.mem_of_find?_eq_some hfind
            have hvpos : 0 < G.sym u v := by simpa using List.find?_some hfind
            simp only [cand, mem_toList, mem_filter, mem_univ, true_and] at hvc
            have hJ : JArc G ok u v := ⟨hvpos, hvc.2⟩
            refine ih (insert v W) D ⟨mem_insert_of_mem hI.mem,
              hI.sub.trans (subset_insert _ _), fun w hw => ?_,
              fun a ha b hab => mem_insert_of_mem (hI.closed a ha b hab)⟩ ?_
            · rcases mem_insert.mp hw with rfl | hw
              · exact (hI.reach u huW).tail hJ
              · exact hI.reach w hw
            · rw [card_insert_of_notMem hvc.1]; omega
        | none =>
            simp only
            -- `u` is finished
            have hnone : ∀ v, JArc G ok u v → v ∈ W := by
              intro v ⟨hpos, hok⟩
              by_contra hvW
              have hvc : v ∈ cand ok W u := by simp [cand, hvW, hok]
              unfold firstPos at hf
              rw [Option.map_eq_none_iff, List.find?_eq_none] at hf
              exact hf v hvc (by simpa using hpos)
            refine ih W (insert u D) ⟨hI.mem, insert_subset huW hI.sub, hI.reach,
              fun a ha b hab => ?_⟩ ?_
            · rcases mem_insert.mp ha with rfl | ha
              · exact hnone b hab
              · exact hI.closed a ha b hab
            · rw [card_insert_of_notMem huD]; omega
      · simp only [DTree.eval_pure]
        refine ⟨hI.mem, hI.reach, fun u hu v hv => ?_⟩
        have huD : u ∈ D := by
          by_contra huD
          exact h ⟨u, mem_sdiff.mpr ⟨hu, huD⟩⟩
        exact hI.closed u huD v hv

/-! ## The terminal reduction -/

/-- The public threshold predicate from an LP point. -/
def okOf (p : LPPoint V) (τ : ℝ) (u v : V) : Bool := decide (τ < pc p.z u v)

/-- Extraction from an LP point: search, fall back to `{s}` if `t` was reached, and query the
value of the returned shore. -/
def extract (s t : V) (k : ℕ) (τ : ℝ) (p : LPPoint V) :
    DTree (Finset V) ℕ (Finset V × ℕ) (2 * Fintype.card V * (3 + 3 * k) + 1) :=
  (bfs k (okOf p τ) (2 * Fintype.card V) {s} ∅).bind fun W =>
    let S := if t ∈ W then {s} else W
    DTree.query S fun a => DTree.pure (S, a)

/-- The terminal-cut specification: an exact minimum `s`–`t` shore with its value. -/
def STGood (s t : V) (G : DiGraph V) (r : Finset V × ℕ) : Prop :=
  s ∈ r.1 ∧ t ∉ r.1 ∧ G.out r.1 = stMin G s t ∧ r.2 = G.out r.1

/-- A good LP output for `G`. -/
def LPGood (s t : V) (ε : ℝ) (G : DiGraph V) (p : LPPoint V) : Prop :=
  Feasible G s t p ∧ obj p ≤ -(stMin G s t : ℝ) + ε

/-- **Extraction is exact on a good LP point.** -/
theorem extract_correct (hG : G.Simple) (hst : s ≠ t) {k : ℕ} (hk : Fintype.card V ≤ 2 ^ k)
    {τ ε : ℝ} (hτ : 0 < τ) (hn : 8 * (Fintype.card V : ℝ) ^ 2 * τ ≤ 1) (hε : ε ≤ τ / 16)
    {p : LPPoint V} (hp : LPGood s t ε G p) :
    STGood s t G ((extract s t k τ p).eval G.out) := by
  have hI : BfsInv G (okOf p τ) s {s} ∅ :=
    ⟨mem_singleton_self s, empty_subset _, fun w hw => by
      rw [mem_singleton.mp hw], fun u hu => absurd hu (Finset.notMem_empty u)⟩
  obtain ⟨hsW, hreach, hclosed⟩ := bfs_correct G (okOf p τ) s hk (2 * Fintype.card V) {s} ∅ hI
    (by simp)
  set W := (bfs k (okOf p τ) (2 * Fintype.card V) {s} ∅).eval G.out
  have hreach' : ∀ w ∈ W, Relation.ReflTransGen
      (fun u v => 0 < G.sym u v ∧ τ < pc p.z u v) s w := fun w hw => by
    have h := hreach w hw
    clear hw
    induction h with
    | refl => exact .refl
    | tail _ hbc ih => exact ih.tail ⟨hbc.1, by simpa [okOf] using hbc.2⟩
  obtain ⟨htW, hval⟩ := extraction hG hst hp.1 hτ hn hε hp.2 (pc p.z)
    (fun u v _ => by simp; positivity) hsW
    (fun u hu v hpos hgt => hclosed u hu v ⟨hpos, by simpa [okOf] using hgt⟩) hreach'
  simp only [extract, DTree.eval_bind, DTree.eval_query, DTree.eval_pure]
  rw [ite_eq_right_of_eq_false _ _ (eq_false htW)]
  exact ⟨hsW, htW, hval, rfl⟩

/-- **The terminal reduction, conditional on an LP solver** (source `thm:st`). -/
theorem terminal_solves {X : Type} (graph : X → DiGraph V) (hsimple : ∀ x, (graph x).Simple)
    (hst : s ≠ t) {k : ℕ} (hk : Fintype.card V ≤ 2 ^ k) {τ ε ζ : ℝ} (hτ : 0 < τ)
    (hn : 8 * (Fintype.card V : ℝ) ^ 2 * τ ≤ 1) (hε : ε ≤ τ / 16) (hζ : 0 ≤ ζ) {qLP : ℕ}
    (lp : RTree (Finset V) ℕ (LPPoint V) qLP)
    (hlp : lp.SolvesWithError (fun x => (graph x).out) (fun x => LPGood s t ε (graph x)) ζ) :
    (lp.bind fun p => RTree.ofDeterministic (extract s t k τ p)).SolvesWithError
      (fun x => (graph x).out) (fun x => STGood s t (graph x)) ζ := by
  have := RTree.bind_solves (ε := 0) hζ le_rfl hlp fun x p hp => by
    have hsol : (extract s t k τ p).Solves (fun _ : Unit => (graph x).out)
        (fun _ => STGood s t (graph x)) := fun _ =>
      extract_correct (hsimple x) hst hk hτ hn hε hp
    simpa using RTree.ofDeterministic_solves hsol ()
  simpa using this

end

end DirectedMincut
end CutQueryComplexity
