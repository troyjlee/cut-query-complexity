import CutQueryComplexity.DirectedMincut.FlowDuality
import Mathlib.Algebra.BigOperators.Field

/-! # The penalized terminal LP (D5; source `eq:lp`, `lem:opt`)

Vertices carry a linear order; the canonical orientation of a pair is `u < v`. With pair
multiplicity `m_uv = c_uv + c_vu`, `χ = e_s − e_t`, and `b = d⁺ − d⁻`, a point
`(z, q, y⁺, y⁻)` is feasible (`Feasible`) when

  `Bᵀ z + q χ + y⁺ − y⁻ = b`,  `−1 ≤ z ≤ 1`,  `−2 ≤ q ≤ 2n`,  `0 ≤ y^± ≤ 4n`.

Hidden copies of a pair carry identical data, so `Bᵀ z` is `div z w = Σ_x g(w, x)` with
`g(w, x) = m_wx z_wx` for `w < x` (antisymmetric). The objective is `R − q/2`, with
`R = Σ_v (y⁺_v + y⁻_v)`.

* `residual_cut`: each copy carries `(1 ± z)/2` in the two directions (`pc`); the fractional
  digraph `P_z` satisfies `P_z(S) = F(S) − (q/2) χ(S) − r(S)/2`, where `r = y⁺ − y⁻`.
* `obj_ge`: every feasible point has objective at least `−λ_st`.
* `exists_feasible_obj_eq`: the residual network of a maximum flow gives a feasible point of
  objective `−λ_st` (simple digraphs keep `q = 2λ ≤ 2n`).
* `near_opt`: objective `≤ −λ + ε` implies `R ≤ 2ε` and `|q/2 − λ| ≤ ε`.
* `strict_start`: `z = q = 0`, `y^± = 2n ± b/2` is strictly feasible for simple digraphs.
-/

namespace CutQueryComplexity
namespace DirectedMincut

open Finset Certificate

noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- A point of the penalized LP, with one common coordinate per potential pair. -/
structure LPPoint (V : Type) where
  z : V → V → ℝ
  q : ℝ
  yp : V → ℝ
  ym : V → ℝ

variable (G : DiGraph V) (s t : V)

/-- The pair multiplicity as a real number. -/
def mult (u v : V) : ℝ := G.sym u v

/-- The terminal vector `χ = e_s − e_t`. -/
def chi (w : V) : ℝ := (if w = s then 1 else 0) - (if w = t then 1 else 0)

/-- The degree imbalance `b = d⁺ − d⁻`. -/
def bvec (w : V) : ℝ := (G.outdeg w : ℝ) - G.indeg w

/-- The antisymmetric pair flow `g(w, x)` of the hidden rows. -/
def gz (z : V → V → ℝ) (w x : V) : ℝ :=
  if w < x then mult G w x * z w x else if x < w then -(mult G x w * z x w) else 0

/-- `(Bᵀ z)_w`. -/
def divz (z : V → V → ℝ) (w : V) : ℝ := ∑ x, gz G z w x

/-- `R = Σ_v (y⁺_v + y⁻_v)`. -/
def Rsum (p : LPPoint V) : ℝ := ∑ v, (p.yp v + p.ym v)

/-- The objective `R − q/2`. -/
def obj (p : LPPoint V) : ℝ := Rsum p - p.q / 2

/-- Feasibility for the penalized LP. -/
def Feasible (p : LPPoint V) : Prop :=
  (∀ u v, u < v → -1 ≤ p.z u v ∧ p.z u v ≤ 1) ∧ -2 ≤ p.q ∧ p.q ≤ 2 * Fintype.card V ∧
    (∀ v, 0 ≤ p.yp v ∧ p.yp v ≤ 4 * Fintype.card V) ∧
    (∀ v, 0 ≤ p.ym v ∧ p.ym v ≤ 4 * Fintype.card V) ∧
    ∀ w, divz G p.z w + p.q * chi s t w + p.yp w - p.ym w = bvec G w

/-- The per-copy fractional capacity from `u` to `v`. -/
def pc (z : V → V → ℝ) (u v : V) : ℝ :=
  if u < v then (1 + z u v) / 2 else if v < u then (1 - z v u) / 2 else 0

/-- The fractional digraph's outgoing cut `P_z(S)`. -/
def Pz (z : V → V → ℝ) (S : Finset V) : ℝ := ∑ u ∈ S, ∑ v ∈ Sᶜ, mult G u v * pc z u v

variable {G s t}

omit [Fintype V] [DecidableEq V] [LinearOrder V] in
theorem mult_comm (u v : V) : mult G u v = mult G v u := by
  simp [mult, G.sym_comm u v]

omit [Fintype V] [DecidableEq V] [LinearOrder V] in
theorem mult_nonneg (u v : V) : 0 ≤ mult G u v := Nat.cast_nonneg _

omit [Fintype V] [DecidableEq V] in
theorem gz_isFlow (z : V → V → ℝ) : IsFlow (gz G z) := by
  intro u v
  rcases lt_trichotomy u v with h | rfl | h
  · simp [gz, h, not_lt.mpr h.le]
  · simp [gz]
  · simp [gz, h, not_lt.mpr h.le]

omit [Fintype V] [DecidableEq V] in
theorem mult_pc (z : V → V → ℝ) (u v : V) :
    mult G u v * pc z u v = mult G u v / 2 + gz G z u v / 2 := by
  rcases lt_trichotomy u v with h | rfl | h
  · simp [pc, gz, h]; ring
  · simp [pc, gz, mult]
  · simp [pc, gz, h, not_lt.mpr h.le, mult_comm (G := G) u v]; ring

omit [Fintype V] [DecidableEq V] in
theorem pc_mem {z : V → V → ℝ} (hz : ∀ u v, u < v → -1 ≤ z u v ∧ z u v ≤ 1) (u v : V) :
    0 ≤ pc z u v ∧ pc z u v ≤ 1 := by
  rcases lt_trichotomy u v with h | rfl | h
  · have := hz u v h; simp only [pc, h, ite_true]; constructor <;> linarith
  · simp [pc]
  · have := hz v u h; simp only [pc, not_lt.mpr h.le, h, ite_true, ite_false]
    constructor <;> linarith

omit [LinearOrder V] in
theorem symCut_cast (S : Finset V) :
    (G.symCut S : ℝ) = ∑ u ∈ S, ∑ v ∈ Sᶜ, mult G u v := by
  simp [DiGraph.symCut, DiGraph.pairs, mult]

/-- `P_z(S) = F(S) − (q/2) χ(S) − r(S)/2` (source `eq:residual-cut`). -/
theorem residual_cut {p : LPPoint V} (hp : Feasible G s t p) (S : Finset V) :
    Pz G p.z S = G.out S - p.q / 2 * ∑ w ∈ S, chi s t w - (∑ w ∈ S, (p.yp w - p.ym w)) / 2 := by
  have hcons : ∀ w, divz G p.z w = bvec G w - p.q * chi s t w - (p.yp w - p.ym w) := fun w => by
    have := hp.2.2.2.2.2 w; linarith
  have hdiv : ∑ w ∈ S, divz G p.z w = ∑ u ∈ S, ∑ v ∈ Sᶜ, gz G p.z u v :=
    sum_netOut_eq (gz_isFlow p.z) S
  have h2F := G.two_mul_out S
  have h2F' : 2 * (G.out S : ℝ) = G.symCut S + ∑ v ∈ S, bvec G v := by
    have : ((2 * (G.out S : ℤ) : ℤ) : ℝ) =
        ((G.symCut S + ∑ v ∈ S, ((G.outdeg v : ℤ) - G.indeg v) : ℤ) : ℝ) := by rw [h2F]
    push_cast at this; simpa [bvec] using this
  have hP : Pz G p.z S = (G.symCut S : ℝ) / 2 + (∑ w ∈ S, divz G p.z w) / 2 := by
    rw [hdiv, symCut_cast, Pz, sum_div, sum_div, ← sum_add_distrib]
    refine sum_congr rfl fun u _ => ?_
    rw [sum_div, sum_div, ← sum_add_distrib]
    exact sum_congr rfl fun v _ => mult_pc p.z u v
  rw [hP, sum_congr rfl fun w _ => hcons w, sum_sub_distrib, sum_sub_distrib, ← mul_sum]
  linarith

theorem Pz_nonneg {p : LPPoint V} (hp : Feasible G s t p) (S : Finset V) : 0 ≤ Pz G p.z S :=
  sum_nonneg fun u _ => sum_nonneg fun v _ =>
    mul_nonneg (mult_nonneg u v) (pc_mem hp.1 u v).1

omit [Fintype V] [LinearOrder V] in
theorem sum_chi {S : Finset V} (hs : s ∈ S) (ht : t ∉ S) :
    ∑ w ∈ S, chi s t w = 1 := by
  simp only [chi, sum_sub_distrib, sum_ite_eq', hs, ht, ite_true, ite_false, sub_zero]

theorem abs_r_le {p : LPPoint V} (hp : Feasible G s t p) (S : Finset V) :
    |∑ w ∈ S, (p.yp w - p.ym w)| ≤ Rsum p := by
  calc |∑ w ∈ S, (p.yp w - p.ym w)| ≤ ∑ w ∈ S, |p.yp w - p.ym w| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ w ∈ S, (p.yp w + p.ym w) := sum_le_sum fun w _ => by
        have := hp.2.2.2.1 w; have := hp.2.2.2.2.1 w
        rw [abs_le]; constructor <;> linarith
    _ ≤ Rsum p := sum_le_sum_of_subset_of_nonneg (subset_univ S) fun w _ _ => by
        have := hp.2.2.2.1 w; have := hp.2.2.2.2.1 w; linarith

theorem Rsum_nonneg {p : LPPoint V} (hp : Feasible G s t p) : 0 ≤ Rsum p :=
  sum_nonneg fun w _ => by have := hp.2.2.2.1 w; have := hp.2.2.2.2.1 w; linarith

/-- `f ≤ F(S) + R/2` for every terminal shore. -/
theorem half_q_le {p : LPPoint V} (hp : Feasible G s t p) {S : Finset V}
    (hs : s ∈ S) (ht : t ∉ S) : p.q / 2 ≤ G.out S + Rsum p / 2 := by
  have h := residual_cut hp S
  rw [sum_chi hs ht, mul_one] at h
  have h0 := Pz_nonneg hp S
  have hr := abs_r_le hp S
  rw [abs_le] at hr
  linarith

/-- **Lower bound** (source `lem:opt`). -/
theorem obj_ge {p : LPPoint V} (hp : Feasible G s t p) (hst : s ≠ t) :
    -(stMin G s t : ℝ) ≤ obj p := by
  obtain ⟨S, hs, ht, hS⟩ := exists_stMin G hst
  have := half_q_le hp hs ht
  rw [hS] at this
  have := Rsum_nonneg hp
  unfold obj; linarith

/-- **Near-optimal points** (source `lem:opt`). -/
theorem near_opt {p : LPPoint V} (hp : Feasible G s t p) (hst : s ≠ t) {ε : ℝ}
    (hε : obj p ≤ -(stMin G s t : ℝ) + ε) :
    Rsum p ≤ 2 * ε ∧ |p.q / 2 - stMin G s t| ≤ ε := by
  obtain ⟨S, hs, ht, hS⟩ := exists_stMin G hst
  have h1 := half_q_le hp hs ht
  rw [hS] at h1
  have h0 := Rsum_nonneg hp
  unfold obj at hε
  refine ⟨by linarith, ?_⟩
  rw [abs_le]; constructor <;> linarith

omit [LinearOrder V] in
/-- The out-degree of a simple digraph is at most `n − 1`. -/
theorem outdeg_le (hG : G.Simple) (v : V) : (G.outdeg v : ℝ) ≤ Fintype.card V - 1 := by
  have h : G.outdeg v ≤ (univ.erase v).card := by
    unfold DiGraph.outdeg
    rw [← sum_erase (f := fun u => G.c v u) _ (G.diag v)]
    calc ∑ x ∈ univ.erase v, G.c v x ≤ ∑ x ∈ univ.erase v, 1 := sum_le_sum fun x _ => hG v x
      _ = _ := by simp
  rw [card_erase_of_mem (mem_univ v), card_univ] at h
  have hpos : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  have : (G.outdeg v : ℝ) ≤ ((Fintype.card V - 1 : ℕ) : ℝ) := by exact_mod_cast h
  rwa [Nat.cast_sub hpos, Nat.cast_one] at this

omit [LinearOrder V] in
theorem indeg_le (hG : G.Simple) (v : V) : (G.indeg v : ℝ) ≤ Fintype.card V - 1 := by
  have h : G.indeg v ≤ (univ.erase v).card := by
    unfold DiGraph.indeg
    rw [← sum_erase (f := fun u => G.c u v) _ (G.diag v)]
    calc ∑ x ∈ univ.erase v, G.c x v ≤ ∑ x ∈ univ.erase v, 1 := sum_le_sum fun x _ => hG x v
      _ = _ := by simp
  rw [card_erase_of_mem (mem_univ v), card_univ] at h
  have hpos : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  have : (G.indeg v : ℝ) ≤ ((Fintype.card V - 1 : ℕ) : ℝ) := by exact_mod_cast h
  rwa [Nat.cast_sub hpos, Nat.cast_one] at this

/-- **The optimum is attained at `−λ`** (source `lem:opt`), from a maximum flow. -/
theorem exists_feasible_obj_eq (hG : G.Simple) (hst : s ≠ t) :
    ∃ p : LPPoint V, Feasible G s t p ∧ obj p = -(stMin G s t : ℝ) := by
  obtain ⟨f, ⟨hflow, hcap, hcons⟩, hval⟩ := exists_maxFlow_st G hst
  set lam : ℝ := (stMin G s t : ℝ)
  -- residual capacities, written per copy
  let z : V → V → ℝ := fun u v =>
    if mult G u v = 0 then 0 else 2 * ((G.c u v : ℝ) - f u v) / mult G u v - 1
  have hlow : ∀ u v, -(G.c v u : ℝ) ≤ f u v := fun u v => by
    have := hcap v u; rw [hflow u v] at this; linarith
  have hgz : ∀ w x, gz G z w x = (G.c w x : ℝ) - G.c x w - 2 * f w x := by
    intro w x
    by_cases hm : mult G w x = 0
    · have hcwx : (G.c w x : ℝ) = 0 := by
        have : (G.sym w x : ℝ) = 0 := hm
        simp only [DiGraph.sym, Nat.cast_add] at this
        have := Nat.cast_nonneg (α := ℝ) (G.c x w); linarith [Nat.cast_nonneg (α := ℝ) (G.c w x)]
      have hcxw : (G.c x w : ℝ) = 0 := by
        have : (G.sym w x : ℝ) = 0 := hm
        simp only [DiGraph.sym, Nat.cast_add] at this
        linarith [Nat.cast_nonneg (α := ℝ) (G.c w x), Nat.cast_nonneg (α := ℝ) (G.c x w)]
      have hf : f w x = 0 := le_antisymm (by have := hcap w x; linarith)
        (by have := hlow w x; linarith)
      have hm' : mult G x w = 0 := by rw [mult_comm]; exact hm
      rcases lt_trichotomy w x with h | rfl | h
      · simp [gz, h, hm, hcwx, hcxw, hf]
      · simp [gz, hf]
      · simp [gz, h, not_lt.mpr h.le, hm', hcwx, hcxw, hf]
    · have hmx : mult G w x = (G.c w x : ℝ) + G.c x w := by simp [mult, DiGraph.sym]
      rcases lt_trichotomy w x with h | rfl | h
      · simp only [gz, h, ite_true, z, hm, ite_false]
        field_simp; rw [hmx]; ring
      · simp [gz, G.diag, IsFlow.self hflow]
      · have hm' : ¬ mult G x w = 0 := by rw [mult_comm]; exact hm
        have hmx' : mult G x w = (G.c w x : ℝ) + G.c x w := by rw [mult_comm]; exact hmx
        simp only [gz, not_lt.mpr h.le, h, ite_true, ite_false, z, hm']
        field_simp; rw [hmx', hflow w x]; ring
  have hnet_t : netOut f t = -lam := by
    have htot : ∑ x, netOut f x = 0 := by
      rw [sum_netOut_eq hflow univ]; simp
    rw [← sum_erase_add _ _ (mem_univ t), ← sum_erase_add _ _ (mem_erase.mpr ⟨hst, mem_univ s⟩)]
      at htot
    have : ∑ x ∈ (univ.erase t).erase s, netOut f x = 0 := sum_eq_zero fun x hx =>
      hcons x (ne_of_mem_erase hx) (ne_of_mem_erase (mem_of_mem_erase hx))
    rw [this, hval] at htot
    linarith
  have hnet : ∀ w, netOut f w = lam * chi s t w := by
    intro w
    by_cases hws : w = s
    · subst hws; simp [chi, hst, hval, lam]
    · by_cases hwt : w = t
      · subst hwt; simp [chi, hws, hnet_t]
      · simp [chi, hws, hwt, hcons w hws hwt]
  have hdiv : ∀ w, divz G z w = bvec G w - 2 * lam * chi s t w := by
    intro w
    simp only [divz, hgz, sum_sub_distrib, ← mul_sum, bvec, DiGraph.outdeg, DiGraph.indeg,
      Nat.cast_sum]
    have : ∑ x, f w x = netOut f w := rfl
    rw [this, hnet]; ring
  have hlam_le : lam ≤ Fintype.card V := by
    have h1 : (stMin G s t : ℝ) ≤ G.out {s} := by
      exact_mod_cast stMin_le G (mem_singleton_self s) (by simpa using hst.symm)
    have h2 : (G.out {s} : ℝ) ≤ G.outdeg s := by
      have := G.out_add_arcs_self {s}
      simp only [sum_singleton] at this
      exact_mod_cast (show G.out {s} ≤ G.outdeg s by omega)
    have h3 := outdeg_le hG s
    linarith
  refine ⟨⟨z, 2 * lam, fun _ => 0, fun _ => 0⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro u v _
    show -1 ≤ z u v ∧ z u v ≤ 1
    by_cases hm : mult G u v = 0
    · simp [z, hm]
    · have hmpos : 0 < mult G u v := lt_of_le_of_ne (mult_nonneg u v) (Ne.symm hm)
      have hmx : mult G u v = (G.c u v : ℝ) + G.c v u := by simp [mult, DiGraph.sym]
      have h1 := hcap u v; have h2 := hlow u v
      simp only [z, hm, ite_false]
      constructor
      · rw [le_sub_iff_add_le, le_div_iff₀ hmpos]; nlinarith
      · rw [sub_le_iff_le_add, div_le_iff₀ hmpos]; nlinarith
  · have : (0 : ℝ) ≤ lam := Nat.cast_nonneg _
    show -2 ≤ 2 * lam; linarith
  · show 2 * lam ≤ 2 * Fintype.card V; linarith
  · intro v; simp
  · intro v; simp
  · intro w
    show divz G z w + 2 * lam * chi s t w + 0 - 0 = bvec G w
    rw [hdiv]; ring
  · simp [obj, Rsum, lam]

/-- **The strict feasible start**, for simple digraphs. -/
theorem strict_start (hG : G.Simple) :
    let p : LPPoint V := ⟨fun _ _ => 0, 0, fun v => 2 * Fintype.card V + bvec G v / 2,
      fun v => 2 * Fintype.card V - bvec G v / 2⟩
    Feasible G s t p ∧ -2 < p.q ∧ p.q < 2 * Fintype.card V ∧
      (∀ v, 0 < p.yp v ∧ p.yp v < 4 * Fintype.card V) ∧
      (∀ v, 0 < p.ym v ∧ p.ym v < 4 * Fintype.card V) := by
  intro p
  have hn : (1 : ℝ) ≤ Fintype.card V := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨s⟩
  have hb : ∀ v, |bvec G v| ≤ Fintype.card V - 1 := fun v => by
    have := outdeg_le hG v; have := indeg_le hG v
    have := Nat.cast_nonneg (α := ℝ) (G.outdeg v); have := Nat.cast_nonneg (α := ℝ) (G.indeg v)
    rw [abs_le, bvec]; constructor <;> linarith
  have hyp : ∀ v, 0 < p.yp v ∧ p.yp v < 4 * Fintype.card V := fun v => by
    have := abs_le.mp (hb v); simp only [p]; constructor <;> linarith
  have hym : ∀ v, 0 < p.ym v ∧ p.ym v < 4 * Fintype.card V := fun v => by
    have := abs_le.mp (hb v); simp only [p]; constructor <;> linarith
  refine ⟨⟨fun u v _ => by simp [p], by simp [p], by show (0 : ℝ) ≤ 2 * Fintype.card V; positivity,
    fun v => ⟨(hyp v).1.le, (hyp v).2.le⟩, fun v => ⟨(hym v).1.le, (hym v).2.le⟩,
    fun w => ?_⟩, by simp [p], by show (0 : ℝ) < 2 * Fintype.card V; linarith, hyp, hym⟩
  simp only [p, divz, gz, mul_zero, neg_zero, ite_self, sum_const_zero, zero_mul, zero_add]
  ring

end

end DirectedMincut
end CutQueryComplexity
