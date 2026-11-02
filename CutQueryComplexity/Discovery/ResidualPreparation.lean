import CutQueryComplexity.Discovery.RowSearch
import CutQueryComplexity.Graph.Integral

/-! # Residual preparation (Lemma 29)

The algorithm learns an explicit subgraph `K ⊆ G` whose entries are full original
weights or zero, so that the residual `R = G - K` satisfies, for every vertex `v`,
`r_v ≤ t` or `w_R(v, u) ≤ r_v / k` for all `u` (`eq:residual-light`).

A *scan* of `v` (`scan`) records the reference `q_v = r_v` and adds to `K` every residual
edge at `v` heavier than `q_v / (2k)`, found by `residualRow` (Lemma 3) with
`b = 2k`, at most `4 k ⌈log₂ (N - 1)⌉` cut queries. `prepLoop` repeatedly scans a vertex
with `r_v > t` that is unscanned or whose residual degree fell below half its last
reference.

The invariant `PrepInv` records exactness of `K`, the lightness of scanned rows relative
to their reference, and `q_v 2^{c_v} ≤ 2D`, where `c_v` counts the scans of `v` and
`D` bounds all degrees. Since references stay above `t`, `D < t 2^s` gives `c_v ≤ s`,
so there are at most `N s` scans, whatever the weight spread (`prepLoop_spec`).
`residualPrep_spec` is the lemma with an explicit bound `N s · 4k ⌈log₂ (N - 1)⌉`, and
`residualPrep_normalized` specializes to `d_v ≤ (N - 1) U`, `t = U / (16 N²)`,
`s = 4 + 3 ⌈log₂ N⌉`, giving `O(N k log² (2N))` queries.
-/

namespace CutQueryComplexity
namespace Discovery

open Search Search.Comp WeightedGraph Finset

variable {V : Type} [Fintype V] [DecidableEq V]

section Star

/-- The star at `v` with weight `max 0 (f u)` on each edge `vu`, `u ≠ v`. -/
noncomputable def star (v : V) (f : V → ℝ) : WeightedGraph V where
  w a b := if a = v ∧ b ≠ v then max 0 (f b) else if b = v ∧ a ≠ v then max 0 (f a) else 0
  symm a b := by by_cases ha : a = v <;> by_cases hb : b = v <;> simp_all
  nonneg a b := by split_ifs <;> simp
  diag a := by simp

omit [Fintype V] in
theorem star_w (v : V) (f : V → ℝ) (a b : V) : (star v f).w a b =
    if a = v ∧ b ≠ v then max 0 (f b) else if b = v ∧ a ≠ v then max 0 (f a) else 0 := rfl

omit [Fintype V] [DecidableEq V] in
theorem subtract_w (G K : WeightedGraph V) (a b : V) :
    (G.subtract K).w a b = max 0 (G.w a b - K.w a b) := rfl

end Star

/-- The state of residual preparation: the explicit graph `K`, the last references `q`,
and the scan counts `c`. -/
structure PrepState (V : Type) where
  K : WeightedGraph V
  q : V → ℝ
  c : V → ℕ

/-- The known residual degree `r_v = d_v - deg_K(v)`, from the known degrees `d`. -/
noncomputable def resDeg (d : V → ℝ) (st : PrepState V) (v : V) : ℝ := d v - st.K.degree v

/-- `v` must be scanned: `r_v > t` and either unscanned or below half its reference. -/
def Needs (d : V → ℝ) (t : ℝ) (st : PrepState V) (v : V) : Prop :=
  t < resDeg d st v ∧ (st.c v = 0 ∨ resDeg d st v < st.q v / 2)

/-- One scan of `v`: learn its residual edges heavier than `r_v / (2k)` and add them. -/
noncomputable def scan (d : V → ℝ) (k : ℕ) (st : PrepState V) (v : V) :
    Comp (Finset V) ℝ (PrepState V) :=
  (residualRow st.K v (resDeg d st v) ((2 * k : ℕ) : ℝ)).map fun f =>
    { K := st.K.add (star v f)
      q := Function.update st.q v (resDeg d st v)
      c := Function.update st.c v (st.c v + 1) }

open scoped Classical in
/-- Scan while some vertex needs it, for at most `fuel` scans. -/
noncomputable def prepLoop (d : V → ℝ) (t : ℝ) (k : ℕ) :
    ℕ → PrepState V → Comp (Finset V) ℝ (PrepState V)
  | 0, st => Comp.pure st
  | fuel + 1, st =>
      if h : ∃ v, Needs d t st v then
        (scan d k st (Classical.choose h)).bind (prepLoop d t k fuel)
      else Comp.pure st

/-- Residual preparation, with scan budget `s` per vertex. -/
noncomputable def residualPrep (d : V → ℝ) (t : ℝ) (k s : ℕ) :
    Comp (Finset V) ℝ (WeightedGraph V) :=
  (prepLoop d t k (Fintype.card V * s + 1) ⟨0, fun _ => 0, fun _ => 0⟩).map PrepState.K

/-- The invariant of residual preparation. -/
structure PrepInv (G : WeightedGraph V) (D t : ℝ) (k : ℕ) (st : PrepState V) : Prop where
  exact : ∀ a b, st.K.w a b = 0 ∨ st.K.w a b = G.w a b
  ref : ∀ v, 1 ≤ st.c v → t < st.q v ∧ st.q v * 2 ^ st.c v ≤ 2 * D
  light : ∀ v, 1 ≤ st.c v → ∀ u, (G.subtract st.K).w v u ≤ st.q v / (2 * k)

section Proofs

variable (G : WeightedGraph V) {D t : ℝ} {k s : ℕ}

omit [Fintype V] [DecidableEq V] in
theorem le_of_exact {K : WeightedGraph V} (h : ∀ a b, K.w a b = 0 ∨ K.w a b = G.w a b) :
    ∀ a b, K.w a b ≤ G.w a b := fun a b => by
  rcases h a b with h | h <;> rw [h]; exact G.nonneg a b

theorem resDeg_eq {st : PrepState V} (hK : ∀ a b, st.K.w a b ≤ G.w a b) (v : V) :
    resDeg G.degree st v = (G.subtract st.K).degree v := by
  rw [degree_subtract G st.K hK]; rfl

omit [DecidableEq V] in
theorem degree_nonneg (H : WeightedGraph V) (v : V) : 0 ≤ H.degree v :=
  Finset.sum_nonneg fun u _ => H.nonneg v u

omit [Fintype V] [DecidableEq V] in
/-- The scan count is bounded by `s` when `D < t 2^s`. -/
theorem c_le {st : PrepState V} (hinv : PrepInv G D t k st) (ht : 0 < t)
    (hs : D < t * 2 ^ s) (v : V) : st.c v ≤ s := by
  by_contra hcs
  push Not at hcs
  obtain ⟨hq, hD⟩ := hinv.ref v (by omega)
  have h1 : (2 : ℝ) ^ (s + 1) ≤ 2 ^ st.c v := pow_le_pow_right₀ (by norm_num) hcs
  have h2 : t * 2 ^ (s + 1) < st.q v * 2 ^ st.c v :=
    calc t * 2 ^ (s + 1) ≤ t * 2 ^ st.c v := mul_le_mul_of_nonneg_left h1 ht.le
      _ < _ := mul_lt_mul_of_pos_right hq (by positivity)
  rw [pow_succ] at h2
  linarith

/-- One scan preserves the invariant, increments one count, and costs at most
`4 k ⌈log₂ (N - 1)⌉` cut queries. -/
theorem scan_spec {st : PrepState V} (hinv : PrepInv G D t k st) (hk : 0 < k) (ht : 0 < t)
    (hD : ∀ v, G.degree v ≤ D) {v : V} (hv : Needs G.degree t st v) :
    PrepInv G D t k ((scan G.degree k st v).eval G.cut) ∧
      ((scan G.degree k st v).eval G.cut).c = Function.update st.c v (st.c v + 1) ∧
      (scan G.degree k st v).cost G.cut ≤ 4 * k * Nat.clog 2 (Fintype.card V - 1) := by
  have hKG := le_of_exact G hinv.exact
  set R := G.subtract st.K with hR
  have hr := resDeg_eq G hKG v
  set r := resDeg G.degree st v with hr_def
  have hk2 : 0 < 2 * k := by omega
  obtain ⟨heval, hcost⟩ := residualRow_spec G st.K hKG v hk2
  rw [← hr] at heval hcost
  have hr0 : 0 < r := lt_trans ht hv.1
  have hkR : (0 : ℝ) < (2 * k : ℕ) := by exact_mod_cast hk2
  set thr := r / ((2 * k : ℕ) : ℝ) with hthr_def
  set f : V → ℝ := fun u => if thr < R.w v u then R.w v u else 0 with hf
  refine ⟨?_, ?_, ?_⟩
  swap
  · simp [scan]
  swap
  · simp only [scan, cost_map]
    calc _ ≤ 2 * (2 * k) * Nat.clog 2 (Fintype.card V - 1) := hcost
      _ = _ := by ring
  simp only [scan, eval_map]
  rw [← hr_def, heval]
  set K' := st.K.add (star v f)
  -- Basic facts about the new explicit graph.
  have hKK' : ∀ a b, st.K.w a b ≤ K'.w a b := fun a b => by
    simp only [K', add_w]; linarith [(star v f).nonneg a b]
  have hR' : ∀ a b, (G.subtract K').w a b ≤ R.w a b := fun a b => by
    simp only [subtract_w, R]
    exact max_le_max le_rfl (by linarith [hKK' a b])
  have hthr : 0 < thr := div_pos hr0 hkR
  have hheavy : ∀ u, thr < R.w v u → K'.w v u = G.w v u := by
    intro u hh
    have hu : u ≠ v := by rintro rfl; rw [R.diag] at hh; linarith
    have hpos : 0 < R.w v u := hthr.trans hh
    have hK0 : st.K.w v u = 0 := by
      rcases hinv.exact v u with h | h
      · exact h
      · simp [R, subtract_w, h] at hpos
    simp only [K', add_w, star_w, hu, ne_eq, not_false_eq_true, and_self, ↓reduceIte, hf, hh,
      hK0, zero_add, max_eq_right (R.nonneg v u)]
    simp [R, subtract_w, hK0, G.nonneg v u]
  have hkeep : ∀ u, ¬ thr < R.w v u → K'.w v u = st.K.w v u := by
    intro u hh
    by_cases hu : u = v
    · subst hu; rw [K'.diag, st.K.diag]
    simp [K', star_w, hu, hf, hh]
  have hrow : ∀ u, K'.w v u = 0 ∨ K'.w v u = G.w v u := by
    intro u
    by_cases hh : thr < R.w v u
    · exact Or.inr (hheavy u hh)
    · rw [hkeep u hh]; exact hinv.exact v u
  have hoff : ∀ a b, a ≠ v → b ≠ v → K'.w a b = st.K.w a b := fun a b ha hb => by
    simp [K', star_w, ha, hb]
  have hexact : ∀ a b, K'.w a b = 0 ∨ K'.w a b = G.w a b := by
    intro a b
    by_cases ha : a = v
    · subst ha; exact hrow b
    by_cases hb : b = v
    · subst hb; rw [K'.symm, G.symm]; exact hrow a
    rw [hoff a b ha hb]; exact hinv.exact a b
  have hdeg : r ≤ D := by
    rw [hr_def, resDeg]
    linarith [degree_nonneg st.K v, hD v]
  refine ⟨hexact, ?_, ?_⟩
  · intro x hx
    by_cases hxv : x = v
    · subst hxv
      simp only [Function.update_self]
      refine ⟨hv.1, ?_⟩
      by_cases hc0 : st.c x = 0
      · rw [hc0]; norm_num; linarith
      · have hq := (hinv.ref x (by omega)).2
        have hhalf : r < st.q x / 2 := hv.2.resolve_left hc0
        rw [pow_succ]
        nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (st.c x)]
    · simp only [Function.update_of_ne hxv] at hx ⊢
      exact hinv.ref x hx
  · intro x hx u
    by_cases hxv : x = v
    · subst hxv
      simp only [Function.update_self]
      by_cases hh : thr < R.w x u
      · rw [subtract_w, hheavy u hh, sub_self, max_self]
        have : (0 : ℝ) < 2 * k := by exact_mod_cast hk2
        positivity
      · push Not at hh
        have := (hR' x u).trans hh
        rw [hthr_def] at this
        push_cast at this
        exact this
    · simp only [Function.update_of_ne hxv] at hx ⊢
      exact (hR' x u).trans (hinv.light x hx u)

/-- The number of scans still available: `∑_v (s - c_v)`. -/
def potential (s : ℕ) (st : PrepState V) : ℕ := ∑ v, (s - st.c v)

/-- The conclusion `eq:residual-light` of Lemma 29 for `R = G - K`. -/
def ResidualLight (G K : WeightedGraph V) (t : ℝ) (k : ℕ) : Prop :=
  ∀ v, (G.subtract K).degree v ≤ t ∨ ∀ u, (G.subtract K).w v u ≤ (G.subtract K).degree v / k

theorem potential_update (c : V → ℕ) {v : V} (h : c v < s) :
    ∑ w, (s - Function.update c v (c v + 1) w) + 1 = ∑ w, (s - c w) := by
  classical
  rw [← Finset.add_sum_erase _ _ (mem_univ v), ← Finset.add_sum_erase _ _ (mem_univ v),
    Function.update_self,
    Finset.sum_congr rfl fun w hw => by rw [Function.update_of_ne (ne_of_mem_erase hw)]]
  omega

/-- The loop: from any state satisfying the invariant, with more fuel than the potential,
the output is residual-light, and the cost is at most one scan bound per unit of
potential. -/
theorem prepLoop_spec (hk : 0 < k) (ht : 0 < t) (hD : ∀ v, G.degree v ≤ D)
    (hs : D < t * 2 ^ s) :
    ∀ (fuel : ℕ) (st : PrepState V), PrepInv G D t k st → potential s st < fuel →
      PrepInv G D t k ((prepLoop G.degree t k fuel st).eval G.cut) ∧
      ResidualLight G ((prepLoop G.degree t k fuel st).eval G.cut).K t k ∧
      (prepLoop G.degree t k fuel st).cost G.cut ≤
        potential s st * (4 * k * Nat.clog 2 (Fintype.card V - 1)) := by
  intro fuel
  induction fuel with
  | zero => intro st _ h; omega
  | succ fuel ih =>
    intro st hinv hP
    by_cases h : ∃ v, Needs G.degree t st v
    · have hv := Classical.choose_spec h
      simp only [prepLoop, h, ↓reduceDIte, eval_bind, cost_bind]
      obtain ⟨hinv', hc', hcost⟩ := scan_spec G hinv hk ht hD hv
      set st' := (scan G.degree k st (Classical.choose h)).eval G.cut
      have hlt : st.c (Classical.choose h) < s := by
        have := c_le G hinv' ht hs (Classical.choose h)
        rw [hc', Function.update_self] at this
        omega
      have hpot : potential s st' + 1 = potential s st := by
        unfold potential; rw [hc']; exact potential_update st.c hlt
      obtain ⟨h1, h2, h3⟩ := ih st' hinv' (by omega)
      refine ⟨h1, h2, ?_⟩
      rw [← hpot, Nat.add_mul, one_mul]
      omega
    · simp only [prepLoop, h, ↓reduceDIte, eval_pure, cost_pure, zero_le, and_true]
      refine ⟨hinv, fun v => ?_⟩
      have hKG := le_of_exact G hinv.exact
      have hnv : ¬ Needs G.degree t st v := fun hv => h ⟨v, hv⟩
      unfold Needs at hnv
      rw [resDeg_eq G hKG] at hnv
      by_cases htv : (G.subtract st.K).degree v ≤ t
      · exact Or.inl htv
      right
      intro u
      push Not at htv hnv
      obtain ⟨hc, hhalf⟩ := hnv htv
      have hl := hinv.light v (by omega) u
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      calc _ ≤ st.q v / (2 * k) := hl
        _ = st.q v / 2 / k := by rw [div_div]
        _ ≤ _ := div_le_div_of_nonneg_right hhalf hkR.le

/-- **Lemma 29 (residual preparation).** If every degree is at most `D`, `t > 0` and
`D < t 2^s`, the explicit graph `K` returned by `residualPrep` has every entry equal to
`0` or to the original weight, the residual `G - K` satisfies `eq:residual-light`, and at
most `N s · 4k ⌈log₂ (N - 1)⌉` cut queries are used. -/
theorem residualPrep_spec (hk : 0 < k) (ht : 0 < t) (hD : ∀ v, G.degree v ≤ D)
    (hs : D < t * 2 ^ s) :
    (∀ a b, ((residualPrep G.degree t k s).eval G.cut).w a b = 0 ∨
        ((residualPrep G.degree t k s).eval G.cut).w a b = G.w a b) ∧
      ResidualLight G ((residualPrep G.degree t k s).eval G.cut) t k ∧
      (residualPrep G.degree t k s).cost G.cut ≤
        Fintype.card V * s * (4 * k * Nat.clog 2 (Fintype.card V - 1)) := by
  have hinit : PrepInv G D t k ⟨0, fun _ => 0, fun _ => 0⟩ :=
    ⟨fun _ _ => Or.inl rfl, fun _ h => absurd h (by simp), fun _ h => absurd h (by simp)⟩
  have hpot : potential s (⟨0, fun _ => 0, fun _ => 0⟩ : PrepState V) =
      Fintype.card V * s := by
    simp [potential]
  obtain ⟨h1, h2, h3⟩ := prepLoop_spec G hk ht hD hs (Fintype.card V * s + 1) _ hinit
    (by omega)
  rw [hpot] at h3
  simp only [residualPrep, eval_map, cost_map]
  exact ⟨h1.exact, h2, h3⟩

/-- Lemma 29 under the normalization `d_v ≤ (N - 1) U`, with `t = U / (16 N²)` and
`s = 4 + 3 ⌈log₂ N⌉` scans per vertex: at most
`N (4 + 3 ⌈log₂ N⌉) · 4k ⌈log₂ (N - 1)⌉` cut queries. -/
theorem residualPrep_normalized [Nonempty V] {U : ℝ} (hU : 0 < U) (hk : 0 < k)
    (hD : ∀ v, G.degree v ≤ ((Fintype.card V : ℝ) - 1) * U) :
    (∀ a b, ((residualPrep G.degree (U / (16 * (Fintype.card V : ℝ) ^ 2)) k
          (4 + 3 * Nat.clog 2 (Fintype.card V))).eval G.cut).w a b = 0 ∨
        ((residualPrep G.degree (U / (16 * (Fintype.card V : ℝ) ^ 2)) k
          (4 + 3 * Nat.clog 2 (Fintype.card V))).eval G.cut).w a b = G.w a b) ∧
      ResidualLight G ((residualPrep G.degree (U / (16 * (Fintype.card V : ℝ) ^ 2)) k
          (4 + 3 * Nat.clog 2 (Fintype.card V))).eval G.cut)
        (U / (16 * (Fintype.card V : ℝ) ^ 2)) k ∧
      (residualPrep G.degree (U / (16 * (Fintype.card V : ℝ) ^ 2)) k
          (4 + 3 * Nat.clog 2 (Fintype.card V))).cost G.cut ≤
        Fintype.card V * (4 + 3 * Nat.clog 2 (Fintype.card V)) *
          (4 * k * Nat.clog 2 (Fintype.card V - 1)) := by
  have hN : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast Fintype.card_pos
  refine residualPrep_spec G hk (by positivity) hD ?_
  have hc0 : Fintype.card V ≤ 2 ^ Nat.clog 2 (Fintype.card V) := Nat.le_pow_clog one_lt_two _
  have hc : (Fintype.card V : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 (Fintype.card V) := by
    exact_mod_cast hc0
  generalize (Fintype.card V : ℝ) = n at hN hc ⊢
  generalize Nat.clog 2 (Fintype.card V) = m at hc ⊢
  have h1 : n ^ 3 ≤ ((2 : ℝ) ^ m) ^ 3 := pow_le_pow_left₀ (by positivity) hc 3
  rw [pow_add, mul_comm 3 m, pow_mul, div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
  have h2 : (n - 1) * n ^ 2 < ((2 : ℝ) ^ m) ^ 3 := by nlinarith
  have h3 := mul_lt_mul_of_pos_left h2 (by positivity : (0 : ℝ) < 16 * U)
  norm_num
  nlinarith

end Proofs

end Discovery
end CutQueryComplexity
