import CutQueryComplexity.CanonicalST.Augmentation.MaxFlow
import CutQueryComplexity.Graph.Integral
import CutQueryComplexity.CanonicalST.Witness.Loss

/-!
# Actual sparse unknown-edge augmentation

Only positive residual-support pairs absent from the learned graph are kept.
The resulting Q is a unit subgraph of the actual input, and adding the proved
residual flow to the learned maximum flow is feasible in H+Q. Its size is
bounded by the actual acyclic integral residual support.
-/

set_option autoImplicit false

namespace CutQueryComplexity.CanonicalST.Augmentation

open Finset WeightedGraph Certificate
open DirectedUnitST.Repair
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

def unknownSupportGraph (H : WeightedGraph V) (a : V → V → ℝ) (ha : IsFlow a) :
    WeightedGraph V where
  w u v := if H.w u v = 0 ∧ (0 < a u v ∨ 0 < a v u) then 1 else 0
  symm u v := by rw [H.symm u v]; simp only [or_comm]
  nonneg u v := by split_ifs <;> norm_num
  diag v := by simp [ha.self]

theorem unknownSupportGraph_unit (H : WeightedGraph V) (a : V → V → ℝ) (ha : IsFlow a) :
    AllPairsAudit.Unweighted (unknownSupportGraph H a ha) := by
  intro u v
  simp only [unknownSupportGraph]
  split_ifs <;> simp

theorem unknownSupportGraph_disjoint (H : WeightedGraph V) (a : V → V → ℝ)
    (ha : IsFlow a) (u v : V) :
    H.w u v = 0 ∨ (unknownSupportGraph H a ha).w u v = 0 := by
  by_cases h : H.w u v = 0
  · exact Or.inl h
  · exact Or.inr (by simp [unknownSupportGraph, h])

theorem unknownSupportGraph_unknown (H : WeightedGraph V) (a : V → V → ℝ)
    (ha : IsFlow a) {u v : V} (h : 0 < (unknownSupportGraph H a ha).w u v) : H.w u v = 0 := by
  by_contra hne
  simp [unknownSupportGraph, hne] at h

theorem feasible_zero_edge {H : WeightedGraph V} {g : V → V → ℝ}
    (hg : Certificate.Feasible H g) {u v : V} (hH : H.w u v = 0) : g u v = 0 := by
  have h := hg.2 u v
  rw [hH] at h
  exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))

theorem unknownSupportGraph_le {H G : WeightedGraph V}
    (hG : AllPairsAudit.Unweighted G) (hHG : H.IsSubgraph G)
    {s t : V} {r : ℝ} {g a : V → V → ℝ} (hg : FlowSpec H s t r g) (ha : IsFlow a)
    (hcap : ∀ u v, a u v ≤ residualCapacity G g u v) :
    (unknownSupportGraph H a ha).IsSubgraph G := by
  have hgG := hg.mono hHG
  intro u v
  by_cases hp : H.w u v = 0 ∧ (0 < a u v ∨ 0 < a v u)
  · have hguv := feasible_zero_edge hg.1 hp.1
    have hGpos : 0 < G.w u v := by
      rcases hp.2 with hpos | hpos
      · have hc := hcap u v
        rw [residualCapacity_cast hG hgG, hguv] at hc
        linarith
      · have hc := hcap v u
        rw [residualCapacity_cast hG hgG, hg.1.1 u v, hguv, G.symm v u] at hc
        linarith
    rcases hG u v with hz | hone
    · rw [hz] at hGpos
      exact False.elim ((lt_irrefl 0) hGpos)
    · simp [unknownSupportGraph, hp, hone]
  · simpa [unknownSupportGraph, hp] using G.nonneg u v

theorem unknownSupportGraph_add_unit {H : WeightedGraph V}
    (hH : AllPairsAudit.Unweighted H) (a : V → V → ℝ) (ha : IsFlow a) :
    AllPairsAudit.Unweighted (H.add (unknownSupportGraph H a ha)) := by
  intro u v
  rcases unknownSupportGraph_disjoint H a ha u v with h | h
  · simpa only [add_w, h, _root_.zero_add] using unknownSupportGraph_unit H a ha u v
  · simpa only [add_w, h, _root_.add_zero] using hH u v

def positiveArcs (a : V → V → ℝ) : Finset (V × V) := univ.filter fun e => 0 < a e.1 e.2

theorem positiveArcs_sum (a : V → V → ℝ) :
    (∑ u, ∑ v, if 0 < a u v then (1 : ℝ) else 0) = (positiveArcs a).card := by
  simp only [positiveArcs, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    Fintype.sum_prod_type]

/-- Each undirected extra edge consumes at least one positive residual arc. -/
theorem unknownSupportGraph_mass_le (H : WeightedGraph V) (a : V → V → ℝ) (ha : IsFlow a) :
    (unknownSupportGraph H a ha).edgeMass ≤ (positiveArcs a).card := by
  have hpair (u v : V) : (unknownSupportGraph H a ha).w u v ≤
      (if 0 < a u v then (1 : ℝ) else 0) + (if 0 < a v u then 1 else 0) := by
    by_cases huv : 0 < a u v <;> by_cases hvu : 0 < a v u <;>
      simp [unknownSupportGraph, huv, hvu] <;> split_ifs <;> norm_num
  have hsum := sum_le_sum (s := (univ : Finset V)) fun u _ =>
    sum_le_sum (s := (univ : Finset V)) fun v _ => hpair u v
  have hswap : (∑ u : V, ∑ v, if 0 < a v u then (1 : ℝ) else 0) =
      ∑ u : V, ∑ v, if 0 < a u v then (1 : ℝ) else 0 := sum_comm
  simp only [sum_add_distrib, hswap, positiveArcs_sum] at hsum
  unfold edgeMass
  linarith

theorem positiveArcs_card (a : V → V → ℝ) (hint : ∀ u v, IntegerValue (a u v)) :
    (positiveArcs a).card = supportSize (naturalPositive a) := by
  simp only [positiveArcs, supportSize, naturalPositive_pos hint]

/-- The supported residual flow remains feasible after retaining only its
actual unknown edges; unused actual edges are not needed for feasibility. -/
theorem unknownSupportGraph_flow {H G : WeightedGraph V}
    (hH : AllPairsAudit.Unweighted H) (hG : AllPairsAudit.Unweighted G)
    (hHG : H.IsSubgraph G) {s t : V} {r q : ℝ} {g a : V → V → ℝ}
    (hg : FlowSpec H s t r g) (ha : IsFlow a)
    (hcap : ∀ u v, a u v ≤ residualCapacity G g u v)
    (hdiv : ∀ x, netOut a x = (if x = s then q else 0) - (if x = t then q else 0))
    (hint : ∀ u v, IntegerValue (a u v)) :
    FlowSpec (H.add (unknownSupportGraph H a ha)) s t (r + q)
      (fun u v => g u v + a u v) := by
  have hf := add_residual_flow hG (hg.mono hHG) ha hcap hdiv hint
  refine ⟨⟨hf.1.1, ?_⟩, hf.2⟩
  intro u v
  have hcapone : |g u v + a u v| ≤ 1 :=
    (hf.1.2 u v).trans (AllPairsAudit.unweighted_edge_le_one hG u v)
  by_cases hknown : H.w u v = 0
  · by_cases hused : 0 < a u v ∨ 0 < a v u
    · simpa [add_w, unknownSupportGraph, hknown, hused] using hcapone
    · have hazero : a u v = 0 := by
        have huv : a u v ≤ 0 := not_lt.mp (fun h => hused (Or.inl h))
        have hvu : a v u ≤ 0 := not_lt.mp (fun h => hused (Or.inr h))
        rw [ha u v] at hvu
        linarith
      have hgzero := feasible_zero_edge hg.1 hknown
      simpa only [hgzero, hazero, _root_.add_zero, abs_zero] using
        (H.add (unknownSupportGraph H a ha)).nonneg u v
  · have hone : H.w u v = 1 := (hH u v).resolve_left hknown
    simpa [add_w, unknownSupportGraph, hknown, hone] using hcapone

/-- Sparse augmentation is a derived existence theorem. Its hypotheses are
the actual learned/input graphs, minimum values, and the target deficit. -/
theorem exists_sparse_augmentation {H G : WeightedGraph V}
    (hH : AllPairsAudit.Unweighted H) (hG : AllPairsAudit.Unweighted G)
    (hHG : H.IsSubgraph G) {s t : V} (hst : s ≠ t) {f k : ℕ}
    (hlower : (f : ℝ) - (k : ℝ) ≤ terminalValue H s t)
    (hupper : terminalValue H s t < f) (hfeas : (f : ℝ) ≤ terminalValue G s t) :
    ∃ Q : WeightedGraph V, AllPairsAudit.Unweighted Q ∧ Q.IsSubgraph G ∧
      (∀ u v, 0 < Q.w u v → H.w u v = 0) ∧
      AllPairsAudit.Unweighted (H.add Q) ∧
      Q.edgeMass ≤ Real.sqrt 2 * Fintype.card V * Real.sqrt k ∧
      ∃ F : V → V → ℝ, FlowSpec (H.add Q) s t f F := by
  let g := maximumFlow H s t
  have hg : FlowSpec H s t (terminalValue H s t) g := maximumFlow_spec H hH hst
  have hfint : IntegerValue (f : ℝ) := ⟨(f : ℤ), by simp⟩
  obtain ⟨a, ha, hcap, hdiv, hint, hcycle⟩ :=
    exists_residual_augmentation hG hHG hst hg hfint hupper.le hfeas
  let Q := unknownSupportGraph H a ha
  have hr : 0 ≤ (f : ℝ) - terminalValue H s t := by linarith
  have hrk : (f : ℝ) - terminalValue H s t ≤ k := by linarith
  refine ⟨Q, unknownSupportGraph_unit H a ha,
    unknownSupportGraph_le hG hHG hg ha hcap,
    fun u v h => unknownSupportGraph_unknown H a ha h,
    unknownSupportGraph_add_unit hH a ha, ?_, ?_⟩
  · calc
      Q.edgeMass ≤ (positiveArcs a).card := unknownSupportGraph_mass_le H a ha
      _ = (supportSize (naturalPositive a) : ℝ) := by rw [positiveArcs_card a hint]
      _ ≤ Real.sqrt 2 * Fintype.card V * Real.sqrt ((f : ℝ) - terminalValue H s t) :=
        cycle_free_support_bound ha hint hcycle s t hr hdiv
      _ ≤ Real.sqrt 2 * Fintype.card V * Real.sqrt k :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hrk) (by positivity)
  · refine ⟨fun u v => g u v + a u v, ?_⟩
    have hflow := unknownSupportGraph_flow hH hG hHG hg ha hcap hdiv hint
    have he : terminalValue H s t + ((f : ℝ) - terminalValue H s t) = f := by ring
    rwa [he] at hflow

def variation (H : WeightedGraph V) (φ : V → ℝ) : ℝ :=
  (∑ u, ∑ v, H.w u v * |φ u - φ v|) / 2

theorem variation_add (H Q : WeightedGraph V) (φ : V → ℝ) :
    variation (H.add Q) φ = variation H φ + variation Q φ := by
  simp only [variation, add_w, add_mul, sum_add_distrib, add_div]

theorem flow_potential_identity {f : V → V → ℝ} (hf : IsFlow f) (φ : V → ℝ) :
    (∑ u, ∑ v, f u v * (φ v - φ u)) = -2 * ∑ u, φ u * netOut f u := by
  have hcross : (∑ u, ∑ v, f u v * φ v) = -∑ u, φ u * netOut f u := by
    rw [sum_comm, ← sum_neg_distrib]
    apply sum_congr rfl
    intro v _
    rw [netOut, mul_sum, ← sum_neg_distrib]
    apply sum_congr rfl
    intro u _
    rw [hf v u]
    ring
  have hrow : (∑ u, ∑ v, f u v * φ u) = ∑ u, φ u * netOut f u := by
    simp only [netOut, mul_sum]
    apply sum_congr rfl
    intro u _
    apply sum_congr rfl
    intro v _
    ring
  simp only [mul_sub, sum_sub_distrib, hcross, hrow]
  ring

/-- Flow duality supplies the potential-variation lower bound directly;
no path-decomposition oracle is required. -/
theorem FlowSpec.variation_lower {H : WeightedGraph V} {s t : V} {r : ℝ}
    {f : V → V → ℝ} (hf : FlowSpec H s t r f) (φ : V → ℝ)
    (hs : φ s = 0) (ht : φ t = 1) : r ≤ variation H φ := by
  have hrow : (∑ u, φ u * netOut f u) = -r := by
    simp only [hf.2.1, mul_sub, mul_ite, mul_zero, sum_sub_distrib,
      sum_ite_eq', mem_univ, ↓reduceIte, hs, ht, zero_mul, one_mul, zero_sub]
  have hid := flow_potential_identity hf.1.1 φ
  rw [hrow] at hid
  have hpair (u v : V) : f u v * (φ v - φ u) ≤ H.w u v * |φ u - φ v| := by
    calc
      f u v * (φ v - φ u) ≤ |f u v * (φ v - φ u)| := le_abs_self _
      _ = |f u v| * |φ v - φ u| := abs_mul _ _
      _ ≤ H.w u v * |φ v - φ u| :=
        mul_le_mul_of_nonneg_right (hf.1.2 u v) (abs_nonneg _)
      _ = _ := by rw [abs_sub_comm]
  have hsum := sum_le_sum (s := (univ : Finset V)) fun u _ =>
    sum_le_sum (s := (univ : Finset V)) fun v _ => hpair u v
  rw [hid] at hsum
  unfold variation
  linarith

theorem cut_separation_sum (H : WeightedGraph V) (S : Finset V) :
    (∑ u, ∑ v, H.w u v * (if Witness.Separates u v S then (1 : ℝ) else 0)) =
      2 * H.cut S := by
  have he : (∑ u, ∑ v, H.w u v * (if Witness.Separates u v S then (1 : ℝ) else 0)) =
      H.cut S + H.cut Sᶜ := by
    rw [H.cut_eq_sum_ite S, H.cut_eq_sum_ite Sᶜ, ← sum_add_distrib]
    apply sum_congr rfl
    intro u _
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro v _
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp [Witness.Separates, hu, hv]
  rw [H.cut_compl] at he
  linarith

/-- Known variation is bounded by the witnessed cut threshold, averaged
over all padded witnesses with their actual multiplicities. -/
theorem witness_variation_le (A : Finset (Finset V)) {H : WeightedGraph V}
    (hH : AllPairsAudit.Unweighted H) (b : ℕ) (hne : (Witness.paddedWitnesses A H b).Nonempty) :
    variation H (fun v => (Witness.potential A H b v : ℝ)) ≤ b := by
  let W := Witness.paddedWitnesses A H b
  let φ : V → ℝ := fun v => (Witness.potential A H b v : ℝ)
  have hWpos : (0 : ℝ) < W.card := by exact_mod_cast (card_pos.mpr hne)
  have hj (u v : V) : |φ u - φ v| * W.card ≤
      (Witness.separatedWitnesses A H b u v).card := by
    have hcast := (Rat.cast_le (K := ℝ)).mpr
      (Witness.potential_separation A H b u v hne)
    simpa only [φ, W, Rat.cast_mul, Rat.cast_abs, Rat.cast_sub, Rat.cast_natCast] using hcast
  have hcount (u v : V) : ((Witness.separatedWitnesses A H b u v).card : ℝ) =
      ∑ w ∈ W, if Witness.Separates u v w.1 then (1 : ℝ) else 0 := by
    simp only [W, Witness.separatedWitnesses, card_filter, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero]
  have hright : (∑ u, ∑ v, H.w u v *
      (Witness.separatedWitnesses A H b u v).card) = 2 * ∑ w ∈ W, H.cut w.1 := by
    calc
      (∑ u, ∑ v, H.w u v * (Witness.separatedWitnesses A H b u v).card) =
          ∑ u, ∑ v, ∑ w ∈ W, H.w u v *
            (if Witness.Separates u v w.1 then (1 : ℝ) else 0) := by
          simp only [hcount, mul_sum]
      _ = ∑ u, ∑ w ∈ W, ∑ v, H.w u v *
          (if Witness.Separates u v w.1 then (1 : ℝ) else 0) :=
        sum_congr rfl (fun u _ => sum_comm)
      _ = ∑ w ∈ W, ∑ u, ∑ v, H.w u v *
          (if Witness.Separates u v w.1 then (1 : ℝ) else 0) := sum_comm
      _ = ∑ w ∈ W, 2 * H.cut w.1 := sum_congr rfl (fun w _ => cut_separation_sum H w.1)
      _ = _ := (mul_sum ..).symm
  have hleft : (∑ u, ∑ v, H.w u v * |φ u - φ v|) * W.card ≤
      ∑ u, ∑ v, H.w u v * (Witness.separatedWitnesses A H b u v).card := by
    simp only [sum_mul, mul_assoc]
    exact sum_le_sum fun u _ => sum_le_sum fun v _ =>
      mul_le_mul_of_nonneg_left (hj u v) (H.nonneg u v)
  rw [hright] at hleft
  have hcuts : (∑ w ∈ W, H.cut w.1) ≤ (W.card : ℝ) * b := by
    calc
      ∑ w ∈ W, H.cut w.1 ≤ ∑ _w ∈ W, (b : ℝ) :=
        sum_le_sum fun w hw => Witness.paddedWitnesses_cut_le A hH hw
      _ = _ := by simp
  change variation H φ ≤ b
  unfold variation
  nlinarith

theorem variation_le_mass_mul (Q : WeightedGraph V) (φ : V → ℝ) (d : ℝ)
    (hd : ∀ u v, 0 < Q.w u v → |φ u - φ v| ≤ d) :
    variation Q φ ≤ Q.edgeMass * d := by
  have hpair (u v : V) : Q.w u v * |φ u - φ v| ≤ Q.w u v * d := by
    by_cases hpos : 0 < Q.w u v
    · exact mul_le_mul_of_nonneg_left (hd u v hpos) (Q.nonneg u v)
    · have hz : Q.w u v = 0 := le_antisymm (not_lt.mp hpos) (Q.nonneg u v)
      simp [hz]
  have hsum := sum_le_sum (s := (univ : Finset V)) fun u _ =>
    sum_le_sum (s := (univ : Finset V)) fun v _ => hpair u v
  simp only [← sum_mul] at hsum
  unfold variation edgeMass
  linarith

theorem long_edge_of_variation (Q : WeightedGraph V) (φ : V → ℝ) {c M : ℝ}
    (hc : 0 < c) (hM : 0 < M) (hvar : c ≤ variation Q φ) (hmass : Q.edgeMass ≤ M) :
    ∃ u v, 0 < Q.w u v ∧ c / M ≤ |φ u - φ v| := by
  have hne : (positiveArcs Q.w).Nonempty := by
    by_contra hn
    have hz : ∀ u v, Q.w u v = 0 := by
      intro u v
      have hnot : ¬ 0 < Q.w u v := fun h => hn ⟨(u, v), by simp [positiveArcs, h]⟩
      exact le_antisymm (not_lt.mp hnot) (Q.nonneg u v)
    have hv : variation Q φ = 0 := by simp [variation, hz]
    rw [hv] at hvar
    linarith
  obtain ⟨e, he, hmax⟩ := exists_max_image (positiveArcs Q.w)
    (fun e => |φ e.1 - φ e.2|) hne
  refine ⟨e.1, e.2, (mem_filter.mp he).2, ?_⟩
  have hbound := variation_le_mass_mul Q φ |φ e.1 - φ e.2| (by
    intro u v h
    exact hmax (u, v) (by simp [positiveArcs, h]))
  apply (div_le_iff₀ hM).mpr
  have hm := mul_le_mul_of_nonneg_right hmass (abs_nonneg (φ e.1 - φ e.2))
  nlinarith

def phaseDelta (n k : ℕ) : ℚ :=
  ((k / 2 + 1 : ℕ) : ℚ) / (2 * (n : ℚ) * (⌈Real.sqrt (k : ℝ)⌉₊ : ℚ))

theorem ceil_sqrt_pos {k : ℕ} (hk : 1 ≤ k) : 0 < ⌈Real.sqrt (k : ℝ)⌉₊ := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hs := (Real.sqrt_pos.mpr hkpos).trans_le (Nat.le_ceil (Real.sqrt (k : ℝ)))
  exact_mod_cast hs

theorem phaseDelta_pos {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) : 0 < phaseDelta n k := by
  have hr := ceil_sqrt_pos hk
  unfold phaseDelta
  positivity

theorem phaseDelta_cast (n k : ℕ) :
    (phaseDelta n k : ℝ) =
      ((k / 2 + 1 : ℕ) : ℝ) / (2 * (n : ℝ) * (⌈Real.sqrt (k : ℝ)⌉₊ : ℝ)) := by
  simp [phaseDelta]

theorem ceil_sqrt_le_two_sqrt {k : ℕ} (hk : 1 ≤ k) :
    (⌈Real.sqrt (k : ℝ)⌉₊ : ℝ) ≤ 2 * Real.sqrt (k : ℝ) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hs : (1 : ℝ) ≤ Real.sqrt (k : ℝ) := by
    simpa using Real.sqrt_le_sqrt hkR
  have hc := (Nat.ceil_lt_add_one (Real.sqrt_nonneg (k : ℝ))).le
  linarith

theorem phaseDelta_le_half {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n) :
    phaseDelta n k ≤ 1 / 2 := by
  have hc : k / 2 + 1 ≤ k := by omega
  have hcQ : ((k / 2 + 1 : ℕ) : ℚ) ≤ k := by exact_mod_cast hc
  have hknQ : (k : ℚ) ≤ n := by exact_mod_cast hkn
  have hr : (1 : ℚ) ≤ (⌈Real.sqrt (k : ℝ)⌉₊ : ℚ) := by
    exact_mod_cast (Nat.succ_le_of_lt (ceil_sqrt_pos hk))
  have hnQ : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
  unfold phaseDelta
  apply (div_le_iff₀ (by positivity : (0 : ℚ) <
    2 * (n : ℚ) * (⌈Real.sqrt (k : ℝ)⌉₊ : ℚ))).mpr
  have hm := mul_le_mul_of_nonneg_left hr hnQ.le
  nlinarith

/-- The literal scale estimate used by the phase's public fuel. -/
theorem phaseDelta_ge_sqrt {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    Real.sqrt (k : ℝ) / (8 * (n : ℝ)) ≤ (phaseDelta n k : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hr : (0 : ℝ) < (⌈Real.sqrt (k : ℝ)⌉₊ : ℝ) := by
    exact_mod_cast ceil_sqrt_pos hk
  have hc : (k : ℝ) ≤ 2 * ((k / 2 + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show k ≤ 2 * (k / 2 + 1) by omega)
  have hs := ceil_sqrt_le_two_sqrt hk
  have hp := mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg (k : ℝ))
  have hsq := Real.sq_sqrt (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have hsmall : Real.sqrt (k : ℝ) * (⌈Real.sqrt (k : ℝ)⌉₊ : ℝ) ≤
      4 * ((k / 2 + 1 : ℕ) : ℝ) := by nlinarith
  rw [phaseDelta_cast]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hm := mul_le_mul_of_nonneg_left hsmall (show (0 : ℝ) ≤ 2 * n by positivity)
  nlinarith

theorem phaseDelta_ge_reciprocal {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    (1 : ℚ) / (8 * n) ≤ phaseDelta n k := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hs : (1 : ℝ) ≤ Real.sqrt (k : ℝ) := by
    simpa using Real.sqrt_le_sqrt hkR
  have h : (1 : ℝ) / (8 * n) ≤ (phaseDelta n k : ℝ) :=
    (div_le_div_of_nonneg_right hs (by positivity)).trans (phaseDelta_ge_sqrt hn hk)
  have h' : (((1 : ℚ) / (8 * (n : ℚ)) : ℚ) : ℝ) ≤ (phaseDelta n k : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat,
      Rat.cast_natCast] using h
  exact (Rat.cast_le (K := ℝ)).mp h'

/-- A successful search loses at least this fraction of all padded witnesses. -/
theorem phaseDelta_quarter_ge {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    Real.sqrt (k : ℝ) / (32 * n) ≤ (phaseDelta n k : ℝ) / 4 := by
  have h := div_le_div_of_nonneg_right (phaseDelta_ge_sqrt hn hk) (by norm_num : (0 : ℝ) ≤ 4)
  convert h using 1 <;> ring

theorem phaseDelta_four_div_le {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    (4 : ℝ) / (phaseDelta n k : ℝ) ≤ 32 * n / Real.sqrt (k : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hs := Real.sqrt_pos.mpr hkR
  have hd : (0 : ℝ) < (phaseDelta n k : ℝ) := by exact_mod_cast phaseDelta_pos hn hk
  have h := (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * n)).mp
    (phaseDelta_ge_sqrt hn hk)
  apply (div_le_div_iff₀ hd hs).mpr
  nlinarith

/-- A feasible target and a nonempty actual witness family expose an actual
unknown edge. The residual augmentation is used only in this proof. -/
theorem exists_long_unknown_edge (C : Finset V) (K L G : WeightedGraph V)
    {s t : V} (hst : s ≠ t)
    (hH : AllPairsAudit.Unweighted (K.add L)) (hG : AllPairsAudit.Unweighted G)
    (hHG : (K.add L).IsSubgraph G)
    (hL : ∀ u v, u ∉ C ∨ v ∉ C → L.w u v = 0)
    {f k : ℕ} (hk : 1 ≤ k) (hkf : k ≤ f) (hfn : f ≤ Fintype.card V - 1)
    (hlower : (f : ℝ) - (k : ℝ) ≤ terminalValue (K.add L) s t)
    (hfeas : (f : ℝ) ≤ terminalValue G s t)
    (hne : (Witness.canonicalWitnesses C K s t L (f - k / 2 - 1)).Nonempty) :
    ∃ u v, G.w u v = 1 ∧ (K.add L).w u v = 0 ∧
      phaseDelta (Fintype.card V) k ≤
        |Witness.potential (canonicalFamily C K s t) (K.add L) (f - k / 2 - 1) u -
          Witness.potential (canonicalFamily C K s t) (K.add L) (f - k / 2 - 1) v| := by
  let b := f - k / 2 - 1
  let A := canonicalFamily C K s t
  let φ : V → ℝ := fun v => (Witness.potential A (K.add L) b v : ℝ)
  have hbn : b ≤ Fintype.card V - 1 := by dsimp [b]; omega
  have hbf : b < f := by dsimp [b]; omega
  obtain ⟨S, htS, hsS, hcut⟩ :=
    (Witness.canonicalWitnesses_nonempty_iff C K L hst hH hbn hL).mp hne
  have hmin : terminalValue (K.add L) s t ≤ b := by
    have h := terminalValue_le_cut (K.add L) hst (mem_compl.mpr hsS)
      (show t ∉ Sᶜ by simpa using htS)
    rw [(K.add L).cut_compl] at h
    exact h.trans hcut
  have hupper : terminalValue (K.add L) s t < f :=
    hmin.trans_lt (by exact_mod_cast hbf)
  obtain ⟨Q, hQunit, hQG, hQunknown, _, hQmass, F, hF⟩ :=
    exists_sparse_augmentation hH hG hHG hst hlower hupper hfeas
  have hterm := Witness.canonical_potential_terminals C K L hst hne
  have hφs : φ s = 0 := by
    simpa only [φ, A, b, Rat.cast_zero] using congrArg (fun q : ℚ => (q : ℝ)) hterm.1
  have hφt : φ t = 1 := by
    simpa only [φ, A, b, Rat.cast_one] using congrArg (fun q : ℚ => (q : ℝ)) hterm.2
  have hknown : variation (K.add L) φ ≤ b := witness_variation_le A hH b hne
  have htotal : (f : ℝ) ≤ variation ((K.add L).add Q) φ := hF.variation_lower φ hφs hφt
  rw [variation_add] at htotal
  have hfb : b + (k / 2 + 1) = f := by dsimp [b]; omega
  have hfbR : (b : ℝ) + ((k / 2 + 1 : ℕ) : ℝ) = f := by exact_mod_cast hfb
  have hnew : ((k / 2 + 1 : ℕ) : ℝ) ≤ variation Q φ := by linarith
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨s⟩
  have hroot := ceil_sqrt_pos hk
  let M : ℝ := 2 * (Fintype.card V : ℝ) * (⌈Real.sqrt (k : ℝ)⌉₊ : ℝ)
  have hM : 0 < M := by dsimp [M]; positivity
  have hMbound : Q.edgeMass ≤ M := by
    have htwo : Real.sqrt 2 ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      Q.edgeMass ≤ Real.sqrt 2 * Fintype.card V * Real.sqrt k := hQmass
      _ ≤ 2 * Fintype.card V * Real.sqrt k :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right htwo (Nat.cast_nonneg _)) (Real.sqrt_nonneg _)
      _ ≤ M := mul_le_mul_of_nonneg_left (Nat.le_ceil (Real.sqrt (k : ℝ))) (by positivity)
  obtain ⟨u, v, huv, hlong⟩ := long_edge_of_variation Q φ
    (by positivity : (0 : ℝ) < ((k / 2 + 1 : ℕ) : ℝ)) hM hnew hMbound
  have hQone : Q.w u v = 1 := by
    rcases hQunit u v with hz | ho
    · rw [hz] at huv
      exact False.elim ((lt_irrefl 0) huv)
    · exact ho
  have hGone : G.w u v = 1 := by
    have hle := hQG u v
    rw [hQone] at hle
    rcases hG u v with hz | ho
    · rw [hz] at hle
      linarith
    · exact ho
  refine ⟨u, v, hGone, hQunknown u v huv, ?_⟩
  have hlongR : (phaseDelta (Fintype.card V) k : ℝ) ≤ |φ u - φ v| := by
    rw [phaseDelta_cast]
    exact hlong
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [φ, A, b, Rat.cast_abs, Rat.cast_sub] using hlongR

end
end CutQueryComplexity.CanonicalST.Augmentation

#print axioms CutQueryComplexity.CanonicalST.Augmentation.unknownSupportGraph_le
#print axioms CutQueryComplexity.CanonicalST.Augmentation.unknownSupportGraph_mass_le
#print axioms CutQueryComplexity.CanonicalST.Augmentation.unknownSupportGraph_flow
#print axioms CutQueryComplexity.CanonicalST.Augmentation.exists_sparse_augmentation
#print axioms CutQueryComplexity.CanonicalST.Augmentation.FlowSpec.variation_lower
#print axioms CutQueryComplexity.CanonicalST.Augmentation.witness_variation_le
#print axioms CutQueryComplexity.CanonicalST.Augmentation.long_edge_of_variation
#print axioms CutQueryComplexity.CanonicalST.Augmentation.phaseDelta_pos
#print axioms CutQueryComplexity.CanonicalST.Augmentation.exists_long_unknown_edge

#print axioms CutQueryComplexity.CanonicalST.Augmentation.phaseDelta_le_half
#print axioms CutQueryComplexity.CanonicalST.Augmentation.phaseDelta_ge_sqrt
#print axioms CutQueryComplexity.CanonicalST.Augmentation.phaseDelta_ge_reciprocal
#print axioms CutQueryComplexity.CanonicalST.Augmentation.phaseDelta_quarter_ge
#print axioms CutQueryComplexity.CanonicalST.Augmentation.phaseDelta_four_div_le
