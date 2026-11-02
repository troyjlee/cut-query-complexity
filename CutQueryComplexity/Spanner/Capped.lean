import CutQueryComplexity.Spanner.Query
import CutQueryComplexity.Probability.Truncation

/-! # Capped spanner trials and amplification (D3; source `lem:spanner`)

`trialR`: draw independent fair coins for the `K` sampled phases, then run the trial program
(`trialQ`). `capped` truncates it at `Q = (3 + 3k) · 6n(K + 1)` queries and also rejects outputs
with more than `4n(K + 1)` pairs.

* `capped_valid`: every returned spanner is the semantic trial's output for some coin sequence.
  It is therefore supported in the original pairs, has stretch `2K + 1`, and has at most
  `4n(K + 1)` pairs.
* `capped_fail_le`: the cap rejects only when the trial has more than `4n(K + 1)` reports. The
  trial costs at most `(3 + 3k)(reports + 2n(K + 1))` queries, and the spanner has at most as many
  pairs as reports. So failure has probability at most `1/2` (Markov, `mass_trialReports_gt`).
* `amp`: up to `J` fresh capped trials, returning the first success. Every restart uses the
  original support predicate and fresh coins. Failure is at most `2^{-J}` (`amp_fail_le`), every
  returned spanner is valid (`amp_valid`), and the worst-case cost is `J · Q` queries on every
  execution, including failures.
-/

namespace CutQueryComplexity
namespace Spanner

open Finset Probability
open scoped ENNReal

noncomputable section

attribute [local instance 10] Classical.propDecidable

variable {V : Type} [Fintype V] [DecidableEq V] {κ : Type} [LinearOrder κ] {key : Sym2 V → κ}

/-! ## The spanner is no larger than the number of reports -/

theorem card_selOf_le (coin : V → Bool) (st : State V) (a : V) :
    (selOf key coin st a).card ≤ (reportsOf key coin st a).card := by
  have : selOf key coin st a ⊆ (reportsOf key coin st a).image fun D =>
      s(a, (minNbr key a (toClus st a D)).getD a) := by
    intro f hf
    obtain ⟨D, y, hr, hy, rfl⟩ := (mem_filter.mp hf).2
    exact mem_image.mpr ⟨D, mem_filter.mpr ⟨mem_univ _, hr⟩, by rw [hy]; rfl⟩
  exact (card_le_card this).trans card_image_le

theorem card_selected_le (coin : V → Bool) (st : State V) :
    (selected key coin st).card ≤ totalReports key coin st := by
  have : selected key coin st = univ.biUnion fun a => selOf key coin st a := by
    ext f; simp [selected, selOf]
  rw [this]
  exact card_biUnion_le.trans (sum_le_sum fun a _ => card_selOf_le coin st a)

theorem card_H_runPhases_le (coins : ℕ → V → Bool) (E0 : Finset (Sym2 V)) :
    ∀ j, (runPhases key coins E0 j).H.card ≤
      ∑ i ∈ range j, totalReports key (coins i) (runPhases key coins E0 i)
  | 0 => by simp [runPhases, init]
  | j + 1 => by
      simp only [runPhases, step, sum_range_succ]
      exact (card_union_le _ _).trans (add_le_add (card_H_runPhases_le coins E0 j)
        (card_selected_le _ _))

theorem card_trial_le {K : ℕ} (cs : Fin K → V → Bool) (E0 : Finset (Sym2 V)) :
    (trial key (extCoins cs) E0 (K + 1)).H.card ≤ trialReports key E0 cs := by
  simp only [trial, Nat.add_sub_cancel, step]
  refine (card_union_le _ _).trans (add_le_add ?_ (card_selected_le _ _))
  refine (card_H_runPhases_le (extCoins cs) E0 K).trans (le_of_eq ?_)
  exact (Fin.sum_univ_eq_sum_range (fun i => totalReports key (extCoins cs i)
    (runPhases key (extCoins cs) E0 i)) K).symm

/-! ## The capped trial -/

variable (key)

/-- The uncapped randomized trial: fresh fair coins, then the trial program. -/
def trialR (K kq : ℕ) (P : Sym2 V → Bool) :
    RTree (Finset V) ℕ (Finset (Sym2 V)) (K * phBudget V kq + phBudget V kq) :=
  RTree.mix ((coinSeqPMF V K).map fun cs => RTree.ofDeterministic (trialQ key cs kq P))

/-- The query cap of one trial. -/
def capQ (V : Type) [Fintype V] (K kq : ℕ) : ℕ := (3 + 3 * kq) * (6 * Fintype.card V * (K + 1))

/-- The size cap of one spanner. -/
def capH (V : Type) [Fintype V] (K : ℕ) : ℕ := 4 * Fintype.card V * (K + 1)

/-- **The capped trial**: truncated at `capQ` queries, rejecting spanners above `capH`. -/
def capped (K kq : ℕ) (P : Sym2 V → Bool) :
    RTree (Finset V) ℕ (Option (Finset (Sym2 V))) (capQ V K kq) :=
  ((trialR key K kq P).truncate (capQ V K kq)).map fun o =>
    o.bind fun H => if H.card ≤ capH V K then some H else none

variable {key}

/-- The output of the capped trial for one coin sequence. -/
def cappedOut (G : DiGraph V) (K kq : ℕ) (P : Sym2 V → Bool) (cs : Fin K → V → Bool) :
    Option (Finset (Sym2 V)) :=
  if (trialQ key cs kq P).cost G.out ≤ capQ V K kq then
    (if ((trialQ key cs kq P).eval G.out).card ≤ capH V K then
      some ((trialQ key cs kq P).eval G.out) else none)
  else none

theorem eval_capped (G : DiGraph V) (K kq : ℕ) (P : Sym2 V → Bool) :
    (capped key K kq P).eval G.out = (coinSeqPMF V K).map (cappedOut (key := key) G K kq P) := by
  simp only [capped, RTree.eval_map, RTree.eval_truncate, trialR, RTree.run_mix, PMF.map_bind]
  rw [PMF.bind_map]
  simp only [Function.comp_def, RTree.run_ofDeterministic, PMF.pure_map, PMF.map_comp]
  rw [PMF.map]
  congr 1
  funext cs
  simp only [Function.comp_apply, cappedOut, DTree.cost, DTree.eval]
  congr 1
  by_cases h1 : (DTree.run G.out (trialQ key cs kq P)).2 ≤ capQ V K kq <;>
    by_cases h2 : ((DTree.run G.out (trialQ key cs kq P)).1).card ≤ capH V K <;>
    simp [h1, h2]

/-- **Every returned spanner is valid.** -/
theorem cappedOut_valid (hinj : Function.Injective key) (G : DiGraph V) {K kq : ℕ}
    (hk : Fintype.card V ≤ 2 ^ kq) (P : Sym2 V → Bool) (cs : Fin K → V → Bool)
    {H : Finset (Sym2 V)} (hH : cappedOut (key := key) G K kq P cs = some H) :
    H = (trial key (extCoins cs) (support G P) (K + 1)).H ∧ H.card ≤ capH V K := by
  unfold cappedOut at hH
  rw [trialQ_correct hinj cs hk P] at hH
  split_ifs at hH with h1 h2
  · cases hH; exact ⟨rfl, h2⟩

/-- **The cap rejects with probability at most one half.** -/
theorem capped_fail_le (hinj : Function.Injective key) (G : DiGraph V) {K kq : ℕ}
    (hk : Fintype.card V ≤ 2 ^ kq) (hK : Fintype.card V ≤ 2 ^ K) (P : Sym2 V → Bool) :
    mass ((capped key K kq P).eval G.out) (fun o => o = none) ≤ 2⁻¹ := by
  rw [eval_capped, mass_map]
  refine le_trans (mass_mono _ fun cs hcs => ?_) (mass_trialReports_gt key hinj (support G P) hK)
  by_contra hle
  push Not at hle
  apply (show cappedOut (key := key) G K kq P cs ≠ none from ?_) hcs
  have hcost := trialQ_cost (G := G) hinj cs hk P
  have hcard := card_trial_le (key := key) cs (support G P)
  rw [← trialQ_correct hinj cs hk P] at hcard
  have h1 : (trialQ key cs kq P).cost G.out ≤ capQ V K kq := by
    unfold capQ
    calc _ ≤ (3 + 3 * kq) * (trialReports key (support G P) cs + 2 * Fintype.card V * (K + 1)) :=
          hcost
      _ ≤ (3 + 3 * kq) * (6 * Fintype.card V * (K + 1)) := by
          refine Nat.mul_le_mul_left _ ?_
          calc trialReports key (support G P) cs + 2 * Fintype.card V * (K + 1)
              ≤ 4 * Fintype.card V * (K + 1) + 2 * Fintype.card V * (K + 1) :=
                Nat.add_le_add_right hle _
            _ = 6 * Fintype.card V * (K + 1) := by ring
  have h2 : ((trialQ key cs kq P).eval G.out).card ≤ capH V K := by unfold capH; omega
  simp [cappedOut, h1, h2]

/-! ## Amplification -/

variable (key)

/-- Up to `J` fresh capped trials, returning the first success. -/
def amp (K kq : ℕ) (P : Sym2 V → Bool) :
    (J : ℕ) → RTree (Finset V) ℕ (Option (Finset (Sym2 V))) (J * capQ V K kq)
  | 0 => RTree.pure (PMF.pure none)
  | J + 1 => ((capped key K kq P).bind fun o => match o with
      | some H => RTree.pure (PMF.pure (some H))
      | none => amp K kq P J).cast (by ring)

variable {key}

/-- **Failure after `J` trials is at most `2^{-J}`.** -/
theorem amp_fail_le (hinj : Function.Injective key) (G : DiGraph V) {K kq : ℕ}
    (hk : Fintype.card V ≤ 2 ^ kq) (hK : Fintype.card V ≤ 2 ^ K) (P : Sym2 V → Bool) :
    ∀ J, mass ((amp key K kq P J).eval G.out) (fun o => o = none) ≤ (2⁻¹ : ℝ≥0∞) ^ J
  | 0 => by simp [amp]
  | J + 1 => by
      simp only [amp, RTree.eval_cast, RTree.eval_bind, mass_bind]
      rw [tsum_eq_single none]
      · rw [pow_succ']
        have h := capped_fail_le hinj G hk hK P
        rw [mass, show {x : Option (Finset (Sym2 V)) | x = none} = {none} from rfl,
          PMF.toOuterMeasure_apply_singleton] at h
        exact mul_le_mul' h (amp_fail_le hinj G hk hK P J)
      · intro o ho
        obtain ⟨H, rfl⟩ := Option.ne_none_iff_exists'.mp ho
        simp

/-- **Every returned spanner is a valid trial output.** -/
theorem amp_valid (hinj : Function.Injective key) (G : DiGraph V) {K kq : ℕ}
    (hk : Fintype.card V ≤ 2 ^ kq) (P : Sym2 V → Bool) :
    ∀ J, ∀ H, some H ∈ ((amp key K kq P J).eval G.out).support →
      ∃ cs : Fin K → V → Bool, H = (trial key (extCoins cs) (support G P) (K + 1)).H ∧
        H.card ≤ capH V K
  | 0 => by intro H hH; simp [amp] at hH
  | J + 1 => by
      intro H hH
      simp only [amp, RTree.eval_cast, RTree.eval_bind, PMF.mem_support_bind_iff] at hH
      obtain ⟨o, ho, hH⟩ := hH
      cases o with
      | none => exact amp_valid hinj G hk P J H hH
      | some H' =>
          simp only [RTree.eval_pure, PMF.support_pure, Set.mem_singleton_iff,
            Option.some.injEq] at hH
          subst hH
          rw [eval_capped, PMF.support_map] at ho
          obtain ⟨cs, -, hcs⟩ := ho
          obtain ⟨h1, h2⟩ := cappedOut_valid hinj G hk P cs hcs
          exact ⟨cs, h1, h2⟩

/-- **Size, stretch, and amplification** (source `lem:spanner`). After `J` fresh capped trials
(`J · capQ` queries on every execution), failure has probability at most `2^{-J}`. Every
returned spanner is supported in the original pairs, has at most `4n(K + 1)` pairs, and joins
every original pair `ab` by a path of length at most `(2K + 1) ℓ_{ab}`. -/
theorem amp_spanner (hinj : Function.Injective key) {ℓ : Sym2 V → ℝ}
    (hmono : ∀ e f, key f ≤ key e → ℓ f ≤ ℓ e) (hℓ : ∀ e, 0 ≤ ℓ e) (G : DiGraph V) {K kq : ℕ}
    (hk : Fintype.card V ≤ 2 ^ kq) (hK : Fintype.card V ≤ 2 ^ K) (P : Sym2 V → Bool) (J : ℕ) :
    mass ((amp key K kq P J).eval G.out) (fun o => o = none) ≤ (2⁻¹ : ℝ≥0∞) ^ J ∧
      ∀ H, some H ∈ ((amp key K kq P J).eval G.out).support →
        H ⊆ support G P ∧ H.card ≤ capH V K ∧
          ∀ a b, s(a, b) ∈ support G P → ∃ p : (Spectral.pairGraph H).Walk a b,
            p.IsPath ∧ (p.edges.map ℓ).sum ≤ (2 * K + 1 : ℕ) * ℓ s(a, b) := by
  refine ⟨amp_fail_le hinj G hk hK P J, fun H hH => ?_⟩
  obtain ⟨cs, rfl, hcard⟩ := amp_valid hinj G hk P J H hH
  have hE0 : ∀ a b, s(a, b) ∈ support G P → a ≠ b := fun a b h hab => by
    subst hab; simp [support] at h
  obtain ⟨hsub, -, -⟩ := trial_stretch (ℓ := ℓ) hinj hmono hE0 (extCoins cs) (Nat.succ_pos K)
  refine ⟨hsub, hcard, fun a b hab => ?_⟩
  obtain ⟨p, hp, hlen⟩ := trial_path hinj hmono hℓ hE0 (extCoins cs) (Nat.succ_pos K) hab
  refine ⟨p, hp, hlen.trans (le_of_eq ?_)⟩
  congr 2

end

end Spanner
end CutQueryComplexity
