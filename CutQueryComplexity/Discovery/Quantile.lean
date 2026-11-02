import CutQueryComplexity.Search.BinarySearch
import CutQueryComplexity.Search.Combinators
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Exact checkpoints for a nonnegative measure (Lemma 16)

A nonnegative measure `μ` on positions `0, …, n - 1` is accessed through its
prefix masses `pre μ k = μ 0 + ⋯ + μ (k - 1)`. For each threshold `j M / q`
with `1 ≤ j < q`, `quantileCheckpoints` finds by binary search the first prefix
`k` reaching it and records the exact masses of the prefixes `k` and `k - 1`,
together with the free prefixes `0` and `n`.

Every nonnegative `ν` with the same masses on the recorded prefixes is within
`M / q` of `μ` on every prefix, hence within `2 M / q` on every interval
(`quantileCheckpoints_spec`). Recording the predecessor `k - 1` handles large
atoms. The program makes at most `(q - 1) (log₂ n + 3)` prefix queries.
-/

namespace CutQueryComplexity
namespace Discovery

open Search Search.Comp Finset

/-- Prefix mass of the first `k` positions. -/
def pre (μ : ℕ → ℝ) (k : ℕ) : ℝ := ∑ i ∈ range k, μ i

@[simp] theorem pre_zero (μ : ℕ → ℝ) : pre μ 0 = 0 := by simp [pre]

theorem pre_mono {μ : ℕ → ℝ} {n : ℕ} (hμ : ∀ i < n, 0 ≤ μ i) {a b : ℕ} (hab : a ≤ b)
    (hb : b ≤ n) : pre μ a ≤ pre μ b := by
  unfold pre
  rw [← Finset.sum_range_add_sum_Ico μ hab]
  have : 0 ≤ ∑ k ∈ Ico a b, μ k :=
    Finset.sum_nonneg fun i hi => hμ i (by simp at hi; omega)
  linarith

/-- The first prefix among `1, …, n` whose answer is at least `t`. -/
noncomputable def crossing (n : ℕ) (t : ℝ) : Comp ℕ ℝ (Option ℕ) :=
  findFirst (fun k => (ask k).map fun m => decide (t ≤ m)) (List.range' 1 n)

/-- The checkpoints contributed by one threshold: the crossing and its predecessor. -/
noncomputable def thresholdCheckpoints (n : ℕ) (t : ℝ) : Comp ℕ ℝ (List (ℕ × ℝ)) :=
  (crossing n t).bind fun
    | none => Comp.pure []
    | some k => (ask k).bind fun a => (ask (k - 1)).map fun b => [(k, a), (k - 1, b)]

/-- Exact prefix checkpoints for the thresholds `j M / q`, `1 ≤ j < q`. -/
noncomputable def quantileCheckpoints (n q : ℕ) (M : ℝ) : Comp ℕ ℝ (List (ℕ × ℝ)) :=
  (mapList (fun j : ℕ => thresholdCheckpoints n ((j : ℝ) * M / q)) (List.range' 1 (q - 1))).map
    fun Ls => (0, 0) :: (n, M) :: Ls.flatten

theorem crossing_cost (o : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    (crossing n t).cost o ≤ Nat.log 2 n + 1 := by
  have := findFirst_cost o (fun k => (ask k).map fun m => decide (t ≤ m)) 1 _
    (List.range' 1 n) le_rfl (fun _ _ => by simp)
  simpa [crossing] using this

theorem thresholdCheckpoints_cost (o : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    (thresholdCheckpoints n t).cost o ≤ Nat.log 2 n + 3 := by
  have := crossing_cost o n t
  simp only [thresholdCheckpoints, cost_bind]
  split <;> simp <;> omega

section Spec

variable {o : ℕ → ℝ} {μ : ℕ → ℝ} {n : ℕ}

/-- The binary search returns the first prefix reaching a positive threshold `t ≤ μ([n])`. -/
theorem crossing_spec (hμ : ∀ i < n, 0 ≤ μ i) (ho : ∀ k ≤ n, o k = pre μ k) {t : ℝ}
    (ht : 0 < t) (htM : t ≤ pre μ n) :
    ∃ k, (crossing n t).eval o = some k ∧ 1 ≤ k ∧ k ≤ n ∧ t ≤ pre μ k ∧
      pre μ (k - 1) < t := by
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at htM; linarith
    · exact h
  have hspec := findFirst_spec o (fun k => (ask k).map fun m => decide (t ≤ m))
    (fun k => t ≤ pre μ k) 1 _ (List.range' 1 n) le_rfl
    (fun x hx => by
      rw [List.mem_range'_1] at hx
      simp [ho x (by omega)])
    ((List.pairwise_lt_range' (s := 1) (n := n)).imp_of_mem fun {a b} ha hb hab h => by
      rw [List.mem_range'_1] at ha hb
      exact le_trans h (pre_mono hμ hab.le (by omega)))
  obtain ⟨L₁, y, L₂, hL, hpy, hL₁, hev⟩ :=
    hspec.2.1 n (List.mem_range'_1.mpr ⟨hn, by omega⟩) htM
  have hy : y ∈ List.range' 1 n := by rw [hL]; simp
  rw [List.mem_range'_1] at hy
  refine ⟨y, hev, hy.1, by omega, hpy, ?_⟩
  rcases Nat.eq_zero_or_pos (y - 1) with h0 | h0
  · rw [h0, pre_zero]; exact ht
  · -- `y - 1` lies strictly before `y` in the sorted list, hence in `L₁`.
    have hmem : y - 1 ∈ List.range' 1 n := List.mem_range'_1.mpr ⟨h0, by omega⟩
    have hpw := hL ▸ (List.pairwise_lt_range' (s := 1) (n := n))
    rw [List.pairwise_append] at hpw
    rw [hL, List.mem_append] at hmem
    rcases hmem with h1 | h2
    · exact lt_of_not_ge (hL₁ _ h1)
    · rcases List.mem_cons.mp h2 with h | h
      · omega
      · have := (List.pairwise_cons.mp hpw.2.1).1 _ h; omega

/-- Lemma 16. The recorded prefixes are exact, there are at most `2q` of them, and every
nonnegative measure agreeing on them is within `2M/q` of `μ` on every interval. -/
theorem quantileCheckpoints_spec (hμ : ∀ i < n, 0 ≤ μ i) (ho : ∀ k ≤ n, o k = pre μ k)
    {q : ℕ} (hq : 1 ≤ q) (hM : 0 < pre μ n) :
    let out := (quantileCheckpoints n q (pre μ n)).eval o
    (∀ p ∈ out, p.1 ≤ n ∧ p.2 = pre μ p.1) ∧ out.length ≤ 2 * q ∧
    (∀ ν : ℕ → ℝ, (∀ i < n, 0 ≤ ν i) → (∀ p ∈ out, pre ν p.1 = p.2) →
      ∀ a b, a ≤ b → b ≤ n →
        |∑ i ∈ Ico a b, μ i - ∑ i ∈ Ico a b, ν i| ≤ 2 * pre μ n / q) ∧
    (quantileCheckpoints n q (pre μ n)).cost o ≤ (q - 1) * (Nat.log 2 n + 3) := by
  intro out
  set M := pre μ n with hMdef
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  -- The threshold `j M / q` for `1 ≤ j < q` is positive and at most `M`.
  have hthr : ∀ j : ℕ, 1 ≤ j → j < q → 0 < (j : ℝ) * M / q ∧ (j : ℝ) * M / q ≤ M := by
    intro j hj1 hjq
    have hj : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    have hjq' : (j : ℝ) ≤ q := by exact_mod_cast hjq.le
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ hqpos]; nlinarith
  -- The checkpoints contributed by one threshold.
  have hblock : ∀ j : ℕ, 1 ≤ j → j < q → ∃ k, 1 ≤ k ∧ k ≤ n ∧
      (j : ℝ) * M / q ≤ pre μ k ∧ pre μ (k - 1) < (j : ℝ) * M / q ∧
      (thresholdCheckpoints n ((j : ℝ) * M / q)).eval o = [(k, pre μ k), (k - 1, pre μ (k - 1))] := by
    intro j hj1 hjq
    obtain ⟨k, hev, hk1, hkn, hge, hlt⟩ :=
      crossing_spec hμ ho (hthr j hj1 hjq).1 (hthr j hj1 hjq).2
    refine ⟨k, hk1, hkn, hge, hlt, ?_⟩
    simp [thresholdCheckpoints, hev, ho k hkn, ho (k - 1) (by omega)]
  have hout : out = (0, 0) :: (n, M) :: ((List.range' 1 (q - 1)).map fun j : ℕ =>
      (thresholdCheckpoints n ((j : ℝ) * M / q)).eval o).flatten := by
    simp [out, quantileCheckpoints, M]
  have hmemblock : ∀ j : ℕ, 1 ≤ j → j < q → ∀ p ∈ (thresholdCheckpoints n ((j : ℝ) * M / q)).eval o,
      p ∈ out := by
    intro j hj1 hjq p hp
    rw [hout]
    refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_flatten.mpr ⟨_, ?_, hp⟩))
    exact List.mem_map.mpr ⟨j, List.mem_range'_1.mpr ⟨hj1, by omega⟩, rfl⟩
  -- Exactness of every recorded prefix.
  have hexact : ∀ p ∈ out, p.1 ≤ n ∧ p.2 = pre μ p.1 := by
    intro p hp
    rw [hout] at hp
    simp only [List.mem_cons, List.mem_flatten, List.mem_map, List.mem_range'_1] at hp
    rcases hp with rfl | rfl | ⟨l, ⟨j, ⟨hj1, hjq⟩, rfl⟩, hp⟩
    · simp
    · simp [M]
    · obtain ⟨k, hk1, hkn, -, -, hev⟩ := hblock j hj1 (by omega)
      rw [hev] at hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ⟨hkn, rfl⟩
      · exact ⟨by simp; omega, rfl⟩
  refine ⟨hexact, ?_, ?_, ?_⟩
  · -- Each threshold contributes two checkpoints.
    have hlen : ∀ j ∈ List.range' 1 (q - 1),
        ((thresholdCheckpoints n ((j : ℝ) * M / q)).eval o).length = 2 := by
      intro j hj
      rw [List.mem_range'_1] at hj
      obtain ⟨k, -, -, -, -, hev⟩ := hblock j hj.1 (by omega)
      simp [hev]
    rw [hout]
    simp only [List.length_cons, List.length_flatten, List.map_map]
    rw [List.map_congr_left (fun j hj => by simpa using hlen j hj)]
    simp; omega
  · intro ν hν hagree
    -- Agreement on the recorded prefixes, in terms of `μ`.
    have hag : ∀ p ∈ out, pre ν p.1 = pre μ p.1 := fun p hp =>
      (hagree p hp).trans (hexact p hp).2
    -- Pointwise prefix error at most `M / q`.
    have hpoint : ∀ x ≤ n, |pre μ x - pre ν x| ≤ M / q := by
      intro x hx
      -- Bracket `x` between checkpoints whose `μ`-masses differ by at most `M / q`.
      suffices h : ∃ c₁ c₂, c₁ ≤ x ∧ x ≤ c₂ ∧ c₂ ≤ n ∧ pre ν c₁ = pre μ c₁ ∧
          pre ν c₂ = pre μ c₂ ∧ pre μ c₂ - pre μ c₁ ≤ M / q by
        obtain ⟨c₁, c₂, h1, h2, h3, e1, e2, hd⟩ := h
        have := pre_mono hμ h1 hx
        have := pre_mono hμ h2 h3
        have := pre_mono hν h1 hx
        have := pre_mono hν h2 h3
        rw [abs_le]; constructor <;> linarith
      have hPx0 : 0 ≤ pre μ x := by simpa using pre_mono hμ (Nat.zero_le x) hx
      set j₀ := min (q - 1) ⌊pre μ x * q / M⌋₊ with hj₀
      have hlow : (j₀ : ℝ) * M / q ≤ pre μ x := by
        have hf : (⌊pre μ x * q / M⌋₊ : ℝ) ≤ pre μ x * q / M := Nat.floor_le (by positivity)
        have : (j₀ : ℝ) ≤ pre μ x * q / M :=
          le_trans (by exact_mod_cast min_le_right _ _) hf
        rw [div_le_iff₀ hqpos]
        rw [le_div_iff₀ hM] at this
        linarith
      have hj₀q : j₀ ≤ q - 1 := min_le_left _ _
      -- The lower checkpoint.
      obtain ⟨c₁, hc₁x, hc₁, hc₁m⟩ : ∃ c₁, c₁ ≤ x ∧ (c₁, pre μ c₁) ∈ out ∧
          (j₀ : ℝ) * M / q ≤ pre μ c₁ := by
        rcases Nat.eq_zero_or_pos j₀ with h0 | h0
        · refine ⟨0, Nat.zero_le _, by rw [hout]; simp, by simp [h0]⟩
        · obtain ⟨k, hk1, hkn, hge, hlt, hev⟩ := hblock j₀ h0 (by omega)
          refine ⟨k, ?_, hmemblock j₀ h0 (by omega) _ (by rw [hev]; simp), hge⟩
          by_contra hkx
          have := pre_mono hμ (show x ≤ k - 1 by omega) (by omega)
          linarith
      -- The upper checkpoint.
      obtain ⟨c₂, hxc₂, hc₂n, hc₂, hc₂m⟩ : ∃ c₂, x ≤ c₂ ∧ c₂ ≤ n ∧ (c₂, pre μ c₂) ∈ out ∧
          pre μ c₂ ≤ ((j₀ : ℝ) + 1) * M / q := by
        by_cases htop : j₀ + 1 ≤ q - 1
        · have hj₀f : j₀ = ⌊pre μ x * q / M⌋₊ := by omega
          have hup : pre μ x < ((j₀ : ℝ) + 1) * M / q := by
            have := Nat.lt_floor_add_one (pre μ x * q / M)
            rw [← hj₀f, div_lt_iff₀ hM] at this
            rw [lt_div_iff₀ hqpos]; linarith
          obtain ⟨k, hk1, hkn, hge, hlt, hev⟩ := hblock (j₀ + 1) (by omega) (by omega)
          push_cast at hlt hev
          refine ⟨k - 1, ?_, by omega,
            hmemblock (j₀ + 1) (by omega) (by omega) _ (by push_cast; rw [hev]; simp), hlt.le⟩
          by_contra hkx
          have := pre_mono hμ (show k ≤ x by omega) hx
          push_cast at hge
          linarith
        · have hj : (j₀ : ℝ) + 1 = q := by
            have : j₀ + 1 = q := by omega
            exact_mod_cast this
          refine ⟨n, hx, le_rfl, by rw [hout]; simp [M], ?_⟩
          rw [hj, mul_div_cancel_left₀ _ hqpos.ne']
      refine ⟨c₁, c₂, hc₁x, hxc₂, hc₂n, hag _ hc₁, hag _ hc₂, ?_⟩
      have : ((j₀ : ℝ) + 1) * M / q - (j₀ : ℝ) * M / q = M / q := by ring
      linarith
    intro a b hab hb
    rw [Finset.sum_Ico_eq_sub μ hab, Finset.sum_Ico_eq_sub ν hab]
    have h1 := hpoint b hb
    have h2 := hpoint a (le_trans hab hb)
    simp only [pre] at h1 h2
    calc _ = |(∑ k ∈ range b, μ k - ∑ k ∈ range b, ν k) -
          (∑ k ∈ range a, μ k - ∑ k ∈ range a, ν k)| := by ring_nf
      _ ≤ _ := abs_sub _ _
      _ ≤ M / q + M / q := add_le_add h1 h2
      _ = 2 * M / q := by ring
  · simp only [quantileCheckpoints, cost_map]
    have := cost_mapList_le o (fun j : ℕ => thresholdCheckpoints n ((j : ℝ) * M / q))
      (List.range' 1 (q - 1)) (c := Nat.log 2 n + 3)
      (fun j _ => thresholdCheckpoints_cost o n _)
    simpa [Nat.mul_comm] using this

end Spec

end Discovery
end CutQueryComplexity
