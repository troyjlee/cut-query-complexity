import CutQueryComplexity.Hierarchy.RealError
import CutQueryComplexity.Hierarchy.Children
import CutQueryComplexity.Graph.Integral
import CutQueryComplexity.TwoRespecting.TreeCover

/-! # A weak skeleton from a supplied hierarchy (Theorem 15)

Given a hierarchy `H` whose representation cost at some minimum cut `S*` is at most
`B λ`, the program queries the cluster cuts and quantile checkpoints (Lemma 17),
chooses a completion `F` offline, and outputs `H₀ = F + s J`, where `J` is a guard
graph for the tree (Lemma 19) and `s = 1/(10ρB)`. With `q = ⌈200 ρ² B²⌉` the
completion error is at most `s² L²/λ` for every real labelling of cost `L` extending
`S` (Lemma 18), which gives

* `λ ≤ c_{H₀}(S)` for every proper shore (`supplied_lower`), and
* `c_{H₀}(S*) ≤ (111/100) λ` (`supplied_upper`),

so `H₀` is a weak skeleton of `G` (`supplied_weakSkeleton`). The guard is taken as
the explicit hypothesis `GuardFor H ρ`: for subadditive capacities, a graph `J` whose
cuts dominate the cost of some real extension of `S` and are at most `ρ R(S)`. It is
supplied by the star-mesh construction of `Hierarchy.Guard` with `ρ = 2 · height`. The program uses the cluster
cuts already queried by the completion, so it costs no further queries.
-/

namespace CutQueryComplexity
namespace Hierarchy

open TwoRespecting WeightedGraph Search Search.Comp Discovery Finset

variable {V : Type} [Fintype V] [DecidableEq V]

theorem le_mincutValue (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V) {lam : ℝ}
    (h : ∀ S, ProperShore S → lam ≤ G.cut S) : lam ≤ mincutValue G := by
  have hne : (properShores V).Nonempty := by
    obtain ⟨v⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card V by omega)
    exact ⟨{v}, (mem_properShores _).mpr (properShore_singleton v hn)⟩
  rw [mincutValue, dite_eq_left_of_eq_true (eq_true hne)]
  exact Finset.le_inf' _ _ fun S hS => h S ((mem_properShores S).mp hS)

namespace Hier

variable {N : Type} [Fintype N] [DecidableEq N] [LinearOrder N] (H : Hier V N)

/-- Lemma 19 as a hypothesis: guard graphs of quality `ρ` for nonnegative subadditive
capacities on the tree. The lower bound is through some real extension of `S`. -/
def GuardFor (ρ : ℝ) : Prop :=
  ∀ cap : N → ℝ, (∀ x, 0 ≤ cap x) → H.Subadd cap →
    ∃ J : WeightedGraph V, ∀ S,
      (∃ a, H.ExtendsR S a ∧ H.labelCost cap a ≤ J.cut S) ∧ J.cut S ≤ ρ * H.rep cap S

/-- Capacities read off the recorded data (clamped to be nonnegative). -/
noncomputable def capOf (D : N → Option (ℝ × List (ℕ × ℝ) × List (ℕ × ℝ))) : N → ℝ :=
  fun x => max 0 (((D x).map Prod.fst).getD 0)

omit [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N] [LinearOrder N] in
theorem capOf_nonneg (D : N → Option (ℝ × List (ℕ × ℝ) × List (ℕ × ℝ))) (x : N) :
    0 ≤ capOf D x := le_max_left _ _

variable {H}

open Classical in
/-- A guard graph for the given capacities, chosen offline (empty if they are not
subadditive). -/
noncomputable def guardOf {ρ : ℝ} (hg : H.GuardFor ρ) (cap : N → ℝ) (hcap : ∀ x, 0 ≤ cap x) :
    WeightedGraph V :=
  if hs : H.Subadd cap then Classical.choose (hg cap hcap hs) else 0

omit [LinearOrder N] in
theorem guardOf_spec {ρ : ℝ} (hg : H.GuardFor ρ) (cap : N → ℝ) (hcap : ∀ x, 0 ≤ cap x)
    (hs : H.Subadd cap) (S : Finset V) :
    (∃ a, H.ExtendsR S a ∧ H.labelCost cap a ≤ (guardOf hg cap hcap).cut S) ∧
      (guardOf hg cap hcap).cut S ≤ ρ * H.rep cap S := by
  classical
  have h := Classical.choose_spec (hg cap hcap hs) S
  unfold guardOf
  rw [dite_eq_left_of_eq_true (eq_true hs)]
  exact h

omit [Fintype V] [DecidableEq V] [LinearOrder N] in
theorem labelCost_congr {cap cap' : N → ℝ} (h : ∀ x ∈ H.edges, cap x = cap' x)
    (ℓ : N → ℝ) : H.labelCost cap ℓ = H.labelCost cap' ℓ :=
  Finset.sum_congr rfl fun x hx => by rw [h x hx]

omit [LinearOrder N] in
theorem rep_congr {cap cap' : N → ℝ} (h : ∀ x ∈ H.edges, cap x = cap' x) (S : Finset V) :
    H.rep cap S = H.rep cap' S := by
  unfold rep
  exact Finset.inf'_congr _ rfl fun ℓ _ => labelCost_congr h _

variable (H)

/-- **Theorem 15**: the skeleton program. -/
noncomputable def supplied {ρ : ℝ} (hg : H.GuardFor ρ) (s : ℝ) (hs : 0 ≤ s) (q : ℕ) :
    Comp (Finset V) ℝ (WeightedGraph V) :=
  (tabulate (H.clusterData q) H.edges.toList).map fun D =>
    (H.completionOf D).add ((guardOf hg (capOf D) (capOf_nonneg D)).scale s hs)

variable {H}

/-- The data, the completion, and the capacities on the genuine oracle. -/
theorem supplied_eval (G : WeightedGraph V) {ρ : ℝ} (hg : H.GuardFor ρ) {s : ℝ} (hs : 0 ≤ s)
    (q : ℕ) :
    ∃ cap : N → ℝ, ∃ hcap : ∀ x, 0 ≤ cap x,
      (∀ x ∈ H.edges, cap x = H.canon G x) ∧ H.Subadd cap ∧
      (H.supplied hg s hs q).eval G.cut =
        ((H.completion q).eval G.cut).add ((guardOf hg cap hcap).scale s hs) := by
  classical
  set D := (tabulate (H.clusterData q) H.edges.toList).eval G.cut
  have hceq : ∀ x ∈ H.edges, capOf D x = H.canon G x := fun x hx => by
    obtain ⟨lo, li, heq, -⟩ := clusterData_eval (H := H) G q x
    have hD : D x = some ((H.clusterData q x).eval G.cut) := by
      simp [D, Finset.mem_toList.mpr hx]
    simp only [capOf, hD, heq, Option.map_some, Option.getD_some, canon]
    exact max_eq_right (G.cut_nonneg _)
  refine ⟨capOf D, capOf_nonneg D, hceq,
    subadd_congr (fun x hx => (hceq x hx).symm) (canon_subadd G), ?_⟩
  simp [supplied, completion, D]

theorem supplied_cost (G : WeightedGraph V) {ρ : ℝ} (hg : H.GuardFor ρ) {s : ℝ} (hs : 0 ≤ s)
    {q : ℕ} (hq : 1 ≤ q) :
    (H.supplied hg s hs q).cost G.cut ≤
      H.edges.card * (1 + 4 * ((q - 1) * (Nat.log 2 (Fintype.card V) + 3))) := by
  have := (completion_spec (H := H) G hq).2.2
  simpa [supplied, completion] using this

/-- The completion error, in the form used below. -/
theorem completion_close (G : WeightedGraph V) {q : ℕ} (hq : 1 ≤ q) {η : ℝ}
    (hqη : 2 / (q : ℝ) ≤ η) (hlam : 0 < mincutValue G) {S : Finset V} {a : N → ℝ}
    (ha : H.ExtendsR S a) :
    G.cut S - η * H.labelCost (H.canon G) a ^ 2 / mincutValue G ≤
      ((H.completion q).eval G.cut).cut S ∧
    ((H.completion q).eval G.cut).cut S ≤
      G.cut S + η * H.labelCost (H.canon G) a ^ 2 / mincutValue G := by
  have h := completion_cut_error_real (H := H) G hq hlam ha
  have hR : 0 ≤ H.labelCost (H.canon G) a ^ 2 / mincutValue G := by positivity
  have hmono : 2 / (q : ℝ) * H.labelCost (H.canon G) a ^ 2 / mincutValue G ≤
      η * H.labelCost (H.canon G) a ^ 2 / mincutValue G := by
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right hqη hR
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

/-- **Lower bound.** No proper shore of the skeleton is lighter than `λ(G)`. -/
theorem supplied_lower (G : WeightedGraph V) {ρ : ℝ} (hg : H.GuardFor ρ) {s : ℝ} (hs : 0 ≤ s)
    {q : ℕ} (hq : 1 ≤ q) (hqs : 2 / (q : ℝ) ≤ s ^ 2) (hlam : 0 < mincutValue G)
    {S : Finset V} (hS : ProperShore S) :
    mincutValue G ≤ ((H.supplied hg s hs q).eval G.cut).cut S := by
  obtain ⟨cap, hcap, hcapeq, hsub, heval⟩ := supplied_eval (H := H) G hg hs q
  rw [heval, cut_add, cut_scale]
  set lam := mincutValue G
  obtain ⟨a, ha, hJ'⟩ := (guardOf_spec hg cap hcap hsub S).1
  set R := H.labelCost (H.canon G) a
  have hJ : R ≤ (guardOf hg cap hcap).cut S := by rwa [labelCost_congr hcapeq] at hJ'
  have hF := (completion_close (H := H) G hq hqs hlam ha).1
  have hFnn := ((H.completion q).eval G.cut).cut_nonneg S
  have hGS : lam ≤ G.cut S := mincutValue_le G hS
  have hR : 0 ≤ R := H.labelCost_nonneg (fun x => G.cut_nonneg _) a
  have hsJ : s * R ≤ s * (guardOf hg cap hcap).cut S := mul_le_mul_of_nonneg_left hJ hs
  by_cases hbig : lam ≤ s * R
  · linarith
  · -- here `(sR)² / λ ≤ sR`
    push Not at hbig
    have hsR : 0 ≤ s * R := mul_nonneg hs hR
    have hsq : s ^ 2 * R ^ 2 / lam ≤ s * R := by
      rw [div_le_iff₀ hlam]
      nlinarith
    linarith

/-- **Upper bound at the promised optimum.** -/
theorem supplied_upper (G : WeightedGraph V) {ρ B : ℝ} (hρ : 1 ≤ ρ) (hB : 1 ≤ B)
    (hg : H.GuardFor ρ) {q : ℕ} (hq : 1 ≤ q)
    (hqs : 2 / (q : ℝ) ≤ (1 / (10 * ρ * B)) ^ 2) (hlam : 0 < mincutValue G)
    {S : Finset V} (hRS : H.rep (H.canon G) S ≤ B * mincutValue G) (hSmin : G.cut S = mincutValue G) :
    ((H.supplied hg (1 / (10 * ρ * B)) (by positivity) q).eval G.cut).cut S ≤
      111 / 100 * mincutValue G := by
  set s := 1 / (10 * ρ * B)
  have hs : 0 ≤ s := by positivity
  obtain ⟨cap, hcap, hcapeq, hsub, heval⟩ := supplied_eval (H := H) G hg hs q
  rw [heval, cut_add, cut_scale]
  set lam := mincutValue G
  set R := H.rep (H.canon G) S
  have hJ : (guardOf hg cap hcap).cut S ≤ ρ * R := by
    have h := (guardOf_spec hg cap hcap hsub S).2; rwa [rep_congr hcapeq] at h
  obtain ⟨ℓ, hℓ, hRℓ⟩ := H.exists_rep_eq (H.canon G) S
  have hF := (completion_close (H := H) G hq hqs hlam (extendsR_toReal hℓ)).2
  rw [← hRℓ] at hF
  have hR : 0 ≤ R := le_trans (G.cut_nonneg S) (cut_le_rep G S)
  have hρB : 0 < ρ * B := by positivity
  -- `s² R² / λ ≤ λ / (100 ρ²) ≤ λ / 100` and `s ρ R ≤ λ / 10`
  have hsR : s * R ≤ lam / (10 * ρ) := by
    have : s * R ≤ s * (B * lam) := mul_le_mul_of_nonneg_left hRS hs
    calc s * R ≤ s * (B * lam) := this
      _ = lam / (10 * ρ) := by simp only [s]; field_simp
  have hsRnn : 0 ≤ s * R := mul_nonneg hs hR
  have h1 : s ^ 2 * R ^ 2 / lam ≤ lam / 100 := by
    rw [div_le_iff₀ hlam]
    have h10 : lam / (10 * ρ) ≤ lam / 10 := by
      apply div_le_div_of_nonneg_left hlam.le (by norm_num); nlinarith
    have : s * R ≤ lam / 10 := hsR.trans h10
    nlinarith
  have h2 : s * (guardOf hg cap hcap).cut S ≤ lam / 10 := by
    calc s * (guardOf hg cap hcap).cut S ≤ s * (ρ * R) := mul_le_mul_of_nonneg_left hJ hs
      _ = ρ * (s * R) := by ring
      _ ≤ ρ * (lam / (10 * ρ)) := mul_le_mul_of_nonneg_left hsR (by linarith)
      _ = lam / 10 := by field_simp
  rw [hSmin] at hF
  linarith

/-- **Theorem 15.** A supplied hierarchy with promise `R(S*) ≤ B λ` for some minimum
cut yields a weak skeleton, with at most
`|edges| (1 + 4 (q−1)(⌊log₂ n⌋ + 3))` queries for `q = ⌈200 ρ² B²⌉`. -/
theorem supplied_weakSkeleton (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V) {ρ B : ℝ}
    (hρ : 1 ≤ ρ) (hB : 1 ≤ B) (hg : H.GuardFor ρ) (hlam : 0 < mincutValue G)
    (hprom : ∃ S, IsMinCut G S ∧ H.rep (H.canon G) S ≤ B * mincutValue G) :
    IsWeakSkeleton G ((H.supplied hg (1 / (10 * ρ * B)) (by positivity)
      ⌈200 * ρ ^ 2 * B ^ 2⌉₊).eval G.cut) ∧
    (H.supplied hg (1 / (10 * ρ * B)) (by positivity) ⌈200 * ρ ^ 2 * B ^ 2⌉₊).cost G.cut ≤
      H.edges.card * (1 + 4 * ((⌈200 * ρ ^ 2 * B ^ 2⌉₊ - 1) *
        (Nat.log 2 (Fintype.card V) + 3))) := by
  set q := ⌈200 * ρ ^ 2 * B ^ 2⌉₊
  have hρB : 0 < ρ * B := by positivity
  have hq0 : (200 : ℝ) * ρ ^ 2 * B ^ 2 ≤ q := Nat.le_ceil _
  have hqpos : (0 : ℝ) < q := lt_of_lt_of_le (by positivity) hq0
  have hq : 1 ≤ q := by exact_mod_cast hqpos
  have hqs : 2 / (q : ℝ) ≤ (1 / (10 * ρ * B)) ^ 2 := by
    rw [div_le_iff₀ hqpos, div_pow, one_pow, mul_pow, mul_pow]
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    nlinarith
  obtain ⟨S, hS, hRS⟩ := hprom
  set H0 := (H.supplied hg (1 / (10 * ρ * B)) (by positivity) q).eval G.cut
  have hlow : ∀ T, ProperShore T → mincutValue G ≤ H0.cut T := fun T hT =>
    supplied_lower (H := H) G hg _ hq hqs hlam hT
  have hmin : mincutValue G ≤ mincutValue H0 := le_mincutValue H0 hn hlow
  have hSval : G.cut S = mincutValue G :=
    le_antisymm (le_mincutValue G hn hS.2) (mincutValue_le G hS.1)
  have hup := supplied_upper (H := H) G hρ hB hg hq hqs hlam hRS hSval
  refine ⟨⟨lt_of_lt_of_le hlam hmin, S, hS, ?_⟩, supplied_cost (H := H) G hg _ hq⟩
  calc 4 * H0.cut S ≤ 4 * (111 / 100 * mincutValue G) := by linarith
    _ ≤ 5 * mincutValue G := by linarith
    _ ≤ 5 * mincutValue H0 := by linarith

end Hier
end Hierarchy
end CutQueryComplexity
