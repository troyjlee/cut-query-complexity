import CutQueryComplexity.DirectedMincut.Extraction

/-! # Small shores (D5; source `lem:small`)

`δ = min_v min(d⁺(v), d⁻(v))` for a simple digraph, and `h ≥ 1`.

* `le_out_of_card_le`, `le_out_of_card_compl_le`: when `|S| ≤ δ` (or `|V∖S| ≤ δ`) and the shore
  is nonempty, `F(S) ≥ δ`, since `F(S) ≥ |S| δ − |S|(|S| − 1)`.
* `subset_Dplus`: when `|S| ≤ h` and `F(S) < δ`, every `v ∈ S` has `d⁺(v) ≤ δ + h − 1`.
  Symmetrically, the complement lies in `D₋` (`subset_Dminus`).
* `learn`: learn every pair multiplicity inside a public set `D`, one ordered search per pair
  found plus one finishing search per vertex. Its fuel need is at most `#pairs + |D|`, and the
  number of present pairs is at most `Σ_{v∈D} d⁺(v)` (`card_present_le_out`) or
  `Σ_{v∈D} d⁻(v)` (`card_present_le_in`).
* `smallShore`: query all degrees (`2n`). If `δ ≤ h`, learn the pairs inside `D₊` and `D₋`.
  Enumerate offline every candidate shore whose value is known exactly: subsets of `D₊`,
  complements of subsets of `D₋`, singletons and co-singletons. Return the least candidate with
  its queried value (`smallShore_correct`). Every nonempty proper shore `S` with
  `min(|S|, |V∖S|) ≤ h` has `F(S)` at least the returned value.
-/

namespace CutQueryComplexity
namespace DirectedMincut

open Finset

noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]
variable {G : DiGraph V}

/-! ## Degrees and the counting bounds -/

omit [LinearOrder V] in
theorem out_singleton (G : DiGraph V) (v : V) : G.out {v} = G.outdeg v := by
  have := G.out_add_arcs_self {v}
  simp [DiGraph.arcs, G.diag] at this
  omega

omit [LinearOrder V] in
theorem out_compl_singleton (G : DiGraph V) (v : V) : G.out (univ \ {v}) = G.indeg v := by
  have h := G.arcs_split_left (univ \ {v}) {v}
  rw [G.arcs_univ_left, sum_singleton] at h
  have hc : (univ \ {v})ᶜ = {v} := by ext x; simp
  have hin : G.arcs {v} {v} = 0 := by simp [DiGraph.arcs, G.diag]
  rw [hc, hin, add_zero] at h
  rw [DiGraph.out, hc, ← h]

omit [Fintype V] [LinearOrder V] in
/-- The arcs inside `S` number at most `|S|(|S| − 1)` in a simple digraph. -/
theorem arcs_self_le (hG : G.Simple) (S : Finset V) :
    G.arcs S S ≤ S.card * (S.card - 1) := by
  unfold DiGraph.arcs
  calc ∑ u ∈ S, ∑ v ∈ S, G.c u v ≤ ∑ u ∈ S, (S.card - 1) := sum_le_sum fun u hu => by
        rw [← sum_erase_add _ _ hu, G.diag, add_zero]
        calc ∑ v ∈ S.erase u, G.c u v ≤ ∑ v ∈ S.erase u, 1 := sum_le_sum fun v _ => hG u v
          _ = S.card - 1 := by simp [card_erase_of_mem hu]
    _ = S.card * (S.card - 1) := by simp

omit [LinearOrder V] in
/-- **Small shores have value at least `δ`** (out-degree form). -/
theorem le_out_of_card_le (hG : G.Simple) {δ : ℕ} (hδ : ∀ v, δ ≤ G.outdeg v) {S : Finset V}
    (hne : S.Nonempty) (hS : S.card ≤ δ) : δ ≤ G.out S := by
  have h1 := G.out_add_arcs_self S
  have h2 := arcs_self_le hG S
  have h3 : S.card * δ ≤ ∑ v ∈ S, G.outdeg v := by
    calc S.card * δ = ∑ v ∈ S, δ := by simp
      _ ≤ _ := sum_le_sum fun v _ => hδ v
  have hc : 1 ≤ S.card := hne.card_pos
  have key : δ + S.card * (S.card - 1) ≤ S.card * δ := by
    obtain ⟨m, hm⟩ : ∃ m, S.card = m + 1 := ⟨S.card - 1, by omega⟩
    rw [hm, Nat.add_sub_cancel]
    have : m ≤ δ := by omega
    nlinarith
  omega

omit [LinearOrder V] in
/-- **Small shores have value at least `δ`** (in-degree form, small complement). -/
theorem le_out_of_card_compl_le (hG : G.Simple) {δ : ℕ} (hδ : ∀ v, δ ≤ G.indeg v)
    {S : Finset V} (hne : Sᶜ.Nonempty) (hS : Sᶜ.card ≤ δ) : δ ≤ G.out S := by
  have h1 := G.arcs_split_left S Sᶜ
  rw [G.arcs_univ_left] at h1
  have h2 := arcs_self_le hG Sᶜ
  have h3 : Sᶜ.card * δ ≤ ∑ v ∈ Sᶜ, G.indeg v := by
    calc Sᶜ.card * δ = ∑ v ∈ Sᶜ, δ := by simp
      _ ≤ _ := sum_le_sum fun v _ => hδ v
  have hc : 1 ≤ Sᶜ.card := hne.card_pos
  have key : δ + Sᶜ.card * (Sᶜ.card - 1) ≤ Sᶜ.card * δ := by
    obtain ⟨m, hm⟩ : ∃ m, Sᶜ.card = m + 1 := ⟨Sᶜ.card - 1, by omega⟩
    rw [hm, Nat.add_sub_cancel]
    have : m ≤ δ := by omega
    nlinarith
  rw [DiGraph.out]
  omega

omit [LinearOrder V] in
/-- **Coverage by `D₊`.** -/
theorem outdeg_le_of_small (hG : G.Simple) {S : Finset V} {v : V} (hv : v ∈ S) :
    G.outdeg v + 1 ≤ S.card + G.out S := by
  have hsplit := G.arcs_split_right {v} S
  rw [G.arcs_univ_right, sum_singleton] at hsplit
  have hin : G.arcs {v} S ≤ S.card - 1 := by
    simp only [DiGraph.arcs, sum_singleton]
    rw [← sum_erase_add _ _ hv, G.diag, add_zero]
    calc ∑ x ∈ S.erase v, G.c v x ≤ ∑ x ∈ S.erase v, 1 := sum_le_sum fun x _ => hG v x
      _ = S.card - 1 := by simp [card_erase_of_mem hv]
  have hout : G.arcs {v} Sᶜ ≤ G.out S := by
    unfold DiGraph.out DiGraph.arcs
    rw [sum_singleton]
    exact single_le_sum (f := fun u => ∑ x ∈ Sᶜ, G.c u x) (fun _ _ => Nat.zero_le _) hv
  have hc : 1 ≤ S.card := card_pos.mpr ⟨v, hv⟩
  omega

omit [LinearOrder V] in
/-- **Coverage by `D₋`.** -/
theorem indeg_le_of_small (hG : G.Simple) {S : Finset V} {v : V} (hv : v ∈ Sᶜ) :
    G.indeg v + 1 ≤ Sᶜ.card + G.out S := by
  have hsplit := G.arcs_split_left Sᶜ {v}
  rw [G.arcs_univ_left, sum_singleton, compl_compl] at hsplit
  have hin : G.arcs Sᶜ {v} ≤ Sᶜ.card - 1 := by
    simp only [DiGraph.arcs, sum_singleton]
    rw [← sum_erase_add _ _ hv, G.diag, add_zero]
    calc ∑ x ∈ Sᶜ.erase v, G.c x v ≤ ∑ x ∈ Sᶜ.erase v, 1 := sum_le_sum fun x _ => hG x v
      _ = Sᶜ.card - 1 := by simp [card_erase_of_mem hv]
  have hout : G.arcs S {v} ≤ G.out S := by
    unfold DiGraph.out DiGraph.arcs
    refine sum_le_sum fun u _ => ?_
    rw [sum_singleton]
    exact single_le_sum (f := fun x => G.c u x) (fun _ _ => Nat.zero_le _) hv
  have hc : 1 ≤ Sᶜ.card := card_pos.mpr ⟨v, hv⟩
  omega

/-! ## Learning the pairs inside a public set -/

/-- The present canonical pairs inside `D`. -/
def present (G : DiGraph V) (D : Finset V) : Finset (V × V) :=
  univ.filter fun p => p.1 ∈ D ∧ p.2 ∈ D ∧ p.1 < p.2 ∧ 0 < G.sym p.1 p.2

theorem card_present_le_arcs (D : Finset V) : (present G D).card ≤ G.arcs D D := by
  rw [G.arcs_self_eq_sum_lt]
  calc (present G D).card = ∑ p ∈ present G D, 1 := by simp
    _ ≤ ∑ p ∈ present G D, G.sym p.1 p.2 := sum_le_sum fun p hp => by
        simp only [present, mem_filter] at hp; exact hp.2.2.2.2
    _ ≤ ∑ p ∈ D ×ˢ D, if p.1 < p.2 then G.sym p.1 p.2 else 0 := by
        rw [← sum_filter]
        exact sum_le_sum_of_subset_of_nonneg (fun p hp => by
          simp only [present, mem_filter] at hp
          simp [mem_product, hp.2.1, hp.2.2.1, hp.2.2.2.1]) fun _ _ _ => Nat.zero_le _
    _ = ∑ u ∈ D, ∑ v ∈ D.filter (u < ·), G.sym u v := by
        rw [sum_product]; simp [sum_filter]

theorem card_present_le_out (D : Finset V) : (present G D).card ≤ ∑ v ∈ D, G.outdeg v := by
  have := G.out_add_arcs_self D
  have := card_present_le_arcs (G := G) D
  omega

theorem card_present_le_in (D : Finset V) : (present G D).card ≤ ∑ v ∈ D, G.indeg v := by
  have h := G.arcs_split_left Dᶜ D
  rw [G.arcs_univ_left, compl_compl] at h
  have := card_present_le_arcs (G := G) D
  omega

/-- The learning state: learned multiplicities `M` and finished vertices `Dn`. -/
def learnCand (D : Finset V) (M : V → V → ℕ) (u : V) : List V :=
  (D.filter fun v => u < v ∧ M u v = 0).toList

/-- Learn pair multiplicities inside `D`, with `fuel` ordered searches. -/
def learn (k : ℕ) (D : Finset V) :
    (fuel : ℕ) → (V → V → ℕ) → Finset V → DTree (Finset V) ℕ (V → V → ℕ) (fuel * (3 + 3 * k))
  | 0, M, _ => DTree.pure M
  | fuel + 1, M, Dn =>
      if h : (D \ Dn).Nonempty then
        ((firstNbr ((D \ Dn).min' h) k (learnCand D M ((D \ Dn).min' h))).bind fun r =>
          match r with
          | some (v, m) => learn k D fuel
              (fun a b => if a = (D \ Dn).min' h ∧ b = v then m else M a b) Dn
          | none => learn k D fuel M (insert ((D \ Dn).min' h) Dn)).cast (by ring)
      else DTree.pure M

/-- The learning invariant. -/
structure LearnInv (G : DiGraph V) (D : Finset V) (M : V → V → ℕ) (Dn : Finset V) : Prop where
  sound : ∀ a b, M a b ≠ 0 → a ∈ D ∧ b ∈ D ∧ a < b ∧ M a b = G.sym a b
  fin : Dn ⊆ D
  done : ∀ a ∈ Dn, ∀ b ∈ D, a < b → M a b = G.sym a b

/-- The learned support. -/
def supp (M : V → V → ℕ) : Finset (V × V) := univ.filter fun p => M p.1 p.2 ≠ 0

theorem supp_subset_present {D : Finset V} {M : V → V → ℕ} {Dn : Finset V}
    (hI : LearnInv G D M Dn) : supp M ⊆ present G D := by
  intro p hp
  simp only [supp, mem_filter, mem_univ, true_and] at hp
  obtain ⟨h1, h2, h3, h4⟩ := hI.sound p.1 p.2 hp
  simp only [present, mem_filter, mem_univ, true_and]
  exact ⟨h1, h2, h3, by rw [← h4]; exact Nat.pos_of_ne_zero hp⟩

theorem learn_correct (G : DiGraph V) (D : Finset V) {k : ℕ} (hk : Fintype.card V ≤ 2 ^ k) :
    ∀ (fuel : ℕ) (M : V → V → ℕ) (Dn : Finset V), LearnInv G D M Dn →
      (present G D).card + D.card ≤ fuel + (supp M).card + Dn.card →
      ∀ a ∈ D, ∀ b ∈ D, a < b → (learn k D fuel M Dn).eval G.out a b = G.sym a b := by
  intro fuel
  induction fuel with
  | zero =>
      intro M Dn hI hpot a ha b hb hab
      simp only [learn, DTree.eval_pure]
      have h1 := card_le_card (supp_subset_present hI)
      have h2 := card_le_card hI.fin
      have hDn : Dn = D := eq_of_subset_of_card_le hI.fin (by omega)
      exact hI.done a (hDn ▸ ha) b hb hab
  | succ fuel ih =>
      intro M Dn hI hpot a ha b hb hab
      simp only [learn]
      split_ifs with h
      · set u := (D \ Dn).min' h
        have huDD : u ∈ D \ Dn := min'_mem _ h
        have huD : u ∈ D := (mem_sdiff.mp huDD).1
        have huDn : u ∉ Dn := (mem_sdiff.mp huDD).2
        have hnd : (learnCand D M u).Nodup := nodup_toList _
        have hu : u ∉ learnCand D M u := by simp [learnCand]
        have hlen : (learnCand D M u).length ≤ 2 ^ k := by
          rw [learnCand, length_toList]; exact (card_le_univ _).trans hk
        rw [DTree.eval_cast, DTree.eval_bind, firstNbr_correct G u k hnd hu hlen]
        cases hf : firstPos (G.sym u) (learnCand D M u) with
        | some r =>
            obtain ⟨v, m⟩ := r
            simp only
            have hfind : (learnCand D M u).find? (fun x => decide (0 < G.sym u x)) = some v ∧
                m = G.sym u v := by
              unfold firstPos at hf
              cases hx : (learnCand D M u).find? (fun x => decide (0 < G.sym u x)) with
              | none => rw [hx] at hf; cases hf
              | some x => rw [hx] at hf; simp at hf; obtain ⟨rfl, rfl⟩ := hf; exact ⟨rfl, rfl⟩
            obtain ⟨hfind, rfl⟩ := hfind
            have hvc : v ∈ learnCand D M u := List.mem_of_find?_eq_some hfind
            have hvpos : 0 < G.sym u v := by simpa using List.find?_some hfind
            simp only [learnCand, mem_toList, mem_filter] at hvc
            obtain ⟨hvD, huv, hM0⟩ := hvc
            set M' : V → V → ℕ := fun a b => if a = u ∧ b = v then G.sym u v else M a b
            have hI' : LearnInv G D M' Dn := by
              refine ⟨fun a b hne => ?_, hI.fin, fun a ha' b hb' hab' => ?_⟩
              · by_cases hab'' : a = u ∧ b = v
                · obtain ⟨rfl, rfl⟩ := hab''; simp [M'] at hne ⊢; exact ⟨huD, hvD, huv⟩
                · simp only [M', hab'', ite_false] at hne ⊢; exact hI.sound a b hne
              · have hau : a ≠ u := fun h' => huDn (h' ▸ ha')
                simp only [M', hau, false_and, ite_false]; exact hI.done a ha' b hb' hab'
            have hsupp : (supp M').card = (supp M).card + 1 := by
              have : supp M' = insert (u, v) (supp M) := by
                ext p
                simp only [supp, mem_filter, mem_univ, true_and, mem_insert, M']
                by_cases hp : p.1 = u ∧ p.2 = v
                · simp [hp, Prod.ext_iff, (Nat.pos_iff_ne_zero.mp hvpos)]
                · simp only [hp, ite_false]
                  constructor
                  · exact Or.inr
                  · rintro (h' | h')
                    · exact absurd ⟨by rw [h'], by rw [h']⟩ hp
                    · exact h'
              rw [this, card_insert_of_notMem]
              simp [supp, hM0]
            exact ih M' Dn hI' (by omega) a ha b hb hab
        | none =>
            simp only
            have hnone : ∀ b ∈ D, u < b → M u b = G.sym u b := by
              intro b hb hub
              by_cases hM : M u b = 0
              · by_contra hne
                have hpos : 0 < G.sym u b := by omega
                have hbc : b ∈ learnCand D M u := by simp [learnCand, hb, hub, hM]
                unfold firstPos at hf
                rw [Option.map_eq_none_iff, List.find?_eq_none] at hf
                exact hf b hbc (by simpa using hpos)
              · exact (hI.sound u b hM).2.2.2
            have hI' : LearnInv G D M (insert u Dn) :=
              ⟨hI.sound, insert_subset huD hI.fin, fun a ha' b hb' hab' => by
                rcases mem_insert.mp ha' with rfl | ha'
                · exact hnone b hb' hab'
                · exact hI.done a ha' b hb' hab'⟩
            exact ih M (insert u Dn) hI' (by rw [card_insert_of_notMem huDn]; omega) a ha b hb hab
      · simp only [DTree.eval_pure]
        have haDn : a ∈ Dn := by
          by_contra haDn; exact h ⟨a, mem_sdiff.mpr ⟨ha, haDn⟩⟩
        exact hI.done a haDn b hb hab

omit [Fintype V] [DecidableEq V] in
theorem learnInv_zero (D : Finset V) : LearnInv G D (fun _ _ => 0) ∅ :=
  ⟨fun _ _ h => absurd rfl h, empty_subset _, fun _ h => absurd h (Finset.notMem_empty _)⟩

/-! ## The degrees -/

/-- Query `F({v})` and `F(V ∖ {v})` for every listed vertex. -/
def degs : (vs : List V) → DTree (Finset V) ℕ ((V → ℕ) × (V → ℕ)) (2 * vs.length)
  | [] => DTree.pure (0, 0)
  | v :: vs => (DTree.query {v} fun a => DTree.query (univ \ {v}) fun b =>
      (degs vs).map fun fg => (Function.update fg.1 v a, Function.update fg.2 v b)).cast
        (by simp only [List.length_cons]; ring)

omit [LinearOrder V] in
theorem degs_correct (G : DiGraph V) (vs : List V) {w : V} (hw : w ∈ vs) :
    ((degs vs).eval G.out).1 w = G.outdeg w ∧ ((degs vs).eval G.out).2 w = G.indeg w := by
  induction vs with
  | nil => simp at hw
  | cons v vs ih =>
      simp only [degs, DTree.eval_cast, DTree.eval_query, DTree.eval_map]
      by_cases hwv : w = v
      · subst hwv
        simp [out_singleton, out_compl_singleton]
      · simp only [Function.update_of_ne hwv]
        exact ih ((List.mem_cons.mp hw).resolve_left hwv)

/-! ## The small-shore procedure -/

/-- `Σ_{v∈S} a(v) − Σ_{u<v in S} M(u, v)`: the value of a shore (out-degrees) or of a
complement (in-degrees) when `M` is correct inside `S`. -/
def formula (a : V → ℕ) (M : V → V → ℕ) (S : Finset V) : ℕ :=
  ∑ v ∈ S, a v - ∑ u ∈ S, ∑ v ∈ S.filter (u < ·), M u v

theorem formula_out {M : V → V → ℕ} {S : Finset V}
    (hM : ∀ u ∈ S, ∀ v ∈ S, u < v → M u v = G.sym u v) :
    formula G.outdeg M S = G.out S := by
  rw [formula, G.out_eq_sum_outdeg]
  congr 1
  exact sum_congr rfl fun u hu => sum_congr rfl fun v hv =>
    hM u hu v (mem_filter.mp hv).1 (mem_filter.mp hv).2

theorem formula_in {M : V → V → ℕ} {T : Finset V}
    (hM : ∀ u ∈ T, ∀ v ∈ T, u < v → M u v = G.sym u v) :
    formula G.indeg M T = G.out Tᶜ := by
  have h := G.arcs_split_left Tᶜ T
  rw [G.arcs_univ_left, compl_compl] at h
  rw [formula, DiGraph.out, compl_compl]
  have : ∑ u ∈ T, ∑ v ∈ T.filter (u < ·), M u v = ∑ u ∈ T, ∑ v ∈ T.filter (u < ·), G.sym u v :=
    sum_congr rfl fun u hu => sum_congr rfl fun v hv =>
      hM u hu v (mem_filter.mp hv).1 (mem_filter.mp hv).2
  rw [this, ← G.arcs_self_eq_sum_lt]
  omega

/-- A candidate: a shore given directly (`true`) or as a complement (`false`). -/
def candVal (dout din : V → ℕ) (M : V → V → ℕ) (c : Finset V × Bool) : ℕ :=
  if c.2 then formula dout M c.1 else formula din M c.1

/-- The shore of a candidate. -/
def candShore (c : Finset V × Bool) : Finset V := if c.2 then c.1 else c.1ᶜ

omit [LinearOrder V] in
theorem compl_nonempty_of_ne {S : Finset V} (h : S ≠ univ) : Sᶜ.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro h'
  apply h
  rw [← compl_compl S, h', compl_empty]

/-- The candidates: subsets of `Dp` and singletons (direct); subsets of `Dm` and singletons
(complements); all nonempty and proper. -/
def cands (Dp Dm : Finset V) : Finset (Finset V × Bool) :=
  ((univ : Finset (Finset V)).filter fun S => S.Nonempty ∧ S ≠ univ ∧ (S ⊆ Dp ∨ S.card = 1)).image
      (fun S => (S, true)) ∪
    ((univ : Finset (Finset V)).filter fun T => T.Nonempty ∧ T ≠ univ ∧ (T ⊆ Dm ∨ T.card = 1)).image
      (fun T => (T, false))

/-- The minimum degree `δ`. -/
def minDeg (dout din : V → ℕ) : ℕ := sInf (Set.range fun v => min (dout v) (din v))

/-- The learning fuel: `n · 2h` pairs and `n` finishing searches. -/
def learnFuel (h : ℕ) : ℕ := Fintype.card V * (2 * h) + Fintype.card V

/-- The least candidate under the computed values. -/
def pickCand (dout din : V → ℕ) (Mp Mm : V → V → ℕ) (Dp Dm : Finset V) : Finset V × Bool :=
  if hC : (cands Dp Dm).Nonempty then
    Classical.choose ((cands Dp Dm).exists_min_image
      (fun c => if c.2 then formula dout Mp c.1 else formula din Mm c.1) hC)
  else (∅, true)

theorem pickCand_spec (dout din : V → ℕ) (Mp Mm : V → V → ℕ) {Dp Dm : Finset V}
    (hC : (cands Dp Dm).Nonempty) :
    pickCand dout din Mp Mm Dp Dm ∈ cands Dp Dm ∧ ∀ c' ∈ cands Dp Dm,
      (if (pickCand dout din Mp Mm Dp Dm).2 then formula dout Mp (pickCand dout din Mp Mm Dp Dm).1
        else formula din Mm (pickCand dout din Mp Mm Dp Dm).1) ≤
      (if c'.2 then formula dout Mp c'.1 else formula din Mm c'.1) := by
  unfold pickCand; simp only [hC, ↓reduceDIte]
  exact Classical.choose_spec ((cands Dp Dm).exists_min_image _ hC)

/-- Query the chosen shore and return it with its value. -/
def finish (c : Finset V × Bool) : DTree (Finset V) ℕ (Finset V × ℕ) 1 :=
  DTree.query (candShore c) fun a => DTree.pure (q := 0) (candShore c, a)

/-- The sets `D₊` and `D₋` (empty when `δ > h`). -/
def Dset (a : V → ℕ) (δ h : ℕ) : Finset V := if δ ≤ h then univ.filter fun v => a v ≤ δ + h else ∅

/-- The small-shore procedure. -/
def smallShore (k h : ℕ) :
    DTree (Finset V) ℕ (Finset V × ℕ)
      (2 * Fintype.card V + (learnFuel (V := V) h * (3 + 3 * k) +
        (learnFuel (V := V) h * (3 + 3 * k) + 1))) :=
  ((degs (univ : Finset V).toList).cast (by rw [length_toList, card_univ])).bind fun dd =>
    (learn k (Dset dd.1 (minDeg dd.1 dd.2) h) (learnFuel h) (fun _ _ => 0) ∅).bind fun Mp =>
      (learn k (Dset dd.2 (minDeg dd.1 dd.2) h) (learnFuel h) (fun _ _ => 0) ∅).bind fun Mm =>
        finish (pickCand dd.1 dd.2 Mp Mm (Dset dd.1 (minDeg dd.1 dd.2) h)
          (Dset dd.2 (minDeg dd.1 dd.2) h))

omit [Fintype V] [DecidableEq V] [LinearOrder V] in
theorem minDeg_le (dout din : V → ℕ) (v : V) : minDeg dout din ≤ min (dout v) (din v) :=
  Nat.sInf_le ⟨v, rfl⟩

omit [Fintype V] [DecidableEq V] [LinearOrder V] in
theorem exists_minDeg [Nonempty V] (dout din : V → ℕ) :
    ∃ v, min (dout v) (din v) = minDeg dout din :=
  Nat.sInf_mem (s := Set.range fun v => min (dout v) (din v)) (Set.range_nonempty _)

/-- **The small-shore procedure is correct** (source `lem:small`). The returned shore is
nonempty and proper, its value is the queried cut, it is at most `δ`, and no nonempty proper
shore with `min(|S|, |V∖S|) ≤ h` has smaller value. -/
theorem smallShore_correct (hG : G.Simple) (hn : 2 ≤ Fintype.card V) {k : ℕ}
    (hk : Fintype.card V ≤ 2 ^ k) (h : ℕ) :
    let r := (smallShore k h).eval G.out
    r.1.Nonempty ∧ r.1 ≠ univ ∧ r.2 = G.out r.1 ∧
      G.out r.1 ≤ minDeg G.outdeg G.indeg ∧
      ∀ S : Finset V, S.Nonempty → S ≠ univ → (S.card ≤ h ∨ Sᶜ.card ≤ h) →
        G.out r.1 ≤ G.out S := by
  intro r
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  -- the degrees
  set dd := (degs (univ : Finset V).toList).eval G.out
  have hd1 : dd.1 = G.outdeg := funext fun w => (degs_correct G _ (mem_toList.mpr (mem_univ w))).1
  have hd2 : dd.2 = G.indeg := funext fun w => (degs_correct G _ (mem_toList.mpr (mem_univ w))).2
  set δ := minDeg G.outdeg G.indeg
  set Dp : Finset V := Dset G.outdeg δ h
  set Dm : Finset V := Dset G.indeg δ h
  -- learning is complete
  have hfuel : ∀ (D : Finset V) (a : V → ℕ), (∀ v ∈ D, a v ≤ δ + h) → (D = ∅ ∨ δ ≤ h) →
      (present G D).card ≤ ∑ v ∈ D, a v → (present G D).card + D.card ≤ learnFuel (V := V) h := by
    intro D a ha hD hp
    rcases hD with rfl | hδ
    · simp [present]
    · have h1 : ∑ v ∈ D, a v ≤ D.card * (2 * h) := by
        calc ∑ v ∈ D, a v ≤ ∑ v ∈ D, 2 * h := sum_le_sum fun v hv => by have := ha v hv; omega
          _ = _ := by simp
      have h2 : D.card ≤ Fintype.card V := card_le_univ D
      unfold learnFuel
      have := Nat.mul_le_mul_right (2 * h) h2
      omega
  have hDp : ∀ v ∈ Dp, G.outdeg v ≤ δ + h := fun v hv => by
    simp only [Dp, Dset] at hv; split_ifs at hv
    · simpa using hv
    · simp at hv
  have hDm : ∀ v ∈ Dm, G.indeg v ≤ δ + h := fun v hv => by
    simp only [Dm, Dset] at hv; split_ifs at hv
    · simpa using hv
    · simp at hv
  have hDpc : Dp = ∅ ∨ δ ≤ h := by by_cases hδ : δ ≤ h <;> simp [Dp, Dset, hδ]
  have hDmc : Dm = ∅ ∨ δ ≤ h := by by_cases hδ : δ ≤ h <;> simp [Dm, Dset, hδ]
  set Mp := (learn k Dp (learnFuel (V := V) h) (fun _ _ => 0) ∅).eval G.out
  set Mm := (learn k Dm (learnFuel (V := V) h) (fun _ _ => 0) ∅).eval G.out
  have hMp : ∀ a ∈ Dp, ∀ b ∈ Dp, a < b → Mp a b = G.sym a b :=
    learn_correct G Dp hk _ _ _ (learnInv_zero Dp) (by
      simpa [supp] using hfuel Dp G.outdeg hDp hDpc (card_present_le_out Dp))
  have hMm : ∀ a ∈ Dm, ∀ b ∈ Dm, a < b → Mm a b = G.sym a b :=
    learn_correct G Dm hk _ _ _ (learnInv_zero Dm) (by
      simpa [supp] using hfuel Dm G.indeg hDm hDmc (card_present_le_in Dm))
  -- every candidate's value is its true cut
  set C := cands (V := V) Dp Dm
  set val : Finset V × Bool → ℕ := fun c =>
    if c.2 then formula G.outdeg Mp c.1 else formula G.indeg Mm c.1
  have hval : ∀ c ∈ C, val c = G.out (candShore c) := by
    intro c hc
    simp only [C, cands, mem_union, mem_image, mem_filter, mem_univ, true_and] at hc
    rcases hc with ⟨S, ⟨-, -, hS⟩, rfl⟩ | ⟨T, ⟨-, -, hT⟩, rfl⟩
    · simp only [val, candShore, ite_true]
      apply formula_out
      intro u hu v hv huv
      rcases hS with hS | hS
      · exact hMp u (hS hu) v (hS hv) huv
      · obtain ⟨x, rfl⟩ := card_eq_one.mp hS
        simp at hu hv; subst hu; subst hv; exact absurd huv (lt_irrefl _)
    · simp only [val, candShore, Bool.false_eq_true, ite_false]
      apply formula_in
      intro u hu v hv huv
      rcases hT with hT | hT
      · exact hMm u (hT hu) v (hT hv) huv
      · obtain ⟨x, rfl⟩ := card_eq_one.mp hT
        simp at hu hv; subst hu; subst hv; exact absurd huv (lt_irrefl _)
  -- singletons are candidates
  have hsing : ∀ v : V, ({v}, true) ∈ C ∧ ({v}, false) ∈ C := by
    intro v
    have hne1 : ({v} : Finset V) ≠ univ := fun h' => by
      have := congrArg card h'; simp at this; omega
    constructor
    · simp only [C, cands, mem_union, mem_image, mem_filter, mem_univ, true_and]
      exact Or.inl ⟨{v}, ⟨singleton_nonempty v, hne1, Or.inr (card_singleton v)⟩, rfl⟩
    · simp only [C, cands, mem_union, mem_image, mem_filter, mem_univ, true_and]
      refine Or.inr ⟨{v}, ⟨singleton_nonempty v, hne1, Or.inr (card_singleton v)⟩, rfl⟩
  have hC : C.Nonempty := ⟨_, (hsing (Classical.arbitrary V)).1⟩
  obtain ⟨hcC, hcmin⟩ := pickCand_spec G.outdeg G.indeg Mp Mm hC
  set c := pickCand G.outdeg G.indeg Mp Mm Dp Dm
  have hdd : (degs (univ : Finset V).toList).eval G.out = (G.outdeg, G.indeg) := Prod.ext hd1 hd2
  have hr : r = (candShore c, G.out (candShore c)) := by
    simp only [r, smallShore, DTree.eval_bind, DTree.eval_cast, hdd, finish, DTree.eval_query,
      DTree.eval_pure]
    rfl
  -- the chosen shore beats every candidate
  have hbest : ∀ c' ∈ C, G.out (candShore c) ≤ G.out (candShore c') := fun c' hc' => by
    rw [← hval c hcC, ← hval c' hc']; exact hcmin c' hc'
  rw [hr]
  have hcne : (candShore c).Nonempty ∧ candShore c ≠ univ := by
    simp only [cands, mem_union, mem_image, mem_filter, mem_univ, true_and] at hcC
    rcases hcC with ⟨S, ⟨hS1, hS2, -⟩, hSc⟩ | ⟨T, ⟨hT1, hT2, -⟩, hTc⟩
    · rw [← hSc]; exact ⟨hS1, hS2⟩
    · rw [← hTc]; simp only [candShore, Bool.false_eq_true, ite_false]
      refine ⟨?_, fun h' => ?_⟩
      · exact compl_nonempty_of_ne hT2
      · rw [compl_eq_univ_iff] at h'; exact hT1.ne_empty h'
  refine ⟨hcne.1, hcne.2, rfl, ?_, ?_⟩
  · obtain ⟨v0, hv0⟩ := exists_minDeg G.outdeg G.indeg
    have h1 := hbest _ (hsing v0).1
    have h2 := hbest _ (hsing v0).2
    simp only [candShore, ite_true, Bool.false_eq_true, ite_false] at h1 h2
    rw [out_singleton] at h1
    have hcs : ({v0} : Finset V)ᶜ = univ \ {v0} := by ext; simp
    rw [hcs, out_compl_singleton] at h2
    exact (le_min h1 h2).trans_eq hv0
  · intro S hS1 hS2 hsmall
    have hδout : ∀ v, δ ≤ G.outdeg v := fun v => (minDeg_le _ _ v).trans (min_le_left _ _)
    have hδin : ∀ v, δ ≤ G.indeg v := fun v => (minDeg_le _ _ v).trans (min_le_right _ _)
    have hcδ : G.out (candShore c) ≤ δ := by
      obtain ⟨v0, hv0⟩ := exists_minDeg G.outdeg G.indeg
      have h1 := hbest _ (hsing v0).1
      have h2 := hbest _ (hsing v0).2
      simp only [candShore, ite_true, Bool.false_eq_true, ite_false] at h1 h2
      rw [out_singleton] at h1
      have hcs : ({v0} : Finset V)ᶜ = univ \ {v0} := by ext; simp
      rw [hcs, out_compl_singleton] at h2
      exact (le_min h1 h2).trans_eq hv0
    by_cases hge : δ ≤ G.out S
    · exact hcδ.trans hge
    · push Not at hge
      rcases hsmall with hsm | hsm
      · have hδh : δ ≤ h := by
          by_contra hδh
          exact absurd (le_out_of_card_le hG hδout hS1 (by omega)) (by omega)
        have hSD : S ⊆ Dp := by
          intro v hv
          have := outdeg_le_of_small hG hv
          simp only [Dp, Dset, hδh, ite_true, mem_filter, mem_univ, true_and]
          omega
        have hmem : (S, true) ∈ C := by
          simp only [C, cands, mem_union, mem_image, mem_filter, mem_univ, true_and]
          exact Or.inl ⟨S, ⟨hS1, hS2, Or.inl hSD⟩, rfl⟩
        simpa [candShore] using hbest _ hmem
      · have hT1 : Sᶜ.Nonempty := compl_nonempty_of_ne hS2
        have hδh : δ ≤ h := by
          by_contra hδh
          exact absurd (le_out_of_card_compl_le hG hδin hT1 (by omega)) (by omega)
        have hSD : Sᶜ ⊆ Dm := by
          intro v hv
          have := indeg_le_of_small hG hv
          simp only [Dm, Dset, hδh, ite_true, mem_filter, mem_univ, true_and]
          omega
        have hT2 : Sᶜ ≠ univ := fun h' => by
          rw [compl_eq_univ_iff] at h'; exact hS1.ne_empty h'
        have hmem : (Sᶜ, false) ∈ C := by
          simp only [C, cands, mem_union, mem_image, mem_filter, mem_univ, true_and]
          exact Or.inr ⟨Sᶜ, ⟨hT1, hT2, Or.inl hSD⟩, rfl⟩
        simpa [candShore] using hbest _ hmem

end

end DirectedMincut
end CutQueryComplexity
