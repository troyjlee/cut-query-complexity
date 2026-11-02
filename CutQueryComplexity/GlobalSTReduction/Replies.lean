import CutQueryComplexity.GlobalSTReduction.Specification
import CutQueryComplexity.GHReduction.Randomized.CallOps

/-! # Call programs under arbitrary admissible replies

The existing call language (`GHReduction.Randomized.CallProg`) was analysed with
one ideal reply per call: the canonical (inclusion-minimal) shore. Here a call
may receive *any* reply allowed by a `ReplyRule`:

* `anyReply`: every shore;
* `optReply G`: every minimum s-t shore of the contracted graph `G.contract π`.

`Holds read ok post p` says that every run of `p` whose cut queries are answered
by `read` and whose call replies satisfy `ok` returns an output satisfying
`post`. Replies are chosen per call occurrence, so two calls on the same
instance may receive different minimum shores.

`Within wq wc p c` says that along every run, for all query answers and all
replies, the charge is at most `c`, where a cut query weighs `wq` and a call on
`k` vertices weighs `wc k`. `Within 1 Q` is the charged query cost of
`CallProg.compile Q`; `Within 0 (fun _ => 1)` counts calls.

Both predicates are proved compositionally: `bind`, `map`, tables and public
contractions.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GlobalSTReduction
noncomputable section
open scoped Classical BigOperators
open WeightedGraph GHReduction GHReduction.Randomized

/-- Which replies a call on `k` vertices along `π` with terminals `s`, `t` may receive. -/
abbrev ReplyRule (V : Type) : Type :=
  (k : ℕ) → (V → Fin k) → Fin k → Fin k → Finset (Fin k) → Prop

/-- Every reply is admissible. -/
def anyReply (V : Type) : ReplyRule V := fun _ _ _ _ _ => True

/-- The admissible replies are the minimum s-t shores of the contracted graph. -/
def optReply {V : Type} [Fintype V] [DecidableEq V] (G : WeightedGraph V) : ReplyRule V :=
  fun _ π s t S => IsSTMinCut (G.contract π) s t S

variable {V W : Type} {α β : Type}

/-- Every run with queries answered by `read` and admissible replies satisfies `post`. -/
def Holds (read : Finset V → ℝ) (ok : ReplyRule V) (post : α → Prop) : CallProg V α → Prop
  | .pure a => post a
  | .query S next => Holds read ok post (next (read S))
  | .call k π s t _ next => ∀ S, ok k π s t S → Holds read ok post (next S)

/-- Along every run, for all answers and replies, the charge is at most `c`. -/
def Within (wq : ℕ) (wc : ℕ → ℕ) : CallProg V α → ℕ → Prop
  | .pure _, _ => True
  | .query _ next, c => wq ≤ c ∧ ∀ x, Within wq wc (next x) (c - wq)
  | .call k _ _ _ _ next, c => wc k ≤ c ∧ ∀ S, Within wq wc (next S) (c - wc k)

/-- Charged query cost of `CallProg.compile Q`: one per cut query, `Q k` per call. -/
abbrev CostWithin (Q : ℕ → ℕ) (p : CallProg V α) (c : ℕ) : Prop := Within 1 Q p c

/-- Number of s-t calls. -/
abbrev CallsWithin (p : CallProg V α) (c : ℕ) : Prop := Within 0 (fun _ => 1) p c

/-! ### `Holds` -/

section Holds

variable {read : Finset V → ℝ} {ok : ReplyRule V}

@[simp] theorem holds_pure (post : α → Prop) (a : α) :
    Holds read ok post (CallProg.pure a : CallProg V α) ↔ post a := Iff.rfl

theorem Holds.mono {post post' : α → Prop} {p : CallProg V α} (h : Holds read ok post p)
    (hpost : ∀ a, post a → post' a) : Holds read ok post' p := by
  induction p with
  | pure a => exact hpost a h
  | query S next ih => exact ih _ h
  | call k π s t hst next ih => exact fun S hS => ih S (h S hS)

/-- Shrinking the admissible replies keeps a guarantee. -/
theorem Holds.mono_ok {ok' : ReplyRule V} {post : α → Prop} {p : CallProg V α}
    (h : Holds read ok post p) (hok : ∀ k π s t S, ok' k π s t S → ok k π s t S) :
    Holds read ok' post p := by
  induction p with
  | pure a => exact h
  | query S next ih => exact ih _ h
  | call k π s t hst next ih => exact fun S hS => ih S (h S (hok k π s t S hS))

theorem holds_and {post post' : α → Prop} {p : CallProg V α} (h : Holds read ok post p)
    (h' : Holds read ok post' p) : Holds read ok (fun a => post a ∧ post' a) p := by
  induction p with
  | pure a => exact ⟨h, h'⟩
  | query S next ih => exact ih _ h h'
  | call k π s t hst next ih => exact fun S hS => ih S (h S hS) (h' S hS)

theorem holds_true (p : CallProg V α) : Holds read ok (fun _ => True) p := by
  induction p with
  | pure a => trivial
  | query S next ih => exact ih _
  | call k π s t hst next ih => exact fun S _ => ih S

theorem holds_bind {post : β → Prop} (p : CallProg V α) (f : α → CallProg V β) :
    Holds read ok post (p.bind f) ↔ Holds read ok (fun a => Holds read ok post (f a)) p := by
  induction p with
  | pure a => exact Iff.rfl
  | query S next ih => exact ih _
  | call k π s t hst next ih => exact forall_congr' (fun S => imp_congr_right (fun _ => ih S))

theorem holds_map {post : β → Prop} (f : α → β) (p : CallProg V α) :
    Holds read ok post (p.map f) ↔ Holds read ok (fun a => post (f a)) p :=
  holds_bind p _

@[simp] theorem holds_ask {post : ℝ → Prop} (S : Finset V) :
    Holds read ok post (CallProg.ask S) ↔ post (read S) := Iff.rfl

theorem holds_tableProgram {m : ℕ} {p : Fin m → CallProg V α} {post : Fin m → α → Prop}
    (h : ∀ i, Holds read ok (post i) (p i)) :
    Holds read ok (fun f => ∀ i, post i (f i)) (CallProg.tableProgram m p) := by
  induction m with
  | zero => exact fun i => Fin.elim0 i
  | succ m ih =>
      rw [CallProg.tableProgram, holds_bind]
      refine (h 0).mono (fun o ho => ?_)
      rw [holds_map]
      refine (ih (p := fun i => p i.succ) (post := fun i => post i.succ)
        (fun i => h i.succ)).mono (fun g hg i => ?_)
      cases i using Fin.cases with
      | zero => exact ho
      | succ i => exact hg i

theorem holds_finiteTable {D : Type} [Fintype D] {p : D → CallProg V α} {post : D → α → Prop}
    (h : ∀ x, Holds read ok (post x) (p x)) :
    Holds read ok (fun f => ∀ x, post x (f x)) (CallProg.finiteTable p) := by
  rw [CallProg.finiteTable, holds_map]
  refine (holds_tableProgram (post := fun i => post ((Fintype.equivFin D).symm i))
    (fun i => h _)).mono (fun f hf x => ?_)
  simpa using hf ((Fintype.equivFin D) x)

end Holds

/-- A guarantee on the contracted instance transfers to the pulled-back program,
provided the replies admitted on `V` along `π ∘ f` are admitted on `W` along `π`. -/
theorem holds_contract [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {read : Finset V → ℝ} {okV : ReplyRule V} {okW : ReplyRule W} {post : α → Prop}
    (f : V → W) (hok : ∀ k π s t S, okV k (fun v => π (f v)) s t S → okW k π s t S)
    {p : CallProg W α} (h : Holds (fun S => read (pull f S)) okW post p) :
    Holds read okV post (CallProg.contract f p) := by
  induction p with
  | pure a => exact h
  | query S next ih => exact ih _ h
  | call k π s t hst next ih => exact fun S hS => ih S (h S (hok k π s t S hS))

/-- Minimum replies along `π ∘ f` are minimum replies on the contracted graph. -/
theorem optReply_contract [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : WeightedGraph V) (f : V → W) :
    ∀ k (π : W → Fin k) s t S, optReply G k (fun v => π (f v)) s t S →
      optReply (G.contract f) k π s t S := by
  intro k π s t S h
  simpa only [optReply, contract_contract] using h

/-- The oracle of the contracted graph is the original oracle on pulled-back sets. -/
theorem cut_contract_fun [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : WeightedGraph V) (f : V → W) :
    (fun S => G.cut (pull f S)) = (G.contract f).cut :=
  funext (fun S => (cut_contract G f S).symm)

/-- `holds_contract` for minimum replies on a graph. -/
theorem holds_contract_opt [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : WeightedGraph V) (f : V → W) {post : α → Prop} {p : CallProg W α}
    (h : Holds (G.contract f).cut (optReply (G.contract f)) post p) :
    Holds G.cut (optReply G) post (CallProg.contract f p) := by
  apply holds_contract f (optReply_contract G f)
  rwa [cut_contract_fun]

/-- `holds_contract` for arbitrary replies. -/
theorem holds_contract_any [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {read : Finset V → ℝ} (f : V → W) {post : α → Prop} {p : CallProg W α}
    (h : Holds (fun S => read (pull f S)) (anyReply W) post p) :
    Holds read (anyReply V) post (CallProg.contract f p) :=
  holds_contract f (fun _ _ _ _ _ _ => trivial) h

/-- A minimum reply to the compactly relabeled call is a minimum s-t shore of `H`. -/
theorem holds_canonicalCall [Fintype W] [DecidableEq W] (H : WeightedGraph W) {s t : W}
    (hst : s ≠ t) :
    Holds H.cut (optReply H) (fun S => IsSTMinCut H s t S) (CallProg.canonicalCall s t hst) :=
  fun _ hS => stMinCut_equiv_pull H (Fintype.equivFin W) hS

/-! ### `Within` -/

section Within

variable {wq : ℕ} {wc : ℕ → ℕ}

@[simp] theorem within_pure (a : α) (c : ℕ) : Within wq wc (CallProg.pure a : CallProg V α) c :=
  trivial

theorem Within.mono {p : CallProg V α} {c c' : ℕ} (h : Within wq wc p c) (hc : c ≤ c') :
    Within wq wc p c' := by
  induction p generalizing c c' with
  | pure a => trivial
  | query S next ih => exact ⟨h.1.trans hc, fun x => ih x (h.2 x) (by omega)⟩
  | call k π s t hst next ih => exact ⟨h.1.trans hc, fun S => ih S (h.2 S) (by omega)⟩

theorem within_bind {p : CallProg V α} {f : α → CallProg V β} {c₁ c₂ : ℕ}
    (hp : Within wq wc p c₁) (hf : ∀ a, Within wq wc (f a) c₂) :
    Within wq wc (p.bind f) (c₁ + c₂) := by
  induction p generalizing c₁ with
  | pure a => exact (hf a).mono (Nat.le_add_left _ _)
  | query S next ih =>
      refine ⟨hp.1.trans (Nat.le_add_right _ _), fun x => (ih x (hp.2 x)).mono ?_⟩
      have := hp.1
      omega
  | call k π s t hst next ih =>
      refine ⟨hp.1.trans (Nat.le_add_right _ _), fun S => (ih S (hp.2 S)).mono ?_⟩
      have := hp.1
      omega

theorem within_map {p : CallProg V α} (f : α → β) {c : ℕ} (hp : Within wq wc p c) :
    Within wq wc (p.map f) c := by
  have h := within_bind (c₂ := 0) hp (fun a => within_pure (f a) 0)
  rwa [Nat.add_zero] at h

theorem within_ask (S : Finset V) : Within wq wc (CallProg.ask S) wq :=
  ⟨le_rfl, fun _ => trivial⟩

theorem within_tableProgram {m : ℕ} {p : Fin m → CallProg V α} {c : Fin m → ℕ}
    (h : ∀ i, Within wq wc (p i) (c i)) :
    Within wq wc (CallProg.tableProgram m p) (∑ i, c i) := by
  induction m with
  | zero => trivial
  | succ m ih =>
      rw [Fin.sum_univ_succ]
      exact within_bind (h 0) (fun o => within_map _ (ih (fun i => h i.succ)))

theorem within_finiteTable {D : Type} [Fintype D] {p : D → CallProg V α} {c : D → ℕ}
    (h : ∀ x, Within wq wc (p x) (c x)) :
    Within wq wc (CallProg.finiteTable p) (∑ x, c x) := by
  have ht := within_tableProgram (p := fun i => p ((Fintype.equivFin D).symm i))
    (c := fun i => c ((Fintype.equivFin D).symm i)) (fun i => h _)
  rw [(Fintype.equivFin D).symm.sum_comp c] at ht
  exact within_map _ ht

theorem within_contract [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (f : V → W) {p : CallProg W α} {c : ℕ} (h : Within wq wc p c) :
    Within wq wc (CallProg.contract f p) c := by
  induction p generalizing c with
  | pure a => trivial
  | query S next ih => exact ⟨h.1, fun x => ih x (h.2 x)⟩
  | call k π s t hst next ih => exact ⟨h.1, fun S => ih S (h.2 S)⟩

theorem within_canonicalCall [Fintype W] [DecidableEq W] {s t : W} (hst : s ≠ t) :
    Within wq wc (CallProg.canonicalCall s t hst) (wc (Fintype.card W)) :=
  ⟨le_rfl, fun _ => trivial⟩

end Within

end
end CutQueryComplexity.GlobalSTReduction
