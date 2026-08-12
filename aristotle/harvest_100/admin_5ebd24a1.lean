import Mathlib

/-!
# A formal model of an isolation engine's predicate tightening

This file develops a small, self-contained formal model of the *predicate tightening*
performed by an isolation engine (`PCA.Isolation`).

The engine works with *access predicates*, written in a small Boolean formula language
over atomic checks (`PCA.Isolation.Formula`).  A concrete request is modelled as a
valuation `s : ℕ → Bool` of the atomic checks.

The engine additionally knows a finite set of *isolation facts* `K : Facts`, i.e. atomic
checks whose value is fixed by the isolation context (a sandbox domain, a capability set,
a label, ...).  A request is *admissible* for that context when it agrees with all the
facts (`PCA.Isolation.Consistent`).

Given a predicate `f`, the engine produces the *tightened predicate*
`PCA.Isolation.tighten K f`, obtained by conjoining an explicit guard for the isolation
context with the context-directed simplification of `f`.

The main result, `PCA.Isolation.tightened_predicate_refines_original`, states the
soundness *and* completeness of this construction:

  `(tighten K f).eval s = true ↔ (Consistent K s ∧ f.eval s = true)`

so the tightened predicate accepts exactly the admissible requests accepted by the
original predicate: it never accepts more than the original (soundness / refinement) and
never rejects an admissible request the original would accept (completeness).
-/

set_option maxHeartbeats 1000000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA.Isolation

/-- Access predicates of the isolation engine: Boolean combinations of atomic checks,
atomic checks being indexed by natural numbers. -/
inductive Formula : Type
  | tt : Formula
  | ff : Formula
  | atom : ℕ → Formula
  | neg : Formula → Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula
  deriving DecidableEq, Repr

/-- Evaluation of an access predicate at a request `s`, which assigns a Boolean value to
each atomic check. -/
def Formula.eval : Formula → (ℕ → Bool) → Bool
  | .tt, _ => true
  | .ff, _ => false
  | .atom i, s => s i
  | .neg p, s => !(p.eval s)
  | .conj p q, s => (p.eval s) && (q.eval s)
  | .disj p q, s => (p.eval s) || (q.eval s)

/-- The isolation facts known to the engine: a finite list of atomic checks together with
the value they are forced to take in the current isolation context. -/
abbrev Facts : Type := List (ℕ × Bool)

/-- A request `s` is admissible for the isolation context `K` when it agrees with every
known isolation fact. -/
def Consistent (K : Facts) (s : ℕ → Bool) : Prop := ∀ p ∈ K, s p.1 = p.2

instance (K : Facts) (s : ℕ → Bool) : Decidable (Consistent K s) := by
  unfold Consistent; infer_instance

/-! ### Smart constructors -/

/-- Negation with constant folding. -/
def smartNeg : Formula → Formula
  | .tt => .ff
  | .ff => .tt
  | p => .neg p

/-- Conjunction with constant folding. -/
def smartConj : Formula → Formula → Formula
  | .ff, _ => .ff
  | _, .ff => .ff
  | .tt, q => q
  | p, .tt => p
  | p, q => .conj p q

/-- Disjunction with constant folding. -/
def smartDisj : Formula → Formula → Formula
  | .tt, _ => .tt
  | _, .tt => .tt
  | .ff, q => q
  | p, .ff => p
  | p, q => .disj p q

@[simp] theorem smartNeg_eval (p : Formula) (s : ℕ → Bool) :
    (smartNeg p).eval s = !(p.eval s) := by
  cases p <;> simp [smartNeg, Formula.eval]

@[simp] theorem smartConj_eval (p q : Formula) (s : ℕ → Bool) :
    (smartConj p q).eval s = (p.eval s && q.eval s) := by
  cases p <;> cases q <;> simp [smartConj, Formula.eval]

@[simp] theorem smartDisj_eval (p q : Formula) (s : ℕ → Bool) :
    (smartDisj p q).eval s = (p.eval s || q.eval s) := by
  cases p <;> cases q <;> simp [smartDisj, Formula.eval]

/-! ### Context-directed simplification -/

/-- Simplification of a predicate under the isolation facts `K`: every atomic check whose
value is fixed by the context is replaced by the corresponding constant, and the result is
folded using the smart constructors. -/
def simplify (K : Facts) : Formula → Formula
  | .tt => .tt
  | .ff => .ff
  | .atom i =>
      match K.lookup i with
      | some true => .tt
      | some false => .ff
      | none => .atom i
  | .neg p => smartNeg (simplify K p)
  | .conj p q => smartConj (simplify K p) (simplify K q)
  | .disj p q => smartDisj (simplify K p) (simplify K q)

/-- The explicit guard describing the isolation context `K`: the conjunction of one
literal per known isolation fact. -/
def guard : Facts → Formula
  | [] => .tt
  | p :: K => Formula.conj (if p.2 then .atom p.1 else .neg (.atom p.1)) (guard K)

/-- The tightened predicate produced by the isolation engine: the guard of the isolation
context conjoined with the context-directed simplification of the original predicate. -/
def tighten (K : Facts) (f : Formula) : Formula := Formula.conj (guard K) (simplify K f)

/-! ### Auxiliary facts -/

theorem lookup_mem : ∀ (K : Facts) (i : ℕ) (b : Bool), K.lookup i = some b → (i, b) ∈ K := by
  intro K
  induction K with
  | nil => intro i b h; simp [List.lookup] at h
  | cons p K ih =>
    intro i b h
    rw [List.lookup_cons] at h
    by_cases hp : i == p.1
    · simp only [hp, Option.some.injEq] at h
      subst h
      have : i = p.1 := by simpa using hp
      subst this
      simp
    · simp only [hp] at h
      exact List.mem_cons_of_mem _ (ih i b h)

/-- On admissible requests, a fixed atomic check indeed takes the value recorded in the
isolation context. -/
theorem Consistent.lookup {K : Facts} {s : ℕ → Bool} (hs : Consistent K s) {i : ℕ}
    {b : Bool} (h : K.lookup i = some b) : s i = b :=
  hs (i, b) (lookup_mem K i b h)

/-- The guard of an isolation context accepts exactly the admissible requests. -/
theorem guard_eval (K : Facts) (s : ℕ → Bool) :
    (guard K).eval s = true ↔ Consistent K s := by
  induction K with
  | nil => simp [guard, Formula.eval, Consistent]
  | cons p K ih =>
    constructor
    · intro h
      rw [guard, Formula.eval, Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · cases hb : q.2 <;> rw [hb] at h1 <;> simp [Formula.eval] at h1 ⊢ <;> simpa using h1
      · exact ih.mp h2 q hq
    · intro h
      rw [guard, Formula.eval, Bool.and_eq_true]
      refine ⟨?_, ih.mpr fun q hq => h q (List.mem_cons_of_mem _ hq)⟩
      have hp : s p.1 = p.2 := h p List.mem_cons_self
      cases hb : p.2 <;> simp [Formula.eval, hp, hb]

/-- **Correctness of the context-directed simplification**: on admissible requests the
simplified predicate agrees with the original one. -/
theorem simplify_eval {K : Facts} {s : ℕ → Bool} (hs : Consistent K s) (f : Formula) :
    (simplify K f).eval s = f.eval s := by
  induction f with
  | tt => rfl
  | ff => rfl
  | atom i =>
    rw [simplify]
    cases h : K.lookup i with
    | none => simp [Formula.eval]
    | some b =>
      have hb := hs.lookup h
      cases b <;> simp [Formula.eval, hb]
  | neg p ih => simp [simplify, Formula.eval, ih]
  | conj p q ihp ihq => simp [simplify, Formula.eval, ihp, ihq]
  | disj p q ihp ihq => simp [simplify, Formula.eval, ihp, ihq]

/-! ### Soundness and completeness of the isolation engine's model -/

/-- **Main theorem: the tightened predicate refines the original one.**

The predicate produced by the isolation engine accepts a request exactly when the request
is admissible for the isolation context *and* is accepted by the original predicate.

The forward implication is *soundness* (the tightened predicate never grants an access the
original predicate would deny, nor one that violates the isolation context); the backward
implication is *completeness* (no admissible access granted by the original predicate is
lost by tightening). -/
theorem tightened_predicate_refines_original (K : Facts) (f : Formula) (s : ℕ → Bool) :
    (tighten K f).eval s = true ↔ (Consistent K s ∧ f.eval s = true) := by
  rw [tighten, Formula.eval, Bool.and_eq_true]
  constructor
  · rintro ⟨hg, hf⟩
    have hs : Consistent K s := (guard_eval K s).mp hg
    exact ⟨hs, by rwa [simplify_eval hs f] at hf⟩
  · rintro ⟨hs, hf⟩
    exact ⟨(guard_eval K s).mpr hs, by rwa [simplify_eval hs f]⟩

/-- Soundness: every request accepted by the tightened predicate is accepted by the
original predicate. -/
theorem tighten_sound (K : Facts) (f : Formula) (s : ℕ → Bool)
    (h : (tighten K f).eval s = true) : f.eval s = true :=
  ((tightened_predicate_refines_original K f s).mp h).2

/-- Isolation: every request accepted by the tightened predicate is admissible for the
isolation context. -/
theorem tighten_isolated (K : Facts) (f : Formula) (s : ℕ → Bool)
    (h : (tighten K f).eval s = true) : Consistent K s :=
  ((tightened_predicate_refines_original K f s).mp h).1

/-- Completeness: on admissible requests, tightening loses nothing. -/
theorem tighten_complete (K : Facts) (f : Formula) (s : ℕ → Bool) (hs : Consistent K s)
    (h : f.eval s = true) : (tighten K f).eval s = true :=
  (tightened_predicate_refines_original K f s).mpr ⟨hs, h⟩

/-- On admissible requests, the tightened predicate and the original predicate are
extensionally equal. -/
theorem tighten_eval_of_consistent {K : Facts} {s : ℕ → Bool} (hs : Consistent K s)
    (f : Formula) : (tighten K f).eval s = f.eval s := by
  by_cases h : f.eval s = true
  · simp [tighten_complete K f s hs h, h]
  · simp only [Bool.not_eq_true] at h
    have : ¬ (tighten K f).eval s = true := fun hc => by
      simp [tighten_sound K f s hc] at h
    simpa [h] using this

/-- Tightening is idempotent up to semantics. -/
theorem tighten_idempotent (K : Facts) (f : Formula) (s : ℕ → Bool) :
    (tighten K (tighten K f)).eval s = (tighten K f).eval s := by
  by_cases hs : Consistent K s
  · exact tighten_eval_of_consistent hs _
  · have h1 : ¬ (tighten K (tighten K f)).eval s = true := fun hc => hs (tighten_isolated _ _ _ hc)
    have h2 : ¬ (tighten K f).eval s = true := fun hc => hs (tighten_isolated _ _ _ hc)
    simp only [Bool.not_eq_true] at h1 h2
    rw [h1, h2]

/-- Tightening is monotone: strengthening the original predicate strengthens the tightened
one. -/
theorem tighten_monotone (K : Facts) (f g : Formula)
    (h : ∀ s : ℕ → Bool, f.eval s = true → g.eval s = true) (s : ℕ → Bool)
    (hf : (tighten K f).eval s = true) : (tighten K g).eval s = true := by
  obtain ⟨hs, hfs⟩ := (tightened_predicate_refines_original K f s).mp hf
  exact tighten_complete K g s hs (h s hfs)

/-- The tightened predicate is the *strongest* refinement of `f` that is implied by no
information beyond the isolation context: any predicate `g` that both refines `f` and only
accepts admissible requests is refined by `tighten K f`. -/
theorem tighten_greatest (K : Facts) (f g : Formula)
    (hgf : ∀ s : ℕ → Bool, g.eval s = true → f.eval s = true)
    (hgi : ∀ s : ℕ → Bool, g.eval s = true → Consistent K s) (s : ℕ → Bool)
    (hg : g.eval s = true) : (tighten K f).eval s = true :=
  tighten_complete K f s (hgi s hg) (hgf s hg)

/-! ### Sanity checks: the model is not degenerate -/

/-- A request violating the isolation context is rejected by the tightened predicate even
though the original predicate accepts it. -/
example :
    (Formula.atom 1).eval (fun _ => true) = true ∧
    (tighten [(0, false)] (Formula.atom 1)).eval (fun _ => true) = false := by
  decide

/-- A request admissible for the isolation context is treated identically by the original
and the tightened predicate. -/
example :
    (tighten [(0, false)] (Formula.disj (Formula.atom 0) (Formula.atom 1))).eval
      (fun i => decide (i = 1)) = true := by
  decide

end PCA.Isolation

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

