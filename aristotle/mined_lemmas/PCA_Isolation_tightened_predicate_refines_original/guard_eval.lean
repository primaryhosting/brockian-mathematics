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
