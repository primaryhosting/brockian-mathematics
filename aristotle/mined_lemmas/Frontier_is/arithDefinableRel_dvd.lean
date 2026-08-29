import Mathlib
import RequestProject.Frontier

/-!
# A concrete Gödel numbering, and non-vacuity of Tarski's undefinability theorem

`Frontier.Tarski_undefinability` is stated for an arbitrary *injective* Gödel numbering
`code : AForm → Nat`.  Here we exhibit such a numbering, so that the hypothesis of the

theorem arithDefinableRel_dvd : ArithDefinableRel (fun a b => ∃ k, b = a * k) := by
  refine ⟨.ex 2 (.eq (.var 1) (.mul (.var 0) (.var 2))), fun v => ?_⟩
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    exact ⟨k, by simpa [ATerm.eval, upd] using hk⟩
  · intro h
    obtain ⟨k, hk⟩ := h
    exact ⟨k, by simpa [ATerm.eval, upd] using hk⟩

end Frontier

/-!
# Tarski Undefinability
Category: Frontier — Set Theory
Target: Frontier.Tarski_undefinability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Frontier

/-! ## Syntax of first-order arithmetic

We work with the language of arithmetic `{0, 1, +, *, =}` interpreted in the standard model
`Nat`.  Variables are indexed by natural numbers, and an assignment is a function
`Nat → Nat`.

The development is deliberately self-contained, so that every notion occurring in the
statement of the theorem — syntax, satisfaction, definability, arithmetical truth — is
defined here explicitly.
-/

/-- Terms of the language of arithmetic. -/
inductive ATerm : Type
  | var : Nat → ATerm
  | zero : ATerm
  | one : ATerm
  | add : ATerm → ATerm → ATerm
  | mul : ATerm → ATerm → ATerm

/-- Value of a term in the standard model `Nat` under an assignment `v`. -/
