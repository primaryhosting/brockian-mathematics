/-
# Tarski Undefinability
Category: Frontier — Set Theory
Target: Frontier.Tarski_undefinability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the
-- header above is given as a plain block comment and repeated below verbatim.)

import Mathlib

/-!
# Tarski Undefinability
Category: Frontier — Set Theory
Target: Frontier.Tarski_undefinability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Frontier

open FirstOrder Language

/-! ## The language of arithmetic -/

/-- The function symbols of the language of arithmetic: `0`, the successor `S`,
addition and multiplication. -/
inductive arithFunc : ℕ → Type
  | zero : arithFunc 0
  | succ : arithFunc 1
  | add : arithFunc 2
  | mul : arithFunc 2
  deriving DecidableEq

/-- The relation symbols of the language of arithmetic: the order relation `<`. -/
inductive arithRel : ℕ → Type
  | lt : arithRel 2
  deriving DecidableEq

/-- The first-order language of arithmetic, `(0, S, +, ·, <)`. -/

theorem Tarski_no_universal_formula :
    ¬ ∃ θ : arith.Formula (Fin 2), ∀ φ : arith.Formula (Fin 1), ∃ e : ℕ,
      ∀ n : ℕ, (θ.Realize ![e, n] ↔ φ.Realize ![n]) := by
  rintro ⟨θ, hθ⟩
  obtain ⟨e, he⟩ := hθ (diagonal θ)
  have := he e
  rw [realize_diagonal] at this
  tauto

/-! ## Truth of sentences -/

/-- A ternary relation on the natural numbers is **arithmetical** when it is the extension,
in the standard model `ℕ`, of a first-order formula of the language of arithmetic with three
free variables. -/
