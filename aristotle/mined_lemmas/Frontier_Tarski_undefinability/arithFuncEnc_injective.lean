/-!
# Tarski Undefinability
Category: Frontier — Set Theory
Target: Frontier.Tarski_undefinability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open FirstOrder Language

namespace Frontier

/-! ## The first-order language of arithmetic -/

/-- The function symbols of the language of arithmetic: `0`, `1`, `+`, `*`. -/
inductive arithFunc : ℕ → Type
  | zero : arithFunc 0
  | one : arithFunc 0
  | add : arithFunc 2
  | mul : arithFunc 2
  deriving DecidableEq

/-- The first-order language of arithmetic, with function symbols `0, 1, +, *`
and no relation symbols. -/

private theorem arithFuncEnc_injective : Function.Injective arithFuncEnc := by
  rintro ⟨_, (_ | _ | _ | _)⟩ ⟨_, (_ | _ | _ | _)⟩ h <;> simp_all [arithFuncEnc]

instance : Countable arith.Symbols := by
  have h1 : Countable (Σ l, arith.Functions l) := arithFuncEnc_injective.countable
  have h2 : Countable (Σ l, arith.Relations l) := by
    refine Function.Injective.countable (f := fun x => (nomatch x.2 : ℕ)) ?_
    rintro ⟨_, r⟩; exact nomatch r
  exact instCountableSum

/-! ## Arithmetical definability -/

/-- A set of natural numbers is *arithmetical* if it is the extension of some first-order
formula of the language of arithmetic with one free variable, interpreted in the standard
model `ℕ`. -/
