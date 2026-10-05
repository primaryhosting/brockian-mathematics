/-
# Hilbert 10 Undecidable
Category: Frontier Cs
Target: CS.hilbert10_undecidable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hilbert 10 Undecidable
Category: Frontier Cs
Target: CS.hilbert10_undecidable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace CS

universe u

local infixr:65 " ⊗ " => Sum.elim

/-! ## Exponential polynomials

An *exponential polynomial* in variables of type `α` is built from variables and natural
number constants using addition, multiplication and exponentiation.  These are the objects
occurring in the Davis–Putnam–Robinson theorem. -/

/-- Syntax of exponential polynomials with variables in `α`. -/
inductive ExpPoly (α : Type u) : Type u
  | var : α → ExpPoly α
  | const : ℕ → ExpPoly α
  | add : ExpPoly α → ExpPoly α → ExpPoly α
  | mul : ExpPoly α → ExpPoly α → ExpPoly α
  | pow : ExpPoly α → ExpPoly α → ExpPoly α

/-- Evaluation of an exponential polynomial at a valuation `v : α → ℕ`. -/

theorem diophFn_expPoly_eval {α : Type} (p : ExpPoly α) :
    Dioph.DiophFn (fun v : α → ℕ => p.eval v) := by
  induction p with
  | var i => exact Dioph.proj_dioph i
  | const n => exact Dioph.const_dioph n
  | add p q hp hq => exact Dioph.add_dioph hp hq
  | mul p q hp hq => exact Dioph.mul_dioph hp hq
  | pow p q hp hq => exact Dioph.pow_dioph hp hq

/-- **Exponentiation can be eliminated**: every exponential Diophantine set is Diophantine.
This is the Diophantine-representation half of Matiyasevic's contribution to the MRDP
theorem, obtained here from `Dioph.pow_dioph`. -/
