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

theorem dioph_iff_expDioph {α : Type} {S : Set (α → ℕ)} : Dioph S ↔ ExpDioph S :=
  ⟨expDioph_of_dioph, dioph_of_expDioph⟩

/-! ## The Davis–Putnam–Robinson theorem, as a hypothesis

The remaining ingredient of the MRDP theorem is the Davis–Putnam–Robinson theorem: every
recursively enumerable set of naturals admits an exponential Diophantine representation.
This arithmetisation of computation is not available in Mathlib, so it is carried here as an
explicit hypothesis of the main theorem. -/

/-- The Davis–Putnam–Robinson theorem: every recursively enumerable predicate on `ℕ` is
exponential Diophantine (as a subset of `ℕ^Unit`). -/
