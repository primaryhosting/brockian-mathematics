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

theorem dioph_of_expDioph {α : Type} {S : Set (α → ℕ)} (h : ExpDioph S) : Dioph S := by
  obtain ⟨β, e, f, hS⟩ := h
  have hEq : Dioph {w : α ⊕ β → ℕ | e.eval w = f.eval w} :=
    Dioph.eq_dioph (diophFn_expPoly_eval e) (diophFn_expPoly_eval f)
  exact Dioph.ext (Dioph.ex_dioph hEq) fun v => (hS v).symm

/-- Every integer polynomial is the difference of two exponential polynomials with values
in `ℕ`. -/
