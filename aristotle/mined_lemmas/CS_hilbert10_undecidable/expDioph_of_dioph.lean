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

theorem expDioph_of_dioph {α : Type} {S : Set (α → ℕ)} (h : Dioph S) : ExpDioph S := by
  obtain ⟨β, p, hp⟩ := h
  obtain ⟨e, f, hef⟩ := exists_expPoly_sub p
  refine ⟨β, e, f, fun v => (hp v).trans ⟨?_, ?_⟩⟩ <;> rintro ⟨t, ht⟩ <;>
    exact ⟨t, by have := hef (v ⊗ t); omega⟩

/-- **Matiyasevic's theorem**: a set of tuples of naturals is Diophantine if and only if it is
exponential Diophantine. -/
