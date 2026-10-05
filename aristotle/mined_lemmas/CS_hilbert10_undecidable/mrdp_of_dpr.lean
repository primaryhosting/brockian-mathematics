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

theorem mrdp_of_dpr (hDPR : DavisPutnamRobinson) (A : ℕ → Prop) (hA : REPred A) :
    ∃ (β : Type) (p : Poly (Unit ⊕ β)),
      ∀ a : ℕ, A a ↔ ∃ t : β → ℕ, p ((fun _ => a) ⊗ t) = 0 := by
  obtain ⟨β, p, hp⟩ := dioph_of_expDioph (hDPR A hA)
  exact ⟨β, p, fun a => hp (fun _ => a)⟩

/-! ## Undecidability of Hilbert's tenth problem -/

/-- The halting problem, transported along the standard numbering of partial recursive
programs: `haltsAt n` says that the `n`-th program halts on input `0`. -/
