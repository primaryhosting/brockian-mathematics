import Mathlib

/-!
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header comment is placed directly after the single `import Mathlib` line, since Lean 4
requires `import` commands to precede all other commands, including module docstrings.)
-/

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

set_option grind.warning false

namespace Frontier

/-- The radical of a natural number: the product of its distinct prime factors. -/

lemma ABCFinitenessForm_of_small {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ ε : ℝ, 0 < ε → ε < δ → (ABCExceptions ε).Finite) : ABCFinitenessForm := by
  intro ε hε
  rcases lt_or_ge ε (δ / 2) with hlt | hge
  · exact h ε hε (by linarith)
  · exact (h (δ / 2) (by linarith) (by linarith)).subset (ABCExceptions_subset hge)

/-- Any set of triples whose last coordinate is bounded, and whose first two coordinates sum
to the last, is finite. -/
