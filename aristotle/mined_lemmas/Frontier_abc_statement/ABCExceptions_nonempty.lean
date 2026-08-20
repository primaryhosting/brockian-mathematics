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

lemma ABCExceptions_nonempty {ε : ℝ} (hε : ε ≤ 1 / 5) : (ABCExceptions ε).Nonempty :=
  ⟨(1, 8, 9), ABCExceptions_subset hε mem_ABCExceptions_one_eight_nine⟩

/-- **The abc conjecture, stated in Lean, together with a checked reduction**: the finiteness
form of the conjecture is equivalent to the constant form.

Neither side is known (the abc conjecture is open); what is proved here is the equivalence of
the two standard formulations. Note that the constant form for `ε` follows from the finiteness
form for the *same* `ε`, while the converse uses the constant form for `ε/2`. -/
