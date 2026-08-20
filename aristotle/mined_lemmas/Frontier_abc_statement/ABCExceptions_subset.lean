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

lemma ABCExceptions_subset {ε₁ ε₂ : ℝ} (h : ε₁ ≤ ε₂) :
    ABCExceptions ε₂ ⊆ ABCExceptions ε₁ := by
  rintro ⟨a, b, c⟩ ⟨ha, hb, hab, habc, hlt⟩
  refine ⟨ha, hb, hab, habc, lt_of_le_of_lt ?_ hlt⟩
  exact Real.rpow_le_rpow_of_exponent_le (one_le_rad _) (by linarith)

/-- It suffices to prove the abc conjecture for arbitrarily small `ε`. -/
