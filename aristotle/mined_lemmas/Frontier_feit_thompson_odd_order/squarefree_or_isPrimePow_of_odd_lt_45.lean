import Mathlib

/-!
# Feit Thompson Odd Order
Category: Frontier Abel
Target: Frontier.feit_thompson_odd_order
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

universe u

/-! ## Unconditional base cases -/

/-- A finite group whose order is squarefree is solvable (it is a Z-group). -/

theorem squarefree_or_isPrimePow_of_odd_lt_45 :
    ∀ n < 45, Odd n → Squarefree n ∨ IsPrimePow n := by decide +kernel

/-- **Base case of Feit–Thompson**: every finite group of odd order less than `45` is
solvable.  (Unconditional: `45 = 3 ^ 2 * 5` is the smallest odd number that is neither
squarefree nor a prime power.) -/
