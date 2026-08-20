import Mathlib

/-!
# Sum E Mul
Category: Characters
Target: Brockian.Characters5.sum_e_mul
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/

theorem sum_e : ∑ x : ZMod 5, e x = 0 := by
  show ∑ x : ZMod 5, omega ^ x.val = 0
  have : ∑ x : ZMod 5, omega ^ x.val = ∑ k ∈ Finset.range 5, omega ^ k := rfl
  rw [this, sum_omega_pow]

