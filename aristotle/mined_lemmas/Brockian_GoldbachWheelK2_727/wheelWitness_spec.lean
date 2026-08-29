/-
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header above is repeated as a plain comment at the very top of the file: Lean 4 requires
`import` commands to precede any module docstring.)
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Brockian

/-- The wheel modulus considered here. -/

lemma wheelWitness_spec : ∀ r < 727,
    4 ≤ wheelWitness r ∧ wheelWitness r ≤ 1456 ∧ wheelWitness r % 2 = 0 ∧
      wheelWitness r % 727 = r := by decide

/-- **Goldbach wheel, `K = 2`, modulus `727`.**
Every even number `n` with `4 ≤ n ≤ 2 * 727 + 2` is a sum of two primes, and moreover every
residue class modulo the wheel modulus `727` is represented by such an `n`. -/
