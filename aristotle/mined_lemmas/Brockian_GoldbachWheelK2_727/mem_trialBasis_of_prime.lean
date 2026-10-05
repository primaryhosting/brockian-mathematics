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

lemma mem_trialBasis_of_prime {m : ℕ} (hm : m.Prime) (h : m * m ≤ 1680) :
    m ∈ trialBasis := by
  have h2 := hm.two_le
  have hm40 : m ≤ 40 := by nlinarith
  interval_cases m <;> first | (exact absurd hm (by decide)) | decide

/-- Correctness of the boolean primality test in the intended range. -/
