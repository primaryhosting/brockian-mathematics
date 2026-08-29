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

lemma goldbachB_all : ∀ n < 1457, 4 ≤ n → n % 2 = 0 → goldbachB n = true := by decide

/-- Wheel witness: for a residue `r < 727`, an even number in the verified range whose
residue modulo `727` is `r`. -/
