/-
# Goldbach Wheel K 2 631
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_631
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` before any module docstring, so the header above is a plain
-- comment and is repeated below as the module docstring.)
import Mathlib

/-!
# Goldbach Wheel K 2 631
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_631
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Brockian

/-- The finite "wheel" of small primes used as the first summand. -/

def wheelPrimes631 : List Nat := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 43, 47, 73]

