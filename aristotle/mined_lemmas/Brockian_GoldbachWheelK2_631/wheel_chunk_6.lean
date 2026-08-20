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

private theorem wheel_chunk_6 :
    ∀ n ∈ List.range' 380 63, ∃ p ∈ wheelPrimes631, Nat.Prime p ∧ Nat.Prime (2 * n - p) := by
  decide

