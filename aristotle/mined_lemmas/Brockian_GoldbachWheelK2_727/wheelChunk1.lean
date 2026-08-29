import Mathlib

/-!
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

namespace Brockian

/-- The Goldbach "wheel" statement with `K = 2` spokes at modulus `M`:
every even number `n` with `4 ≤ n ≤ 2 * M` is a sum of two primes. -/

private def wheelChunk1 : List ℕ := [127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281]

