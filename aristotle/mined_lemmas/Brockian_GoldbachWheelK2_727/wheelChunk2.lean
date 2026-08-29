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

private def wheelChunk2 : List ℕ := [283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463]

