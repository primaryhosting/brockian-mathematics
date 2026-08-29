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

private def wheelChunk4 : List ℕ := [661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863]

