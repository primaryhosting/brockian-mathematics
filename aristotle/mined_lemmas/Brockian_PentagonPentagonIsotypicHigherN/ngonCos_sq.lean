/-
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian

/-- The cosine coordinate of the `k`-th Fourier mode on the vertices of a regular `n`-gon:
`ngonCos n k j = cos (2π k j / n)`. -/

theorem ngonCos_sq (n : ℕ) (k j : ℤ) :
    ngonCos n k j ^ 2 = 1 / 2 + ngonCos n (2 * k) j / 2 := by
  have h1 : (2 * Real.pi * ((2 : ℝ) * k) * j / n) = 2 * (2 * Real.pi * k * j / n) := by ring
  simp only [ngonCos, Int.cast_mul, Int.cast_ofNat, h1, Real.cos_sq]

