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

private theorem arg_sub (n : ℕ) (k l j : ℤ) :
    (2 * Real.pi * ((k : ℝ) - l) * j / n)
      = 2 * Real.pi * k * j / n - 2 * Real.pi * l * j / n := by ring

