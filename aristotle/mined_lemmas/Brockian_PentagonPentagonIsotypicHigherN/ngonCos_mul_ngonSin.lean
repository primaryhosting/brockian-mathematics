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

theorem ngonCos_mul_ngonSin (n : ℕ) (k l j : ℤ) :
    ngonCos n k j * ngonSin n l j
      = (ngonSin n (k + l) j - ngonSin n (k - l) j) / 2 := by
  simp only [ngonCos, ngonSin, Int.cast_sub, Int.cast_add, arg_sub, arg_add,
    Real.sin_sub, Real.sin_add]
  ring

