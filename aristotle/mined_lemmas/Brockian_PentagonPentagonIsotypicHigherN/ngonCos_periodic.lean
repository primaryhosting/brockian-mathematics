/-
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-! ## Setup

We model a function on the vertices of a regular `n`-gon as a function `ℤ → ℝ` which is
`n`-periodic (the vertex labelled `j` is the vertex `j mod n`).  The dihedral group `D n`
acts by the rotation `j ↦ j + 1` and the reflection `j ↦ -j`.

The `k`-th *mode subspace* is the span of the two "Fourier" functions
`j ↦ cos (2πkj/n)` and `j ↦ sin (2πkj/n)`.  For the pentagon (`n = 5`) the modes `k = 1, 2`
are exactly the two two-dimensional isotypic components of the vertex representation of
`D 5`; the results below establish the corresponding statements for arbitrary `n`. -/

/-- The cosine Fourier mode of index `k` on the vertices of the `n`-gon. -/

lemma ngonCos_periodic {n : ℕ} (hn : 0 < n) (k : ℕ) (j : ℤ) :
    ngonCos n k (j + n) = ngonCos n k j := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have h : (2 * π * k * ((j : ℝ) + n) / n) = 2 * π * k * j / n + (k : ℝ) * (2 * π) := by
    field_simp
  simp only [ngonCos, Int.cast_add, Int.cast_natCast, h, Real.cos_add_nat_mul_two_pi]

