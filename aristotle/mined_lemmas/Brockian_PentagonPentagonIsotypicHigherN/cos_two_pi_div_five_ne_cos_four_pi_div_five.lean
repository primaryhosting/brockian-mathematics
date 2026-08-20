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

lemma cos_two_pi_div_five_ne_cos_four_pi_div_five :
    Real.cos (2 * π * (1 : ℕ) / (5 : ℕ)) ≠ Real.cos (2 * π * (2 : ℕ) / (5 : ℕ)) := by
  have hlt : Real.cos (2 * π * (2 : ℕ) / (5 : ℕ)) < Real.cos (2 * π * (1 : ℕ) / (5 : ℕ)) := by
    refine Real.cos_lt_cos_of_nonneg_of_le_pi ?_ ?_ ?_
    · push_cast; positivity
    · push_cast; nlinarith [Real.pi_pos]
    · push_cast; nlinarith [Real.pi_pos]
  exact ne_of_gt hlt

/-! ## Main theorem -/

/--
**Pentagon isotypic components, generalized to higher `n`.**

For every `n`-gon (`0 < n`) and every mode index `k`:

* the mode subspace `ngonMode n k` (spanned by `j ↦ cos (2πkj/n)` and `j ↦ sin (2πkj/n)`)
  is invariant under the rotation `j ↦ j + 1` and the reflection `j ↦ -j`, i.e. it is a
  subrepresentation of the dihedral group of the `n`-gon;
* every element of it is `n`-periodic, i.e. is a genuine function on the vertices of
  the `n`-gon;
* whenever `sin (2πk/n) ≠ 0`, the two generating modes are linearly independent and the
  mode subspace is exactly two-dimensional;
* two mode subspaces with `cos (2πk/n) ≠ cos (2πl/n)` intersect trivially.

Specializing to the pentagon `n = 5`, the modes `k = 1, 2` give the two two-dimensional
isotypic components of the vertex representation of the dihedral group `D 5`.
-/
