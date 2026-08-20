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

lemma ngonMode_disjoint {n k l : ℕ}
    (h : Real.cos (2 * π * k / n) ≠ Real.cos (2 * π * l / n)) :
    ngonMode n k ⊓ ngonMode n l = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr ?_
  rintro f ⟨hk, hl⟩
  funext j
  have h1 := ngonMode_three_term f hk (j - 1)
  have h2 := ngonMode_three_term f hl (j - 1)
  have e1 : j - 1 + 1 = j := by ring
  have e2 : j - 1 + 2 = j + 1 := by ring
  rw [e1, e2] at h1 h2
  have h3 : 2 * (Real.cos (2 * π * k / n) - Real.cos (2 * π * l / n)) * f j = 0 := by
    have := h1.symm.trans h2
    linarith [this]
  have h4 : Real.cos (2 * π * k / n) - Real.cos (2 * π * l / n) ≠ 0 := sub_ne_zero.mpr h
  have := mul_eq_zero.mp h3
  rcases this with h5 | h5
  · exact absurd h5 (by simpa using mul_ne_zero two_ne_zero h4)
  · simpa using h5

/-! ## Two-dimensionality of a nondegenerate mode -/

