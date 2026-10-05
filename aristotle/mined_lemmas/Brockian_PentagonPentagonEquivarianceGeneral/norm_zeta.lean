/-
# Pentagon Pentagon Equivariance General
Category: Brockian Corpus
Target: Brockian.PentagonPentagonEquivarianceGeneral
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pentagon Pentagon Equivariance General
Category: Brockian Corpus
Target: Brockian.PentagonPentagonEquivarianceGeneral
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

set_option grind.warning false

namespace Brockian

open Complex

/-! ## The regular `n`-gon and its dihedral symmetries

We realize the regular `n`-gon in the complex plane as the set of `n`-th roots of unity,
indexed by `ZMod n`.  The dihedral group `DihedralGroup n` acts on the index set `ZMod n`
combinatorially (`r i` rotates the labels by `i`, `sr i` reflects them) and on the plane `ℂ`
geometrically (`r i` is multiplication by `ζ ^ i`, `sr i` is that rotation followed by complex
conjugation).  The main theorem states that the vertex map is equivariant for these two actions,
for every `n ≥ 1`; the classical pentagon (`D₅`) statement is the special case `n = 5`.
-/

/-- The primitive `n`-th root of unity `exp (2 π i / n)`. -/

lemma norm_zeta (n : ℕ) : ‖zeta n‖ = 1 := by
  rw [zeta, Complex.norm_exp]
  norm_num [Complex.div_re]

