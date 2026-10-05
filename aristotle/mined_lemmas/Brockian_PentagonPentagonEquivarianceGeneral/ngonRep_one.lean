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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

open Complex

/-- The primitive `n`-th root of unity `exp (2πi / n)`, the rotation constant of the
regular `n`-gon. -/

lemma ngonRep_one (z : ℂ) : ngonRep n (1 : DihedralGroup n) z = z := by
  show ngonRep n (DihedralGroup.r 0) z = z
  rw [ngonRep_r, neg_zero, ngonVertex_zero, one_mul]

omit [NeZero n] in
/-- The combinatorial action is a genuine action of the dihedral group. -/
