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

lemma norm_ngonRep (g : DihedralGroup n) (z : ℂ) : ‖ngonRep n g z‖ = ‖z‖ := by
  cases g with
  | r i => rw [ngonRep_r, norm_mul, abs_ngonVertex, one_mul]
  | sr i => rw [ngonRep_sr, norm_mul, abs_ngonVertex, one_mul, RCLike.norm_conj]

end

/-- **Pentagon equivariance, general `n`-gon version.**

For every `n ≥ 1`, the assignment `ngonRep n` is an action of the dihedral group `D n` on the
complex plane by norm-preserving maps, `dihedralVertexAction n` is the corresponding action on the
vertex labels `ZMod n`, and the vertex map `ngonVertex n : ZMod n → ℂ` of the regular `n`-gon is
equivariant for these two actions.  Specialising to `n = 5` recovers the pentagon (`D₅`) statement.
-/
