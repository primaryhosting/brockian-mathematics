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

lemma ngonVertex_injective : Function.Injective (ngonVertex n) := by
  intro a b hab
  have h := isPrimitiveRoot_ngonRoot.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) hab
  have := congrArg (fun m : ℕ => (m : ZMod n)) h
  simpa [ZMod.natCast_val, ZMod.cast_id] using this

omit [NeZero n] in
