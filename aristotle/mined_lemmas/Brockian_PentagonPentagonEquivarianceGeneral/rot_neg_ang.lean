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

/-- The planar rotation matrix by an angle `t`. -/

lemma rot_neg_ang (n : ℕ) (i : ZMod n) : rot (-(ang n i)) = rot (ang n (-i)) := by
  have h1 : rot (ang n i) * rot (ang n (-i)) = 1 := by
    rw [rot_ang_mul]
    simpa using rot_ang_zero n
  have h2 : rot (-(ang n i)) * rot (ang n i) = 1 := by
    rw [rot_mul]
    simpa using rot_zero
  calc rot (-(ang n i)) = rot (-(ang n i)) * (rot (ang n i) * rot (ang n (-i))) := by
        rw [h1, mul_one]
    _ = (rot (-(ang n i)) * rot (ang n i)) * rot (ang n (-i)) := by rw [mul_assoc]
    _ = rot (ang n (-i)) := by rw [h2, one_mul]

