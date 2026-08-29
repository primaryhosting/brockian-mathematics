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

noncomputable def dihedralRep (n : ℕ) : DihedralGroup n →* Matrix (Fin 2) (Fin 2) ℝ where
  toFun g := match g with
    | DihedralGroup.r i => rot (ang n i)
    | DihedralGroup.sr i => refl * rot (ang n i)
  map_one' := by simpa using rot_ang_zero n
  map_mul' := by
    rintro (i | i) (j | j)
    · simpa [DihedralGroup.r_mul_r] using (rot_ang_mul n i j).symm
    · show refl * rot (ang n (j - i)) = rot (ang n i) * (refl * rot (ang n j))
      rw [← mul_assoc, rot_ang_mul_refl, mul_assoc, rot_ang_mul, sub_eq_neg_add]
    · show refl * rot (ang n (i + j)) = refl * rot (ang n i) * rot (ang n j)
      rw [mul_assoc, rot_ang_mul]
    · show rot (ang n (j - i)) = refl * rot (ang n i) * (refl * rot (ang n j))
      rw [mul_assoc, ← mul_assoc (rot (ang n i)) refl, rot_ang_mul_refl, ← mul_assoc,
        ← mul_assoc, refl_mul_refl, one_mul, rot_ang_mul, sub_eq_neg_add]

