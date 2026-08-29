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

lemma rot_ang_mul (n : ℕ) (i j : ZMod n) :
    rot (ang n i) * rot (ang n j) = rot (ang n (i + j)) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [ang, rot_zero]
  · haveI : NeZero n := ⟨by omega⟩
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have key : ang n i + ang n j = ang n (i + j) + ((i.val + j.val) / n : ℕ) * (2 * Real.pi) := by
      have hd : (n : ℝ) * (((i.val + j.val) / n : ℕ) : ℝ) + (((i.val + j.val) % n : ℕ) : ℝ)
          = ((i.val : ℝ) + (j.val : ℝ)) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (Nat.div_add_mod (i.val + j.val) n)
      simp only [ang, ZMod.val_add]
      field_simp
      nlinarith [hd, Real.pi_pos]
    rw [rot_mul, key, rot_add_two_pi_mul]

