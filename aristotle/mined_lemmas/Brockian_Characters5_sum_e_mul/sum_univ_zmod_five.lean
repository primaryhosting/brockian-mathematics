-- # Sum E Mul
-- Category: Characters
-- Target: Brockian.Characters5.sum_e_mul
-- Verification: pending
-- Provenance: Aristotle theorem prover (Harmonic)

import Mathlib

/-!
# Sum E Mul
Category: Characters
Target: Brockian.Characters5.sum_e_mul
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

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/

lemma sum_univ_zmod_five (f : ZMod 5 → ℂ) :
    ∑ x : ZMod 5, f x = f 0 + f 1 + f 2 + f 3 + f 4 := by
  rw [show (Finset.univ : Finset (ZMod 5)) = {0, 1, 2, 3, 4} from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-- Additive-character orthogonality on `ZMod 5`. -/
