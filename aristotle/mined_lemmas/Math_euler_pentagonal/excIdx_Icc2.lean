import Mathlib
/-!
# Euler Pentagonal
Category: Pure Mathematics
Target: Math.euler_pentagonal
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

namespace Math

/-- The smallest element of a finite set of naturals (junk value `0` if empty). -/

lemma excIdx_Icc2 {m : ℕ} (hm : 1 ≤ m) : excIdx (Finset.Icc (m + 1) (2 * m)) = -(m : ℤ) := by
  have hle : m + 1 ≤ 2 * m := by omega
  have hmin : fmin (Finset.Icc (m + 1) (2 * m)) = m + 1 := fmin_Icc hle
  have hmax : fmax (Finset.Icc (m + 1) (2 * m)) = 2 * m := fmax_Icc hle
  have hcard : (Finset.Icc (m + 1) (2 * m)).card = m := by rw [Nat.card_Icc]; omega
  rw [excIdx, if_neg (by omega), hcard]

