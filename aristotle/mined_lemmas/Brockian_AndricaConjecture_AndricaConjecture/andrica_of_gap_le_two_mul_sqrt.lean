import Mathlib

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

/-
# Andrica Conjecture
Category: Brockian Conjecture
Target: Brockian.AndricaConjecture.AndricaConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Andrica Conjecture
Category: Brockian Conjecture
Target: Brockian.AndricaConjecture.AndricaConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.AndricaConjecture

open Real

/-- `primeSeq n` is the `n`-th prime number (`primeSeq 0 = 2`). -/

theorem andrica_of_gap_le_two_mul_sqrt (n : ℕ)
    (hgap : (primeSeq (n + 1) : ℝ) - primeSeq n ≤ 2 * Real.sqrt (primeSeq n)) :
    Real.sqrt (primeSeq (n + 1)) - Real.sqrt (primeSeq n) < 1 :=
  (sqrt_sub_sqrt_lt_one_iff (a := (primeSeq n : ℝ)) (b := (primeSeq (n + 1) : ℝ))
    (Nat.cast_nonneg _)).2 (by linarith)

end Brockian.AndricaConjecture

