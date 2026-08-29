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
# Twin Prime Conjecture
Category: Brockian Conjecture
Target: Brockian.TwinPrimes.TwinPrimeConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Twin Prime Conjecture
Category: Brockian Conjecture
Target: Brockian.TwinPrimes.TwinPrimeConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The twin prime conjecture itself is open, so what is proved here is a
*Lean-checked reduction*: the twin prime conjecture is shown to be equivalent to
an explicit elementary congruence condition (Clement's criterion), together with
some unconditional partial results.
-/

namespace Brockian.TwinPrimes

open Nat

/-- `n` is the smaller member of a twin prime pair. -/

theorem prime_iff_dvd_factorial_pred_add_one {p : ℕ} (hp : 2 ≤ p) :
    Nat.Prime p ↔ p ∣ (p - 1)! + 1 := by
  haveI : NeZero p := ⟨by omega⟩
  rw [Nat.prime_iff_fac_equiv_neg_one (by omega : p ≠ 1), ← ZMod.natCast_eq_zero_iff]
  push_cast
  constructor
  · intro h; rw [h]; ring
  · intro h; linear_combination h

/-! ### Even `n` satisfies neither side of Clement's criterion -/

/-- For even `n ≥ 6`, `n` divides `(n-1)!`. -/
