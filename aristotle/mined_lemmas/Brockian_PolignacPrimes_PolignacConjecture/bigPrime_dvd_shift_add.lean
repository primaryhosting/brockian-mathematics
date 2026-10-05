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

import Mathlib

/-!
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede any module docstring, so the header
-- comment above appears directly after the import.)

namespace Brockian.PolignacPrimes

open Finset

/-- `ConsecutivePrimeGap n p` says that `p` and `p + n` are primes and that there is no
prime strictly between them, i.e. `p` and `p + n` are *consecutive* primes with gap `n`. -/

lemma bigPrime_dvd_shift_add {n j : ℕ} (hj : j ∈ Finset.Ico 1 n) :
    bigPrime n j ∣ (shift n + j) := by
  have h := (shiftSub n).prop j hj
  have hj1 : 1 ≤ j := by simp at hj; omega
  have hjn : j < n := by simp at hj; omega
  have hle : j ≤ bigPrime n j := le_of_lt (lt_of_lt_of_le (lt_of_lt_of_le hjn (le_refl n))
    (le_of_lt (lt_bigPrime (n := n) (j := j) hj1)))
  have h2 : shift n + j ≡ (bigPrime n j - j) + j [MOD bigPrime n j] := h.add_right j
  rw [Nat.sub_add_cancel hle] at h2
  have h3 : shift n + j ≡ 0 [MOD bigPrime n j] := h2.trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl)
  exact Nat.modEq_zero_iff_dvd.1 h3

/-- Admissibility of the pair of forms `modulus n * x + shift n`, `modulus n * x + shift n + n`. -/
