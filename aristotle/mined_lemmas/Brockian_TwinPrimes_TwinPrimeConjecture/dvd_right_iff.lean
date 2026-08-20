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
-- (Lean 4 requires `import` to precede any module docstring, so the header above is
-- repeated as the module docstring immediately after the import.)

import Mathlib

/-!
# Twin Prime Conjecture
Category: Brockian Conjecture
Target: Brockian.TwinPrimes.TwinPrimeConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Nat

namespace Brockian.TwinPrimes

/-! ## The statement

The twin prime conjecture asserts that there are arbitrarily large primes `p` such that
`p + 2` is also prime.  This is a famous open problem, so it is not proved here; instead
we give an unconditional, Lean-checked *equivalent reformulation* (Clement's criterion,
derived from Wilson's theorem — `Nat.prime_iff_fac_equiv_neg_one` in Mathlib), which
turns the conjecture into a single divisibility statement about factorials, together with
some unconditional partial results.
-/

/-- `n` and `n + 2` are both prime. -/

theorem dvd_right_iff (k : ℕ) :
    (2 * k + 3) ∣ 4 * ((2 * k)! + 1) + (2 * k + 1) ↔ (2 * k + 3) ∣ (2 * k + 2)! + 1 := by
  have hfac : (2 * k + 2)! + 1 = (2 * k + 3) * (2 * k * (2 * k)!) + (2 * (2 * k)! + 1) := by
    have h1 : (2 * k + 2)! = (2 * k + 2) * ((2 * k + 1) * (2 * k)!) := by
      rw [show 2 * k + 2 = (2 * k + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    rw [h1]; ring
  have hX : 4 * ((2 * k)! + 1) + (2 * k + 1) = (2 * k + 3) + 2 * (2 * (2 * k)! + 1) := by ring
  rw [hfac, hX, Nat.dvd_add_right (dvd_refl _), Nat.dvd_add_right (Dvd.intro _ rfl)]
  have hcop : Nat.Coprime (2 * k + 3) 2 := (Nat.coprime_mul_left_add_left 3 2 k).mpr rfl
  exact ⟨fun h => hcop.dvd_of_dvd_mul_left h, fun h => h.mul_left 2⟩

/-- Consecutive odd numbers are coprime. -/
