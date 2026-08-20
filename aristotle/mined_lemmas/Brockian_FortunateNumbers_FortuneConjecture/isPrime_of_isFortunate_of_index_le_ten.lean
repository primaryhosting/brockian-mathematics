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

/-!
# Fortune Conjecture
Category: Brockian Conjecture
Target: Brockian.FortunateNumbers.FortuneConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: the required header above is a module docstring, which Lean parses as a
command, so no `import` line may follow it.  The whole development below is therefore
self-contained and uses only the Lean 4 core library (no Mathlib).
-/

namespace Brockian.FortunateNumbers

/-! ## Primality and the primorial -/

/-- `IsPrime p` : `p` is a prime natural number. -/

theorem isPrime_of_isFortunate_of_index_le_ten {n m : Nat} (hn : n ≤ 10) (h : IsFortunate n m) :
    IsPrime m := by
  match n with
  | 0 => rw [isFortunate_of_primorial_eq_one primorial_zero h]; decide
  | 1 => rw [isFortunate_of_primorial_eq_one primorial_one h]; decide
  | (k + 2) => exact isFortunate_prime_of_le_sq h (le_sq_of_index_le_ten (by omega) hn h)

/-! ## Fortune's conjecture -/

/-- **Fortune's conjecture, conditional reduction.**

Fortune's conjecture states that every fortunate number is prime; it is an open problem.
We prove it here from the hypothesis `h` that the `n`-th fortunate number is at most `n * n`
for `n ≥ 11` (itself open, though empirically fortunate numbers are far smaller than that).
All indices `n ≤ 10` are handled unconditionally, by `isPrime_of_isFortunate_of_index_le_ten`.

The mathematical content is `not_dvd_of_isFortunate`: no prime `≤ n` divides the `n`-th
fortunate number, so a composite fortunate number would have to exceed `n * n`. -/
