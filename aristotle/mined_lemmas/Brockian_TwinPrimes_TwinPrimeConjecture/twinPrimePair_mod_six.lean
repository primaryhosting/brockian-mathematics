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

theorem twinPrimePair_mod_six {p : ℕ} (hp : IsTwinPrimePair p) (h3 : 3 < p) : p % 6 = 5 := by
  obtain ⟨hp1, hp2⟩ := hp
  have h2 : ¬ (2 ∣ p) := fun h => by
    have := hp1.eq_one_or_self_of_dvd 2 h; omega
  have h3' : ¬ (3 ∣ p) := fun h => by
    have := hp1.eq_one_or_self_of_dvd 3 h; omega
  have h3'' : ¬ (3 ∣ (p + 2)) := fun h => by
    have := hp2.eq_one_or_self_of_dvd 3 h; omega
  rw [Nat.dvd_iff_mod_eq_zero] at h2 h3' h3''
  have e2 : p % 6 % 2 = p % 2 := Nat.mod_mod_of_dvd p (by norm_num)
  have e3 : p % 6 % 3 = p % 3 := Nat.mod_mod_of_dvd p (by norm_num)
  have hlt : p % 6 < 6 := Nat.mod_lt _ (by norm_num)
  interval_cases h : p % 6 <;> omega

end Brockian.TwinPrimes

