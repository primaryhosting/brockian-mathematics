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
/-!
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

/-!
# Sixth Unitary Perfect Exists

(The header block above is repeated here as a module docstring: Lean requires `import`
commands to precede any doc comment, so the file-opening header is an ordinary comment.)

Unitary divisors, the unitary divisor sum `σ*`, unitary perfect numbers, verification of the
five known unitary perfect numbers, the fact that no odd number `> 1` is unitary perfect, and
a reduction of the open "sixth unitary perfect number" problem.
-/

namespace Brockian.UnitaryPerfect

open Finset

/-- The unitary divisors of `n`: the divisors `d ∣ n` with `gcd (d, n / d) = 1`. -/

theorem unitaryDivisors_prime_pow {p k : ℕ} (hp : p.Prime) :
    unitaryDivisors (p ^ k) = {1, p ^ k} := by
  have hpk : 0 < p ^ k := pow_pos hp.pos k
  ext d
  rw [mem_unitaryDivisors, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hdvd, hcop, -⟩
    obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    rw [Nat.pow_div hi hp.pos] at hcop
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp
    · have hki : k - i = 0 := by
        by_contra hne
        have hpi : p ∣ p ^ i := dvd_pow_self p hi0.ne'
        have hpk' : p ∣ p ^ (k - i) := dvd_pow_self p hne
        exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop hpi hpk')
      right
      have : i = k := by omega
      simp [this]
  · rintro (rfl | rfl)
    · exact ⟨one_dvd _, by simp, hpk.ne'⟩
    · exact ⟨dvd_rfl, by simp [Nat.div_self hpk], hpk.ne'⟩

