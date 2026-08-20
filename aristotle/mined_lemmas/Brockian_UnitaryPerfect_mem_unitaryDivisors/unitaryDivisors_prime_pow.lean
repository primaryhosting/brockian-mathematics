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
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` commands to appear before any other syntax,
so the mandated header block is placed immediately after the single `import Mathlib` line.
-/

open Finset

namespace Brockian.UnitaryPerfect

/-! ## Unitary divisors and the unitary divisor sum -/

/-- The unitary divisors of `n`: the divisors `d ∣ n` with `gcd d (n / d) = 1`. -/

theorem unitaryDivisors_prime_pow {p k : ℕ} (hp : p.Prime) :
    unitaryDivisors (p ^ k) = {1, p ^ k} := by
  have hp1 : 1 < p := hp.one_lt
  ext d
  rw [mem_unitaryDivisors, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hdvd, -, hcop⟩
    obtain ⟨i, hik, rfl⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    rw [Nat.pow_div hik hp.pos] at hcop
    rcases Nat.eq_zero_or_pos i with hi | hi
    · left; simp [hi]
    · right
      have hki : k - i = 0 := by
        by_contra hne
        have hd1 : p ∣ p ^ i := dvd_pow_self p (by omega)
        have hd2 : p ∣ p ^ (k - i) := dvd_pow_self p hne
        have hone : p ∣ 1 := hcop ▸ Nat.dvd_gcd hd1 hd2
        have := Nat.le_of_dvd one_pos hone
        omega
      have hik' : i = k := by omega
      rw [hik']
  · rintro (rfl | rfl)
    · exact ⟨one_dvd _, by positivity, by simp⟩
    · refine ⟨dvd_rfl, by positivity, ?_⟩
      simp [Nat.div_self (by positivity : 0 < p ^ k)]

/-- `σ*(p ^ k) = p ^ k + 1` for a prime power with positive exponent. -/
