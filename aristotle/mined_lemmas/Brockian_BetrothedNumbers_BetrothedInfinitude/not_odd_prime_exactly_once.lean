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
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` lines to precede any module docstring, so the header comment above is a
plain block comment and is repeated here as the module docstring.)
-/

open ArithmeticFunction

namespace Brockian.BetrothedNumbers

/-- Two positive integers `m ≠ n` are *betrothed* (a quasi-amicable pair) when the sum of the
divisors of each equals `m + n + 1`; equivalently, the sum of the divisors of each strictly
between `1` and the number itself equals the other number. -/

theorem not_odd_prime_exactly_once {m n p : ℕ} (h : Betrothed m n) (hpar : Even (m + n))
    (hp : p.Prime) (hodd : Odd p) (hdvd : p ∣ n) (hnsq : ¬ p ^ 2 ∣ n) : False := by
  obtain ⟨k, hk⟩ := hdvd
  have hcop : Nat.Coprime p k := by
    rw [hp.coprime_iff_not_dvd]
    intro hpk
    exact hnsq (by rw [hk, sq]; exact mul_dvd_mul_left p hpk)
  have heven : Even (sigma 1 n) := by
    rw [hk]; exact sigma_even_of_odd_prime_mul hp hodd hcop
  exact (Nat.not_even_iff_odd.2 (sigma_odd_of_betrothed_of_same_parity h hpar)) heven

/-- **Obstruction.** There is no Thabit-style rule producing betrothed pairs of the shape
`(A·p·q, A·r)` with `p, q, r` odd primes and `r` coprime to `A`: such a pair is never
betrothed. (Contrast with the amicable numbers, where exactly this shape yields Thabit's rule.) -/
