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
# Hyperperfect All K
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectAllK
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian.HyperperfectNumbers

/-! ## The notion of a `k`-hyperperfect number -/

/-- `IsHyperperfect k n` says that `n` is a `k`-hyperperfect number, i.e. `n > 1` and
`n = 1 + k * (σ n - n - 1)`, where `σ n` is the sum of the divisors of `n`.

The equation is written in the subtraction-free form `n + k * (n + 1) = k * σ n + 1`,
which is equivalent over `ℤ` to `n = 1 + k * (σ n - n - 1)`; this avoids the pitfalls of
truncated natural subtraction (which would make `n = 1` a spurious solution). -/

theorem certificate_of_isHyperperfect {k n : ℕ} (h : IsHyperperfect k n) :
    IsHyperperfectCertificate k n.primeFactors n.factorization := by
  have hn0 : n ≠ 0 := by rintro rfl; exact absurd h.1 (by norm_num)
  have hprimeExpo : PrimeExpo n.primeFactors n.factorization := by
    intro p hp
    exact ⟨Nat.prime_of_mem_primeFactors hp, (Nat.Prime.factorization_pos_of_dvd
      (Nat.prime_of_mem_primeFactors hp) hn0 (Nat.dvd_of_mem_primeFactors hp))⟩
  have hnum : factorNum n.primeFactors n.factorization = n :=
    Nat.factorization_prod_pow_eq_self hn0
  have hsig : factorSigma n.primeFactors n.factorization = σ 1 n := by
    rw [← sigma_factorNum hprimeExpo, hnum]
  exact ⟨hprimeExpo, by rw [hnum]; exact h.1, by rw [hnum, hsig]; exact h.2⟩

/-- **Main theorem: an equivalent, divisor-sum-free form of the Brockian hyperperfect
conjecture.**

The statement "for every `k ≥ 1` there is a `k`-hyperperfect number" is *equivalent* to the
statement "for every `k ≥ 1` there is a finite set of primes `S` with positive exponents `e`
whose associated number `n = ∏ p ^ e p` satisfies the explicit polynomial equation
`n + k * (n + 1) = k * (∏ p ∈ S, (1 + p + ⋯ + p ^ e p)) + 1`".

The right-hand side mentions no divisor-sum function: it is a purely multiplicative,
elementary condition on primes and exponents, which is the shape in which all known
hyperperfect numbers are produced. -/
