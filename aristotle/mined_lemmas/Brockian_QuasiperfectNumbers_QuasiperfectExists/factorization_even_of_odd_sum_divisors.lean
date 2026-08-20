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
# Quasiperfect Exists
Category: Brockian Conjecture
Target: Brockian.QuasiperfectNumbers.QuasiperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace QuasiperfectNumbers

open Finset

/-- A positive natural number `n` is *quasiperfect* if the sum of all of its divisors is
`2 * n + 1`, equivalently if the sum of its proper divisors is `n + 1`.

Whether a quasiperfect number exists is a longstanding open problem; no example is known,
and none can be small (see `no_quasiperfect_lt_500`). -/

theorem factorization_even_of_odd_sum_divisors {n : ℕ} (hn : n ≠ 0)
    (h : Odd (∑ d ∈ n.divisors, d)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Even (n.factorization p) := by
  by_contra hodd
  have hmem : p ∈ n.primeFactors := by
    rw [Nat.mem_primeFactors]
    refine ⟨hp, ?_, hn⟩
    by_contra hdvd
    exact hodd (by simp [Nat.factorization_eq_zero_of_not_dvd hdvd])
  set f : ℕ → ZMod 2 := fun m => ((∑ d ∈ m.divisors, d : ℕ) : ZMod 2) with hf
  have hkey : f n = n.factorization.prod fun q k => f (q ^ k) := by
    refine Nat.multiplicative_factorization f (fun x y hxy => ?_) (by simp [hf]) hn
    show ((∑ d ∈ (x * y).divisors, d : ℕ) : ZMod 2) = _
    rw [sum_divisors_mul_of_coprime hxy, Nat.cast_mul]
  have hzero : f (p ^ n.factorization p) = 0 := by
    have h1 : ¬ Odd (∑ d ∈ (p ^ n.factorization p).divisors, d) := by
      rw [odd_sum_divisors_prime_pow_iff hp hp2]
      exact hodd
    exact ZMod.natCast_eq_zero_iff_even.2 (Nat.not_odd_iff_even.1 h1)
  have hfn : f n = 0 := by
    rw [hkey]
    exact Finset.prod_eq_zero (by simpa [Nat.support_factorization] using hmem) hzero
  have hfn' : ((∑ d ∈ n.divisors, d : ℕ) : ZMod 2) = 0 := hfn
  rw [(natCast_zmod_two_eq_one_iff _).2 h] at hfn'
  exact one_ne_zero hfn'

/-- A positive natural number all of whose prime exponents are even is a square. -/
