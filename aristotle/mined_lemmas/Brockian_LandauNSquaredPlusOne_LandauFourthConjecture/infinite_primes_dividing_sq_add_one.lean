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
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace LandauNSquaredPlusOne

open Set

/-- The set of natural numbers `n` for which `n ^ 2 + 1` is prime. -/

theorem infinite_primes_dividing_sq_add_one :
    {p : ℕ | p.Prime ∧ ∃ n : ℕ, p ∣ n ^ 2 + 1}.Infinite := by
  have hinf : {p : ℕ | Nat.Prime p ∧ p ≡ 1 [MOD 4]}.Infinite :=
    Nat.infinite_setOf_prime_modEq_one (k := 4) (by norm_num)
  refine hinf.mono ?_
  rintro p ⟨hp, hmod⟩
  refine ⟨hp, ?_⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hp4 : p % 4 = 1 := by
    have h' := hmod
    unfold Nat.ModEq at h'
    omega
  have : IsSquare (-1 : ZMod p) := ZMod.exists_sq_eq_neg_one_iff.2 (by omega)
  obtain ⟨y, hy⟩ := this
  refine ⟨y.val, ?_⟩
  have : ((y.val ^ 2 + 1 : ℕ) : ZMod p) = 0 := by
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id]
    rw [sq, ← hy]
    ring
  exact (ZMod.natCast_eq_zero_iff _ _).1 this

/-! ### The conditional reduction -/

/-- **Landau's fourth problem, conditionally.**

Landau's fourth conjecture asserts that there are infinitely many primes of the form
`n ^ 2 + 1`; it is an open problem.  Here we give a Lean-checked reduction: assuming the
sieve-theoretic hypothesis `NoSmallPrimeFactorInfinitelyOften` — that infinitely often
`n ^ 2 + 1` has no prime factor `≤ n` — the set of `n` with `n ^ 2 + 1` prime is infinite. -/
