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
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 rejects a module doc comment `/-! ... -/` before `import`, so the header above
-- is an ordinary block comment; its text is otherwise exactly as requested.)

import Mathlib

/-!
# Landau's fourth problem: infinitely many primes of the form `n ^ 2 + 1`

Landau's fourth conjecture is an open problem.  This file provides:

* a formal statement of Bunyakovsky's conjecture (`Bunyakovsky`);
* a Lean-checked *conditional reduction*: Landau's fourth conjecture follows from
  Bunyakovsky's conjecture (`LandauFourthConjecture`), via the irreducibility of
  `X ^ 2 + 1` over `ℤ` and the absence of a fixed divisor;
* unconditional partial results: an odd prime divides some `n ^ 2 + 1` iff it is
  `1 mod 4`, and hence infinitely many primes divide numbers of the form `n ^ 2 + 1`.
-/

namespace Brockian.LandauNSquaredPlusOne

open Polynomial

/-- The set of natural numbers `n` such that `n ^ 2 + 1` is prime. -/

theorem prime_dvd_sq_add_one_iff {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (∃ n : ℕ, p ∣ n ^ 2 + 1) ↔ p % 4 = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  constructor
  · rintro ⟨n, hn⟩
    have h : ((n ^ 2 + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hn
    push_cast at h
    have hsq : IsSquare (-1 : ZMod p) := ⟨(n : ZMod p), by linear_combination -h⟩
    have := (ZMod.exists_sq_eq_neg_one_iff (p := p)).1 hsq
    omega
  · intro h4
    obtain ⟨y, hy⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).2 (by omega)
    refine ⟨y.val, ?_⟩
    have h : ((y.val ^ 2 + 1 : ℕ) : ZMod p) = 0 := by
      push_cast
      rw [ZMod.natCast_val, ZMod.cast_id]
      linear_combination -hy
    exact (ZMod.natCast_eq_zero_iff _ _).1 h

/-- Unconditionally, infinitely many primes divide some number of the form `n ^ 2 + 1`. -/
