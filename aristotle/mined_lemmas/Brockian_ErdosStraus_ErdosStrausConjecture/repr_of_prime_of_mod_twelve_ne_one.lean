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
# Erdos Straus Conjecture
Category: Brockian Conjecture
Target: Brockian.ErdosStraus.ErdosStrausConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Erdos Straus Conjecture
Category: Brockian Conjecture
Target: Brockian.ErdosStraus.ErdosStrausConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.ErdosStraus

/-- `ErdosStrausRepr n` says that `4/n` is a sum of three positive unit fractions. -/

theorem repr_of_prime_of_mod_twelve_ne_one {p : ℕ} (hp : p.Prime) (h : p % 12 ≠ 1) :
    ErdosStrausRepr p := by
  have hp2 : 2 ≤ p := hp.two_le
  by_cases he : p % 2 = 0
  · exact repr_of_even (by omega) he
  by_cases h4 : p % 4 = 3
  · exact repr_of_mod_four_eq_three h4
  by_cases h3 : p % 3 = 2
  · exact repr_of_mod_three_eq_two h3
  -- remaining: p % 4 = 1 and p % 3 ∈ {0, 1}; p % 3 = 0 forces p = 3, contradiction
  exfalso
  have h30 : p % 3 = 0 ∨ p % 3 = 1 := by omega
  rcases h30 with h30 | h31
  · have : (3 : ℕ) ∣ p := by omega
    have := (Nat.Prime.eq_one_or_self_of_dvd hp 3 this)
    omega
  · omega

/-- **Erdős–Straus reduction.** If every prime `p ≡ 1 [MOD 12]` admits a representation
of `4/p` as a sum of three unit fractions, then every `n ≥ 2` does. In particular the
Erdős–Straus conjecture is equivalent to its restriction to primes congruent to `1` mod `12`. -/
