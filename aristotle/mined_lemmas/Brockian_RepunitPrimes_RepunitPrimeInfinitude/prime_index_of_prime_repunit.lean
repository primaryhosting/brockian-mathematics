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
# Repunit Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.RepunitPrimes.RepunitPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators

namespace Brockian
namespace RepunitPrimes

/-- The `n`-th repunit `R n = 1 + 10 + ⋯ + 10 ^ (n - 1) = (10 ^ n - 1) / 9`,
i.e. the number written with `n` ones in base ten. -/

theorem prime_index_of_prime_repunit {n : ℕ} (h : Nat.Prime (repunit n)) : Nat.Prime n := by
  have hn2 : 2 ≤ n := by
    rcases n with _ | _ | n
    · simp at h; exact absurd h (by norm_num)
    · simp at h; exact absurd h (by norm_num)
    · omega
  refine Nat.prime_def.mpr ⟨hn2, ?_⟩
  intro m hm
  have hdvd : repunit m ∣ repunit n := repunit_dvd_repunit hm
  rcases (Nat.Prime.eq_one_or_self_of_dvd h _ hdvd) with h1 | h1
  · exact Or.inl (repunit_eq_one_iff.mp h1)
  · exact Or.inr (repunit_injective h1)

/-- Every prime other than `2` and `5` divides some repunit. -/
