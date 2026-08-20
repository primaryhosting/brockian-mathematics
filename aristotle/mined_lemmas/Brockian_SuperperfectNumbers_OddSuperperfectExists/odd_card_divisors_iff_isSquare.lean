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
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

A natural number `n` is *superperfect* when `σ(σ(n)) = 2n`. Whether an odd superperfect
number exists is an open problem, so the target result
`Brockian.SuperperfectNumbers.OddSuperperfectExists` is a Lean-checked *conditional
reduction*: the existence of an odd superperfect number is equivalent to the existence of
one satisfying a list of proved necessary conditions (size lower bound from a kernel
computation, deficiency bounds, non-divisibility by `3` in the non-square case, and parity
information in the square case).
-/

namespace Brockian.SuperperfectNumbers

open Finset

/-- The sum-of-divisors function `σ(n) = ∑_{d ∣ n} d`. -/

lemma odd_card_divisors_iff_isSquare {n : ℕ} (hn : n ≠ 0) :
    Odd n.divisors.card ↔ IsSquare n := by
  rw [isSquare_iff_even_factorization hn, Nat.card_divisors hn, Nat.not_even_iff_odd.symm,
    even_iff_two_dvd, (Nat.prime_two.prime).dvd_finset_prod_iff]
  constructor
  · intro h p
    by_cases hp : p ∈ n.primeFactors
    · have h2 : ¬ (2 ∣ (n.factorization p + 1)) := fun hd => h ⟨p, hp, hd⟩
      rcases Nat.even_or_odd (n.factorization p) with he | ho
      · exact he
      · exact absurd (by rcases ho with ⟨k, hk⟩; omega : 2 ∣ (n.factorization p + 1)) h2
    · have h0 : n.factorization p = 0 := by
        rw [← Nat.support_factorization] at hp
        exact Finsupp.notMem_support_iff.mp hp
      simp [h0]
  · rintro h ⟨p, _, hd⟩
    obtain ⟨k, hk⟩ := h p
    omega

/-- For odd `n`, `σ(n)` is odd exactly when `n` is a perfect square. -/
