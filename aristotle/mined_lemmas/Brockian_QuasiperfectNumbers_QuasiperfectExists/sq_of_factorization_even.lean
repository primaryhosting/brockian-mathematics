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

theorem sq_of_factorization_even {m : ℕ} (hm : m ≠ 0) (h : ∀ p, Even (m.factorization p)) :
    ∃ t, m = t ^ 2 := by
  refine ⟨∏ p ∈ m.primeFactors, p ^ (m.factorization p / 2), ?_⟩
  rw [← Finset.prod_pow]
  have hcongr : ∀ p ∈ m.primeFactors,
      (p ^ (m.factorization p / 2)) ^ 2 = p ^ m.factorization p := by
    intro p _
    rw [← pow_mul]
    obtain ⟨t, ht⟩ := h p
    congr 1
    omega
  rw [Finset.prod_congr rfl hcongr]
  exact (Nat.factorization_prod_pow_eq_self hm).symm

/-- Any quasiperfect number is a square or twice a square (equivalently, its odd part is a
perfect square). -/
