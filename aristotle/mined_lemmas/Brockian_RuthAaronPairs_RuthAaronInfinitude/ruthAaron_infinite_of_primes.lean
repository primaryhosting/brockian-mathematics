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
# Ruth Aaron Infinitude
Category: Brockian Conjecture
Target: Brockian.RuthAaronPairs.RuthAaronInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.RuthAaronPairs

/-- `sopfr n` is the sum of the prime factors of `n`, counted with multiplicity
(A001414, the "integer logarithm"). By convention `sopfr 0 = sopfr 1 = 0`. -/

theorem ruthAaron_infinite_of_primes
    (h : ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧ sopfr (p + 1) = p) :
    {n : ℕ | IsRuthAaronPair n}.Infinite := by
  refine RuthAaronInfinitude.mpr fun N => ?_
  obtain ⟨p, hNp, hp, hsum⟩ := h N
  exact ⟨p, hNp, hp.pos, by rw [sopfr_prime hp, hsum]⟩

/-! ### The squarefree (distinct primes) variant

The variant conjecture uses `sopf`, the sum of the *distinct* prime factors.
It is likewise open, and admits the same reduction. -/

/-- `sopf n` is the sum of the distinct prime factors of `n` (A008472). -/
