/-
# Goldbach Wheel K 2 947
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_947
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` because a module docstring may not
-- precede the `import` command in Lean 4; the text is otherwise verbatim.)

import Mathlib

namespace Brockian

/-- The list of "wheel spokes": the primes below `100`, used as the small summand
in the binary (`K = 2`) Goldbach decompositions below. -/

theorem GoldbachWheelK2_947 :
    ∀ n : ℕ, 4 ≤ n → n ≤ 947 → Even n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n := by
  intro n hn4 hn947 hne
  obtain ⟨p, _, hp, hq⟩ :=
    goldbachWheelK2_947_spokes n (Finset.mem_range.mpr (by omega)) hn4
      (Nat.even_iff.mp hne)
  refine ⟨p, n - p, hp, hq, ?_⟩
  have hple : p ≤ n := by
    by_contra h
    have : n - p = 0 := by omega
    rw [this] at hq
    exact Nat.not_prime_zero hq
  omega

end Brockian

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

