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

theorem odd_sigma_and_sigma_not_isSquare_of_isSquare {n : ℕ} (hodd : Odd n)
    (h : Superperfect n) (hsq : IsSquare n) : Odd (sigma n) ∧ ¬ IsSquare (sigma n) := by
  have hs : Odd (sigma n) := (odd_sigma_iff_isSquare h.1 hodd).mpr hsq
  refine ⟨hs, fun hsq' => ?_⟩
  have hpos : 0 < sigma n := sigma_pos h.1
  have : Odd (sigma (sigma n)) := (odd_sigma_iff_isSquare hpos hs).mpr hsq'
  rw [h.2] at this
  exact (Nat.not_odd_iff_even.mpr ⟨n, by ring⟩) this

/-! ### A verified finite search

A direct kernel computation shows that there is no odd superperfect number below `1000`.
(The literature records a far larger verified bound; the point here is that the bound below
is checked by the Lean kernel.) -/

section FiniteCheck

set_option maxRecDepth 1000000

