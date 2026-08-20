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
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the header above is
-- given as a plain block comment and repeated verbatim as a module docstring below.)

import Mathlib

/-!
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.LandauNSquaredPlusOne

/-- A *Landau prime* is a prime of the form `n ^ 2 + 1`. -/

theorem odd_prime_factor_sq_add_one_mod_four {p n : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hdvd : p ∣ n ^ 2 + 1) : p % 4 = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hne3 : p % 4 ≠ 3 := by
    have : ((n : ZMod p)) ^ 2 = -1 := by
      have : ((n ^ 2 + 1 : ℕ) : ZMod p) = 0 := by
        exact (ZMod.natCast_eq_zero_iff _ _).2 hdvd
      push_cast at this
      linear_combination this
    exact (ZMod.exists_sq_eq_neg_one_iff).1 ⟨(n : ZMod p), by rw [← this]; ring⟩
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hodd
  omega

/-- Unconditionally, there are infinitely many primes dividing some number of the form
`n ^ 2 + 1`. -/
