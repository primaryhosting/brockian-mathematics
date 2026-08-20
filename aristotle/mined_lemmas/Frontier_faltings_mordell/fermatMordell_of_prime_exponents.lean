/-
# Faltings Mordell
Category: Frontier — Fields Medal Work
Target: Frontier.faltings_mordell
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` commands to precede any module docstring, so the header above is
-- repeated verbatim as the module docstring immediately after the import.)

import Mathlib

/-!
# Faltings Mordell
Category: Frontier — Fields Medal Work
Target: Frontier.faltings_mordell
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- The set of affine rational points of the Fermat curve `x ^ n + y ^ n = 1` over `ℚ`. -/

theorem fermatMordell_of_prime_exponents
    (h : ∀ p : ℕ, p.Prime → 5 ≤ p → (fermatRatPoints p).Finite) : FermatMordell := by
  intro n hn
  by_cases h3 : 3 ∣ n
  · exact (faltings_mordell hn (Or.inl h3)).2
  by_cases h4 : 4 ∣ n
  · exact (faltings_mordell hn (Or.inr h4)).2
  obtain ⟨p, hp, hp5, hpn⟩ := exists_prime_factor_five_le hn h3 h4
  exact fermatRatPoints_finite_of_dvd hpn (h p hp hp5)

end Frontier

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

