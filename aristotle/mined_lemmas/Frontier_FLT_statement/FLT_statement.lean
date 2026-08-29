-- (Lean 4 requires `import` lines to precede any module docstring, so the required
-- header comment appears immediately below the import.)
import Mathlib

/-!
# FLT Statement
Category: Frontier — Prime Numbers
Target: Frontier.FLT_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Frontier

/-- Fermat's Last Theorem for a fixed exponent `n`, stated with *positive* integers:
there are no `x, y, z > 0` with `x ^ n + y ^ n = z ^ n`. -/

theorem FLT_statement (hprimes : ∀ p : ℕ, p.Prime → 5 ≤ p → FLTFor p) : FLT := by
  intro n hn
  obtain hdvd | ⟨p, hp, hdvd, hpodd⟩ :=
    Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt hn
  · exact FLTFor_of_dvd hdvd FLT_four
  · refine FLTFor_of_dvd hdvd ?_
    rcases eq_or_ne p 3 with rfl | hp3
    · exact FLT_three
    · refine hprimes p hp ?_
      have h2 := hp.two_le
      rcases hpodd with ⟨k, hk⟩
      omega

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

