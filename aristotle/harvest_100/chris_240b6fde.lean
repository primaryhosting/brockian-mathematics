/-
# Sexy Prime Roads
Category: Cone Line
Target: Brockian.ConeLine.sexy_prime_roads
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Sexy Prime Roads
Category: Cone Line
Target: Brockian.ConeLine.sexy_prime_roads
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Brockian.ConeLine

/-- For a sexy prime pair `(p, p + 6)` with `p > 5`, the residues mod 5 are
`(1,2)`, `(2,3)` or `(3,4)`. -/
theorem sexy_prime_roads (p : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime (p + 6))
    (h5 : 5 < p) :
    (p % 5, (p + 6) % 5) = (1, 2) ∨ (p % 5, (p + 6) % 5) = (2, 3) ∨
      (p % 5, (p + 6) % 5) = (3, 4) := by
  have hp5 : ¬ (5 ∣ p) := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp h
    omega
  have hq5 : ¬ (5 ∣ (p + 6)) := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hq).mp h
    omega
  have h1 : p % 5 ≠ 0 := fun h => hp5 (Nat.dvd_of_mod_eq_zero h)
  have h2 : (p + 6) % 5 ≠ 0 := fun h => hq5 (Nat.dvd_of_mod_eq_zero h)
  have h3 : (p + 6) % 5 = (p % 5 + 1) % 5 := by omega
  have h4 : p % 5 < 5 := Nat.mod_lt _ (by norm_num)
  simp only [Prod.mk.injEq]
  omega

end Brockian.ConeLine

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

