import Mathlib

/-!
# Quadruplet Visits All Active Rays
Category: Cone Line
Target: Brockian.ConeLine.quadruplet_visits_all_active_rays
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian.ConeLine

/-- A prime greater than `5` is not divisible by `5`. -/

theorem mod_five_ne_zero_of_prime {q : ℕ} (hq : q.Prime) (hq5 : 5 < q) : q % 5 ≠ 0 := by
  intro h
  have hdvd : 5 ∣ q := Nat.dvd_of_mod_eq_zero h
  rcases hq.eq_one_or_self_of_dvd 5 hdvd with h1 | h2 <;> omega

/-- A prime quadruplet `(p, p+2, p+6, p+8)` with `p > 5` has `p ≡ 1 (mod 5)`, and the
four members occupy the residues `1, 3, 2, 4` mod `5` respectively. -/
