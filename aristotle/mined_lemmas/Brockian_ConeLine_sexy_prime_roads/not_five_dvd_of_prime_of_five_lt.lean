import Mathlib
/-!
# Sexy Prime Roads
Category: Cone Line
Target: Brockian.ConeLine.sexy_prime_roads
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

namespace Brockian
namespace ConeLine

/-- A prime `p` greater than `5` is not divisible by `5`. -/

theorem not_five_dvd_of_prime_of_five_lt {p : ℕ} (hp : Nat.Prime p) (h5 : 5 < p) :
    ¬ (5 ∣ p) := by
  intro hdvd
  have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp hdvd
  omega

/-- **Sexy prime roads.** If `p` and `p + 6` are both prime and `p > 5`, then modulo `5`
the pair `(p % 5, (p+6) % 5)` is one of `(1,2)`, `(2,3)`, `(3,4)`. -/
