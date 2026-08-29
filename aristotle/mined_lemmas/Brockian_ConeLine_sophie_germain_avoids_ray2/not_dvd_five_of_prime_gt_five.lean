import Mathlib

/-!
# Sophie Germain Avoids Ray 2
Category: Cone Line
Target: Brockian.ConeLine.sophie_germain_avoids_ray2
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

/-- A prime `q > 5` is not divisible by `5`. -/

theorem not_dvd_five_of_prime_gt_five {q : ℕ} (hq : Nat.Prime q) (h : 5 < q) :
    ¬ (5 ∣ q) := by
  intro hdvd
  rcases (Nat.Prime.eq_one_or_self_of_dvd hq 5 hdvd) with h1 | h2
  · omega
  · omega

/-- A Sophie Germain prime `p > 5` never lies on ray 2 (`p % 5 ≠ 2`), and the pair of
residues `(p % 5, (2p+1) % 5)` is one of `(1,3)`, `(3,2)`, `(4,4)`. -/
