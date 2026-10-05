/-
# Catalan Closed
Category: Pure Mathematics
Target: Math.catalan_closed
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Catalan Closed
Category: Pure Mathematics
Target: Math.catalan_closed
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

namespace Math

/-- The exact (division-free) form of the closed formula:
`(n + 1) * catalan n = C(2n, n)`. -/
theorem catalan_mul_succ (n : ℕ) : (n + 1) * catalan n = Nat.choose (2 * n) n := by
  have hdvd : (n + 1) ∣ Nat.centralBinom n := Nat.succ_dvd_centralBinom n
  have h : catalan n = Nat.centralBinom n / (n + 1) := catalan_eq_centralBinom_div n
  have : (n + 1) * catalan n = Nat.centralBinom n := by
    rw [h, Nat.mul_div_cancel' hdvd]
  simpa [Nat.centralBinom] using this

/-- **The nth Catalan number equals `C(2n, n) / (n + 1)`.**
Stated over `ℚ` so that the division is genuine division, together with the
equivalent exact natural-number identity `(n + 1) * catalan n = C(2n, n)`. -/
theorem catalan_closed (n : ℕ) :
    (catalan n : ℚ) = (Nat.choose (2 * n) n : ℚ) / (n + 1) ∧
      (n + 1) * catalan n = Nat.choose (2 * n) n := by
  refine ⟨?_, catalan_mul_succ n⟩
  have h : ((n : ℚ) + 1) * (catalan n : ℚ) = (Nat.choose (2 * n) n : ℚ) := by
    exact_mod_cast congrArg (fun m : ℕ => (m : ℚ)) (catalan_mul_succ n)
  have hne : ((n : ℚ) + 1) ≠ 0 := by positivity
  rw [eq_div_iff hne, mul_comm]
  exact h

end Math

