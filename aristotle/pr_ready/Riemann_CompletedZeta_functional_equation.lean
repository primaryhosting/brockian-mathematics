/-!
# Functional Equation
Category: Riemann Program
Target: Riemann.CompletedZeta.functional_equation
Statement: For all s : Complex, completedRiemannZeta (1 - s) = completedRiemannZeta s : the functional equation of the completed zeta function Lambda(s). (Use Mathlib's completedRiemannZeta_one_sub.)
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
# Functional Equation
Category: Riemann Program
Target: Riemann.CompletedZeta.functional_equation
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

namespace Riemann
namespace CompletedZeta

/-- The functional equation of the completed Riemann zeta function:
`Λ(1 - s) = Λ(s)` for all `s : ℂ`. -/
theorem functional_equation (s : ℂ) :
    completedRiemannZeta (1 - s) = completedRiemannZeta s :=
  completedRiemannZeta_one_sub s

end CompletedZeta
end Riemann

