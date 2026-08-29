/-
# Psi Shadow
Category: Riemann Program
Target: Riemann.Chebyshev.psi_shadow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


import Mathlib

/-!
# Psi Shadow
Category: Riemann Program
Target: Riemann.Chebyshev.psi_shadow
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

namespace Riemann
namespace Chebyshev

/-- **Psi shadow (Chebyshev positivity).**
Each summand `Λ(n)^2` occurring in Montgomery's second moment for the
Chebyshev `ψ`-function is nonnegative: for every real `t`, `0 ≤ t ^ 2`. -/

theorem psi_shadow_sum (f : ℕ → ℝ) (s : Finset ℕ) : 0 ≤ ∑ n ∈ s, f n ^ 2 :=
  Finset.sum_nonneg fun n _ => psi_shadow (f n)

end Chebyshev
end Riemann

#print axioms Riemann.Chebyshev.psi_shadow
#print axioms Riemann.Chebyshev.psi_shadow_sum

