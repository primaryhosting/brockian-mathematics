/-
# Psi Shadow
Category: Riemann Program
Target: Riemann.Chebyshev.psi_shadow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Riemann
namespace Chebyshev

/-- **Psi shadow.** The Chebyshev-positivity shadow: every summand `Λ(n)^2` occurring in
Montgomery's second moment is nonnegative, since squares of real numbers are nonnegative. -/

theorem sum_vonMangoldt_sq_nonneg (N : ℕ) :
    0 ≤ ∑ n ∈ Finset.range N, (ArithmeticFunction.vonMangoldt n) ^ 2 :=
  Finset.sum_nonneg fun n _ => vonMangoldt_sq_nonneg n

end Chebyshev
end Riemann

