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

namespace Riemann.Chebyshev

/-- Key intermediate lemma: in any linear ordered ring, the product of an element
with itself is nonnegative. -/

theorem mul_self_nonneg' {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] (t : R) :
    0 ≤ t * t := by
  rcases le_total 0 t with h | h
  · exact mul_nonneg h h
  · exact mul_nonneg_of_nonpos_of_nonpos h h

/-- **Psi shadow**: the Chebyshev-positivity shadow.  Every summand `Λ(n)^2`
appearing in Montgomery's second moment is nonnegative; abstractly, for every
real `t` we have `0 ≤ t ^ 2`. -/
