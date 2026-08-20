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
theorem psi_shadow : ∀ t : ℝ, 0 ≤ t ^ 2 := by
  intro t
  rw [pow_two]
  exact mul_self_nonneg' t

/-- Concrete instance of the shadow: each von Mangoldt summand `Λ(n)^2` is
nonnegative. -/
theorem vonMangoldt_sq_nonneg (n : ℕ) :
    0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 :=
  psi_shadow _

/-- Consequently, every partial second moment `∑_{n < N} Λ(n)^2` is nonnegative. -/
theorem sum_vonMangoldt_sq_nonneg (N : ℕ) :
    0 ≤ ∑ n ∈ Finset.range N, (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 :=
  Finset.sum_nonneg fun n _ => vonMangoldt_sq_nonneg n

end Riemann.Chebyshev

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

