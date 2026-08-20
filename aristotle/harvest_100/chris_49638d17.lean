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

/-- **Key intermediate lemma.** A real number multiplied by itself is nonnegative:
either `0 ≤ t`, and the product of two nonnegatives is nonnegative, or `t ≤ 0`,
and the product of two nonpositives is nonnegative. -/
theorem mul_self_nonneg_real (t : ℝ) : 0 ≤ t * t := by
  rcases le_total 0 t with ht | ht
  · exact mul_nonneg ht ht
  · exact mul_nonneg_of_nonpos_of_nonpos ht ht

/-- **Chebyshev-positivity shadow.** For every real `t`, `0 ≤ t ^ 2`; this is the
pointwise fact underlying the nonnegativity of the summands `Λ(n) ^ 2` in
Montgomery's second moment. -/
theorem psi_shadow : ∀ t : ℝ, 0 ≤ t ^ 2 := by
  intro t
  rw [pow_two]
  exact mul_self_nonneg_real t

/-- Each summand `Λ(n) ^ 2` of Montgomery's second moment is nonnegative. -/
theorem vonMangoldt_sq_nonneg (n : ℕ) :
    0 ≤ (ArithmeticFunction.vonMangoldt n) ^ 2 :=
  psi_shadow _

/-- The second-moment sum `∑ n ∈ s, Λ(n) ^ 2` is nonnegative. -/
theorem sum_vonMangoldt_sq_nonneg (s : Finset ℕ) :
    0 ≤ ∑ n ∈ s, (ArithmeticFunction.vonMangoldt n) ^ 2 :=
  Finset.sum_nonneg fun n _ => vonMangoldt_sq_nonneg n

end Chebyshev
end Riemann

