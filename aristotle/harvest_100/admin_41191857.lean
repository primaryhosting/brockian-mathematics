/-!
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

set_option grind.warning false

namespace Riemann
namespace Chebyshev

/-- **Chebyshev-positivity shadow.**  Every square of a real number is nonnegative;
in particular each summand `Λ(n)^2` occurring in Montgomery's second moment for the
Chebyshev `ψ`-function is nonnegative.  The proof splits on the sign of `t`. -/
theorem psi_shadow : ∀ t : ℝ, 0 ≤ t ^ 2 := by
  intro t
  rcases le_total 0 t with ht | ht
  · exact pow_nonneg ht 2
  · have : 0 ≤ (-t) ^ 2 := pow_nonneg (neg_nonneg.mpr ht) 2
    simpa using this

/-- Specialization of `psi_shadow` to the von Mangoldt function: each summand
`Λ(n)^2` of Montgomery's second moment is nonnegative. -/
theorem vonMangoldt_sq_nonneg (n : ℕ) :
    0 ≤ (ArithmeticFunction.vonMangoldt n) ^ 2 :=
  psi_shadow _

/-- Consequently, any finite second moment `∑_{n ∈ s} Λ(n)^2` is nonnegative. -/
theorem sum_vonMangoldt_sq_nonneg (s : Finset ℕ) :
    0 ≤ ∑ n ∈ s, (ArithmeticFunction.vonMangoldt n) ^ 2 :=
  Finset.sum_nonneg fun n _ => vonMangoldt_sq_nonneg n

end Chebyshev
end Riemann

