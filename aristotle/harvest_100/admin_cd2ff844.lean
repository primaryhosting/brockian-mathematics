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

namespace Riemann
namespace Chebyshev

/-- **Psi shadow.** The Chebyshev-positivity shadow: every real square is
nonnegative.  In particular each summand `Λ(n)^2` occurring in Montgomery's
second moment for the Chebyshev `ψ`-function is nonnegative. -/
theorem psi_shadow : ∀ t : ℝ, 0 ≤ t ^ 2 := fun t => sq_nonneg t

/-- Instantiation at the von Mangoldt function: `Λ(n)^2 ≥ 0` for every `n`. -/
theorem vonMangoldt_sq_nonneg (n : ℕ) : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 :=
  psi_shadow _

/-- Consequently, any finite second moment `∑ n ∈ s, Λ(n)^2` is nonnegative. -/
theorem sum_vonMangoldt_sq_nonneg (s : Finset ℕ) :
    0 ≤ ∑ n ∈ s, (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 :=
  Finset.sum_nonneg fun n _ => vonMangoldt_sq_nonneg n

end Chebyshev
end Riemann

