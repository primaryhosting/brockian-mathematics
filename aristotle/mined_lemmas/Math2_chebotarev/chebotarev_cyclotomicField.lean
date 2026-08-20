/-
# Chebotarev
Category: Frontier Math
Target: Math2.chebotarev
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` commands to come first in a file, so the module docstring version of
-- the header above is repeated immediately after the imports.)

import Mathlib

/-!
# Chebotarev
Category: Frontier Math
Target: Math2.chebotarev
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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

open NumberField

/-- A cyclotomic extension of `ℚ` is Galois. -/

theorem chebotarev_cyclotomicField (n : ℕ) [NeZero n]
    (σ : 𝓞 (CyclotomicField n ℚ) ≃ₐ[ℤ] 𝓞 (CyclotomicField n ℚ)) :
    {p : ℕ | p.Prime ∧ ∃ Q : Ideal (𝓞 (CyclotomicField n ℚ)), Q.IsPrime ∧
      Q.under ℤ = Ideal.span {(p : ℤ)} ∧ IsArithFrobAt ℤ σ Q}.Infinite :=
  chebotarev n (CyclotomicField n ℚ) σ

end Math2

