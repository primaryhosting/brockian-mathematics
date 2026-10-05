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

namespace Math2

/-- If `ζ` is a primitive `n`-th root of unity and `a ≡ b [MOD n]`, then `ζ ^ a = ζ ^ b`. -/

theorem chebotarev_cyclotomicField (n : ℕ) [NeZero n]
    (σ : CyclotomicField n ℚ ≃ₐ[ℚ] CyclotomicField n ℚ) :
    {p : ℕ | p.Prime ∧ ¬ p ∣ n ∧
      σ (IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ)) =
        IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ) ^ p}.Infinite :=
  chebotarev (NeZero.ne n) (IsCyclotomicExtension.zeta_spec n ℚ (CyclotomicField n ℚ)) σ

end Math2

