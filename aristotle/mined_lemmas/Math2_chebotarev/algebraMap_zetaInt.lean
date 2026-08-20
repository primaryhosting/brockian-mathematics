import Mathlib

/-!
# Chebotarev
Category: Frontier Math
Target: Math2.chebotarev
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math2

open NumberField

section NumberFields

variable (L : Type*) [Field L] [NumberField L]

/-- The group of `ℤ`-algebra automorphisms of the ring of integers of a number field is
finite. -/

lemma algebraMap_zetaInt :
    algebraMap (𝓞 L) L (zetaInt n L) = IsCyclotomicExtension.zeta n ℚ L := rfl

variable {n L}

/-- Two `ℚ`-automorphisms of `L = ℚ(ζₙ)` agreeing on `ζₙ` are equal. -/
