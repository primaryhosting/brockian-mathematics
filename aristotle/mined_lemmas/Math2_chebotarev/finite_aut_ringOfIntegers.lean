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

lemma finite_aut_ringOfIntegers : Finite (𝓞 L ≃ₐ[ℤ] 𝓞 L) :=
  Finite.of_equiv _ (galRestrict ℤ ℚ L (𝓞 L)).toEquiv

/-- For `L/ℚ` Galois, the subring of `𝓞 L` fixed by all `ℤ`-algebra automorphisms is `ℤ`. -/
