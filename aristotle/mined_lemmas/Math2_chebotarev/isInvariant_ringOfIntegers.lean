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

lemma isInvariant_ringOfIntegers [IsGalois ℚ L] :
    Algebra.IsInvariant ℤ (𝓞 L) (𝓞 L ≃ₐ[ℤ] 𝓞 L) :=
  Algebra.isInvariant_of_isGalois' ℤ ℚ L _

/-- There is a prime of the ring of integers above any rational prime, and its residue field
is finite. -/
