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

lemma exists_unit_pow_zetaInt (f : 𝓞 L ≃ₐ[ℤ] 𝓞 L) :
    ∃ a : (ZMod n)ˣ, f (zetaInt n L) = zetaInt n L ^ ((a : ZMod n).val) :=
  ⟨(zetaInt_isPrimitiveRoot n L).autToPow ℤ f,
    ((zetaInt_isPrimitiveRoot n L).autToPow_spec ℤ f).symm⟩

/-- A Frobenius element at a prime `Q` above `p` (with `p ∤ n`) raises `ζₙ` to the `p`-th
power. -/
