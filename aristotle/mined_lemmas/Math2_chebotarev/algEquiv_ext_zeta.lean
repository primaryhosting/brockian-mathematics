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

lemma algEquiv_ext_zeta {f g : L ≃ₐ[ℚ] L}
    (h : f (IsCyclotomicExtension.zeta n ℚ L) = g (IsCyclotomicExtension.zeta n ℚ L)) :
    f = g := by
  have hz := IsCyclotomicExtension.zeta_spec n ℚ L
  apply hz.autToPow_injective ℚ
  have h1 := hz.autToPow_spec ℚ f
  have h2 := hz.autToPow_spec ℚ g
  have hv : ((hz.autToPow ℚ f : (ZMod n)ˣ) : ZMod n).val =
      ((hz.autToPow ℚ g : (ZMod n)ˣ) : ZMod n).val :=
    hz.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (by rw [h1, h2, h])
  ext
  exact ZMod.val_injective _ hv

/-- Two `ℤ`-automorphisms of the ring of integers of `L = ℚ(ζₙ)` agreeing on `ζₙ` are equal. -/
