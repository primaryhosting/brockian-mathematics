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

lemma aut_ext_zetaInt {f g : 𝓞 L ≃ₐ[ℤ] 𝓞 L} (h : f (zetaInt n L) = g (zetaInt n L)) : f = g := by
  set e := galRestrict ℤ ℚ L (𝓞 L) with he
  have key : e.symm f = e.symm g := by
    apply algEquiv_ext_zeta (n := n)
    have h1 := algebraMap_galRestrict_apply (A := ℤ) (e.symm f) (zetaInt n L)
    have h2 := algebraMap_galRestrict_apply (A := ℤ) (e.symm g) (zetaInt n L)
    rw [he] at h1 h2
    simp only [MulEquiv.apply_symm_apply, algebraMap_zetaInt] at h1 h2
    rw [← h1, ← h2, h]
  simpa using congrArg e key

/-- Every `ℤ`-automorphism of the ring of integers raises `ζₙ` to a power prime to `n`. -/
