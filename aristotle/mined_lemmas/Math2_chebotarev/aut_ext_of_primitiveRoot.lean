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

theorem aut_ext_of_primitiveRoot (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (σ τ : 𝓞 K ≃ₐ[ℤ] 𝓞 K) (h : σ hζ.toInteger = τ hζ.toInteger) : σ = τ := by
  obtain ⟨f, rfl⟩ := (galRestrict ℤ ℚ K (𝓞 K)).surjective σ
  obtain ⟨g, rfl⟩ := (galRestrict ℤ ℚ K (𝓞 K)).surjective τ
  have hf : f ζ = g ζ := by
    have := congrArg (algebraMap (𝓞 K) K) h
    rwa [algebraMap_galRestrict_apply, algebraMap_galRestrict_apply,
      show (algebraMap (𝓞 K) K) hζ.toInteger = ζ from rfl] at this
  have hfg : f = g := by
    apply AlgEquiv.coe_algHom_injective
    apply (hζ.powerBasis ℚ).algHom_ext
    simpa [IsPrimitiveRoot.powerBasis_gen] using hf
  rw [hfg]

/-- If two automorphisms of `𝓞 ℚ(ζₙ)` send a primitive `n`-th root of unity `z` to `z ^ i` and
`z ^ j` respectively, with `i ≡ j (mod n)`, then they are equal. -/
