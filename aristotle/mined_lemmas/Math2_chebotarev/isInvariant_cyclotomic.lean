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

theorem isInvariant_cyclotomic (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] :
    Algebra.IsInvariant ℤ (𝓞 K) (𝓞 K ≃ₐ[ℤ] 𝓞 K) :=
  have := isGalois_cyclotomic n K
  Algebra.isInvariant_of_isGalois' ℤ ℚ K (𝓞 K)

/-- Two automorphisms of the ring of integers of a cyclotomic field `ℚ(ζₙ)` that agree on a
primitive `n`-th root of unity are equal. -/
