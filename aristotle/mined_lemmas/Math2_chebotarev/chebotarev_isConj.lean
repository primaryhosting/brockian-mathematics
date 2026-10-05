/-
# Chebotarev
Category: Frontier Math
Target: Math2.chebotarev
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- Auxiliary step: an automorphism `σ` of a field containing a primitive `n`-th root of unity
`ζ` sends `ζ` to `ζ ^ m` for some `m` that is invertible modulo `n`. -/

theorem chebotarev_isConj {n : ℕ} [NeZero n] {K : Type*} [Field K] [Algebra ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) (σ : K ≃ₐ[ℚ] K) :
    {p : ℕ | p.Prime ∧ ¬ p ∣ n ∧ ∃ f : K ≃ₐ[ℚ] K, f ζ = ζ ^ p ∧ IsConj f σ}.Infinite := by
  refine Set.Infinite.mono ?_ (chebotarev hζ σ)
  rintro p ⟨hp, hpn, hpζ⟩
  exact ⟨hp, hpn, σ, hpζ, IsConj.refl σ⟩

/-- Sanity check that the hypotheses are satisfiable: applied to the cyclotomic field
`ℚ(ζ₅)` and the identity automorphism, the theorem says that there are infinitely many
primes `p` with `p ≡ 1 (mod 5)`, phrased as `Frob_p = 1`. -/
example :
    {p : ℕ | p.Prime ∧ ¬ p ∣ 5 ∧
      (AlgEquiv.refl : CyclotomicField 5 ℚ ≃ₐ[ℚ] CyclotomicField 5 ℚ)
          (IsCyclotomicExtension.zeta 5 ℚ (CyclotomicField 5 ℚ))
        = (IsCyclotomicExtension.zeta 5 ℚ (CyclotomicField 5 ℚ)) ^ p}.Infinite :=
  chebotarev (IsCyclotomicExtension.zeta_spec 5 ℚ (CyclotomicField 5 ℚ)) AlgEquiv.refl

end Math2

