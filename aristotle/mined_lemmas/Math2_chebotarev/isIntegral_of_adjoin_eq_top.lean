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

namespace Math2

/-- `IsFrobeniusAt R σ p` says that the ring automorphism `σ` of `R` is a Frobenius
automorphism at the rational prime `p`: there is a maximal ideal `P` of `R` lying above `p`
such that `σ x ≡ x ^ p (mod P)` for all `x : R`.

For `R` the ring of integers of a Galois number field this is the usual notion of (an element
of) the Frobenius conjugacy class at `p`. -/

theorem isIntegral_of_adjoin_eq_top (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n)
    (hgen : Algebra.adjoin ℤ ({ζ} : Set R) = ⊤) : Algebra.IsIntegral ℤ R := by
  constructor
  intro x
  have hx : x ∈ Algebra.adjoin ℤ ({ζ} : Set R) := by rw [hgen]; trivial
  have hle : Algebra.adjoin ℤ ({ζ} : Set R) ≤ integralClosure ℤ R :=
    Algebra.adjoin_le (by simpa using hζ.isIntegral hn)
  exact hle hx

omit [IsDomain R] in
/-- Any prime number is contained in some maximal ideal of a ring that is integral over `ℤ`
(and of characteristic zero). -/
