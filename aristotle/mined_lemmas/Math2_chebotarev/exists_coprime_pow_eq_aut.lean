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

theorem exists_coprime_pow_eq_aut (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) (σ : R ≃+* R) :
    ∃ a : ℕ, Nat.Coprime a n ∧ σ ζ = ζ ^ a := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hprim : IsPrimitiveRoot (σ ζ) n := hζ.map_of_injective σ.injective
  obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one hprim.pow_eq_one
  exact ⟨a, ((hζ.pow_iff_coprime hn a).1 (ha ▸ hprim)), ha.symm⟩

omit [IsDomain R] [CharZero R] in
/-- `ℤ[ζ]` is integral over `ℤ`. -/
