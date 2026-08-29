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

theorem exists_maximal_mem_of_prime [Algebra.IsIntegral ℤ R] {p : ℕ} (hp : p.Prime) :
    ∃ P : Ideal R, P.IsMaximal ∧ (p : R) ∈ P := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  haveI : (Ideal.span ({(p : ℤ)} : Set ℤ)).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hpZ.irreducible
  have hker : RingHom.ker (algebraMap ℤ R) ≤ Ideal.span ({(p : ℤ)} : Set ℤ) := by
    have hinj : Function.Injective (algebraMap ℤ R) := (algebraMap ℤ R).injective_int
    rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]
    exact bot_le
  obtain ⟨Q, hQmax, hQ⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (S := R) (Ideal.span ({(p : ℤ)} : Set ℤ)) hker
  refine ⟨Q, hQmax, ?_⟩
  have : (p : ℤ) ∈ Q.comap (algebraMap ℤ R) := by
    rw [hQ]; exact Ideal.subset_span rfl
  simpa using this

omit [IsDomain R] [CharZero R] in
/-- If `σ ζ = ζ ^ p` and `P` is a maximal ideal containing the prime `p`, then `σ` reduces to
the `p`-power Frobenius modulo `P`. -/
