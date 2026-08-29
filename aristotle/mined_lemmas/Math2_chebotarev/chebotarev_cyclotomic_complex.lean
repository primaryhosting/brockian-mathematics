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

theorem chebotarev_cyclotomic_complex {n : ℕ} (hn : 0 < n) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n)
    (σ : Algebra.adjoin ℤ ({ζ} : Set ℂ) ≃+* Algebra.adjoin ℤ ({ζ} : Set ℂ)) :
    {p : ℕ | p.Prime ∧ IsFrobeniusAt (Algebra.adjoin ℤ ({ζ} : Set ℂ)) σ p}.Infinite := by
  have hmem : ζ ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ) := Algebra.subset_adjoin rfl
  have hζ' : IsPrimitiveRoot (⟨ζ, hmem⟩ : Algebra.adjoin ℤ ({ζ} : Set ℂ)) n :=
    hζ.of_map_of_injective (f := (Algebra.adjoin ℤ ({ζ} : Set ℂ)).subtype) Subtype.val_injective
  have hgen : Algebra.adjoin ℤ
      ({(⟨ζ, hmem⟩ : Algebra.adjoin ℤ ({ζ} : Set ℂ))} : Set (Algebra.adjoin ℤ ({ζ} : Set ℂ))) = ⊤ := by
    have h := Algebra.adjoin_adjoin_coe_preimage (R := ℤ) (s := ({ζ} : Set ℂ))
    convert h using 2
    ext x
    simp [Subtype.ext_iff]
  exact chebotarev hn hζ' hgen σ

end Math2

