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

open ArithmeticFunction Complex Filter Topology

/-! ### The analytic input: Λ-weighted density of a residue class -/

/-- The terms of the `L`-series of the von Mangoldt function restricted to a residue class,
evaluated at a real point, are real. -/

theorem card_conjClass (q : ℕ) [NeZero q]
    (σ : CyclotomicField q ℚ ≃ₐ[ℚ] CyclotomicField q ℚ) :
    Nat.card {τ : CyclotomicField q ℚ ≃ₐ[ℚ] CyclotomicField q ℚ | IsConj σ τ} = 1 := by
  have hcomm : ∀ σ τ : CyclotomicField q ℚ ≃ₐ[ℚ] CyclotomicField q ℚ, σ * τ = τ * σ := by
    intro σ τ
    have e := IsCyclotomicExtension.autEquivPow (n := q) (K := ℚ) (CyclotomicField q ℚ)
      (irreducible_cyclotomic_rat q)
    exact e.injective (by rw [map_mul, map_mul, mul_comm])
  have hset : {τ : CyclotomicField q ℚ ≃ₐ[ℚ] CyclotomicField q ℚ | IsConj σ τ} = {σ} := by
    ext τ
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨c, hc⟩
      have h2 : (c : CyclotomicField q ℚ ≃ₐ[ℚ] CyclotomicField q ℚ) * σ = τ * c := hc.eq
      rw [hcomm (c : CyclotomicField q ℚ ≃ₐ[ℚ] CyclotomicField q ℚ) σ] at h2
      exact (mul_right_cancel h2).symm
    · rintro rfl
      exact IsConj.refl _
  rw [hset]
  simp

