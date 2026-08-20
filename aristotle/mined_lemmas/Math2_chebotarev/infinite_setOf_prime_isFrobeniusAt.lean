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

theorem infinite_setOf_prime_isFrobeniusAt (q : ℕ) [NeZero q]
    (σ : CyclotomicField q ℚ ≃ₐ[ℚ] CyclotomicField q ℚ) :
    {p : ℕ | p.Prime ∧ IsFrobeniusAt q p σ}.Infinite := by
  obtain ⟨a, ha, hfrob⟩ := exists_residue_isFrobeniusAt q σ
  have hset : {p : ℕ | p.Prime ∧ IsFrobeniusAt q p σ} = {p : ℕ | p.Prime ∧ (p : ZMod q) = a} := by
    ext p
    exact and_congr_right fun _ => hfrob p
  rw [hset]
  exact Nat.infinite_setOf_prime_and_eq_mod ha

end Math2

