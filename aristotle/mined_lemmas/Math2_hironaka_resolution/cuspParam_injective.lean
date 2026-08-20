import Mathlib

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

import Mathlib

/-!
# Hironaka Resolution
Category: Frontier Math
Target: Math2.hironaka_resolution
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math2

variable (k : Type*) [Field k]

/-- The affine plane curve `C_{a,b} : y^a = x^b` over a field `k`.
For `a, b ≥ 2` coprime this is the standard quasi-homogeneous plane curve singularity
(for `(a,b) = (2,3)` it is the cuspidal cubic `y² = x³`). -/

lemma cuspParam_injective {a b : ℕ} (ha : 0 < a) (hab : Nat.Coprime a b) :
    Function.Injective (cuspParam k a b) := by
  obtain ⟨u, v, huv⟩ := exists_bezout hab
  intro s t hst
  simp only [cuspParam, Prod.mk.injEq] at hst
  obtain ⟨h1, h2⟩ := hst
  by_cases hs : s = 0
  · subst hs
    have h : t ^ a = 0 := by simpa [zero_pow ha.ne'] using h1.symm
    exact (pow_eq_zero_iff ha.ne' |>.1 h).symm
  · have ht : t ≠ 0 := by
      intro h
      apply hs
      have h0 : s ^ a = 0 := by rw [h1, h, zero_pow ha.ne']
      exact pow_eq_zero_iff ha.ne' |>.1 h0
    calc s = ((s ^ a) ^ u) * ((s ^ b) ^ v) := (bezout_recover hs huv).symm
      _ = ((t ^ a) ^ u) * ((t ^ b) ^ v) := by rw [h1, h2]
      _ = t := bezout_recover ht huv

/-- Away from the singular point the inverse of the parametrization is given by the
Laurent monomial `x^u y^v`, where `ua + vb = 1`. -/
