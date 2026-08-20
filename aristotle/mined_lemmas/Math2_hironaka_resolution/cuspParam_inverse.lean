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

lemma cuspParam_inverse {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) :
    ∃ u v : ℤ, ∀ p : k × k, p ∈ cuspCurve k a b → p ≠ 0 →
      cuspParam k a b (p.1 ^ u * p.2 ^ v) = p := by
  obtain ⟨u, v, huv⟩ := exists_bezout hab
  refine ⟨u, v, ?_⟩
  rintro ⟨x, y⟩ hp hne
  simp only [cuspCurve, Set.mem_setOf_eq] at hp
  have hx : x ≠ 0 := by
    intro hx
    apply hne
    subst hx
    have h1 : y ^ a = 0 := by rw [hp, zero_pow hb.ne']
    have h2 : y = 0 := pow_eq_zero_iff ha.ne' |>.1 h1
    simp [h2]
  have hy : y ≠ 0 := by
    intro hy
    apply hx
    rw [hy, zero_pow ha.ne'] at hp
    exact pow_eq_zero_iff hb.ne' |>.1 hp.symm
  have hxy : (y : k) ^ (a : ℤ) = x ^ (b : ℤ) := by
    simpa [zpow_natCast] using hp
  have h1 := monomial_zpow_fst hx hxy huv
  have h2 := monomial_zpow_snd hy hxy huv
  rw [zpow_natCast] at h1 h2
  simp only [cuspParam, Prod.mk.injEq]
  exact ⟨h1, h2⟩

/-- The parametrization is onto the curve. -/
