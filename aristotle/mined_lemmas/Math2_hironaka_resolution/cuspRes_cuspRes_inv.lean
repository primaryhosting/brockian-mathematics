import Mathlib

/-!
# Hironaka Resolution
Category: Frontier Math
Target: Math2.hironaka_resolution
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

/-- The affine cuspidal cubic `{(x, y) | y ^ 2 = x ^ 3}` over a field `k`. -/

lemma cuspRes_cuspRes_inv {p : k × k} (hp : p ∈ cuspCurve k) :
    cuspRes k (cuspRes.inv k p) = p := by
  obtain ⟨x, y⟩ := p
  simp only [cuspCurve, Set.mem_setOf_eq] at hp
  rcases eq_or_ne x 0 with rfl | hx
  · have hy : y = 0 := by
      have : y ^ 2 = 0 := by simpa using hp
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    simp [cuspRes, cuspRes.inv, hy]
  · have hx2 : x ^ 2 ≠ 0 := pow_ne_zero _ hx
    have hx3 : x ^ 3 ≠ 0 := pow_ne_zero _ hx
    refine Prod.ext ?_ ?_ <;> simp only [cuspRes, cuspRes.inv] <;> field_simp
    · exact hp
    · calc y ^ 3 = y * y ^ 2 := by ring
        _ = y * x ^ 3 := by rw [hp]

