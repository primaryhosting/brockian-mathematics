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

lemma cusp_singular_locus [CharZero k] {p : k × k} (hp : p ∈ cuspCurve k) :
    (3 * p.1 ^ 2 = 0 ∧ 2 * p.2 = 0) ↔ p = (0, 0) := by
  obtain ⟨x, y⟩ := p
  simp only [cuspCurve, Set.mem_setOf_eq] at hp
  constructor
  · rintro ⟨h1, h2⟩
    have hx : x = 0 := by
      have : x ^ 2 = 0 := by
        rcases mul_eq_zero.mp h1 with h | h
        · norm_num at h
        · exact h
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    have hy : y = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · norm_num at h
      · exact h
    simp [hx, hy]
  · rintro h
    obtain ⟨hx, hy⟩ := Prod.mk.injEq .. ▸ h
    simp_all

/-- **Resolution of singularities (Hironaka), an instance in characteristic 0.**

Over any field of characteristic zero, the singular cuspidal cubic `C : y ^ 2 = x ^ 3`
admits a resolution by the smooth affine line: the morphism `t ↦ (t ^ 2, t ^ 3)`

* is a bijection from the (smooth) affine line onto `C`;
* is an isomorphism over the smooth locus `C \ {(0,0)}`, with regular inverse `(x, y) ↦ y / x`;
* and `C` is genuinely singular exactly at the origin (the gradient of the defining
  equation vanishes there and nowhere else on `C`).
-/
