/-
# Hironaka Resolution
Category: Frontier Math
Target: Math2.hironaka_resolution
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Math2

open MvPolynomial

variable {k : Type*} [Field k]

/-- The affine plane curve `C_{p,q} : y^p = x^q`, as a polynomial in two variables. -/

lemma param_surjOn (hp : p ≠ 0) (hq : q ≠ 0) {a b : ℤ} (hab : a * p + b * q = 1) :
    ∀ x ∈ zeroLocus (cuspCurve k p q), param p q ((x 0) ^ a * (x 1) ^ b) = x := by
  intro x hx
  have hcur : (x 1) ^ p = (x 0) ^ q := by
    have := hx
    simp only [zeroLocus, Set.mem_setOf_eq, eval_cuspCurve, sub_eq_zero] at this
    exact this
  rcases eq_or_ne (x 0) 0 with hx0 | hx0
  · have hx1 : x 1 = 0 := by
      have : (x 1) ^ p = 0 := by rw [hcur, hx0, zero_pow hq]
      exact (pow_eq_zero_iff hp).mp this
    have hab0 : a ≠ 0 ∨ b ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      rw [hcon.1, hcon.2] at hab
      simp at hab
    have ht0 : ((x 0) ^ a * (x 1) ^ b : k) = 0 := by
      rw [hx0, hx1]
      rcases hab0 with h | h
      · rw [zero_zpow a h, zero_mul]
      · rw [zero_zpow b h, mul_zero]
    rw [ht0, param_zero p q hp hq]
    exact (eq_zero_of_coords hx0 hx1).symm
  · have hx1 : x 1 ≠ 0 := by
      intro h
      apply hx0
      have : (x 0) ^ q = 0 := by rw [← hcur, h, zero_pow hp]
      exact (pow_eq_zero_iff hq).mp this
    set t : k := (x 0) ^ a * (x 1) ^ b with ht
    have hcurz : ((x 1) ^ (p : ℤ) : k) = ((x 0) ^ (q : ℤ) : k) := by
      rw [← zpow_natCast (x 1) p, ← zpow_natCast (x 0) q] at hcur
      exact hcur
    have hp' : t ^ p = x 0 := by
      rw [ht, mul_pow, ← zpow_natCast ((x 0) ^ a) p, ← zpow_natCast ((x 1) ^ b) p,
        ← zpow_mul, ← zpow_mul]
      have : ((x 1) ^ (b * (p : ℤ)) : k) = ((x 0) ^ ((q : ℤ) * b) : k) := by
        rw [mul_comm b (p : ℤ), zpow_mul, hcurz, ← zpow_mul]
      rw [this, ← zpow_add₀ hx0]
      rw [show (a * (p : ℤ) + (q : ℤ) * b) = 1 by linarith [hab]]
      simp
    have hq' : t ^ q = x 1 := by
      rw [ht, mul_pow, ← zpow_natCast ((x 0) ^ a) q, ← zpow_natCast ((x 1) ^ b) q,
        ← zpow_mul, ← zpow_mul]
      have : ((x 0) ^ (a * (q : ℤ)) : k) = ((x 1) ^ ((p : ℤ) * a) : k) := by
        rw [mul_comm a (q : ℤ), zpow_mul, ← hcurz, ← zpow_mul]
      rw [this, ← zpow_add₀ hx1]
      rw [show ((p : ℤ) * a + b * (q : ℤ)) = 1 by linarith [hab]]
      simp
    funext i
    fin_cases i
    · simpa using hp'
    · simpa using hq'

end

/-- **Resolution of singularities for the monomial plane curve singularities `y^p = x^q`**
(an explicit instance, in characteristic zero, of Hironaka's resolution theorem).

Let `k` be a field of characteristic `0` and let `p, q ≥ 2` be coprime.  For the plane curve
`C : y^p = x^q` the following hold.

1. `C` is singular exactly at the origin (Jacobian criterion).
2. The map `π : 𝔸¹ → 𝔸²`, `t ↦ (t^p, t^q)`, is a bijection from the smooth curve `𝔸¹` onto `C`,
   i.e. `π` is a surjective, injective (in particular proper, quasi-finite) parametrization.
3. `π` restricts to a bijection of `𝔸¹ ∖ {0}` onto the smooth locus `C ∖ {0}`, and its inverse
   there is given by the monomial rational function `x ↦ x₀^a · x₁^b` for Bézout exponents
   `a·p + b·q = 1`; hence `π` is birational and is an isomorphism over the smooth locus.
4. The exceptional fibre over the singular point is the single point `t = 0`.
5. Away from the exceptional point the differential of `π` is nonzero, so `π` is an immersion
   there.
6. `π` is a finite (hence proper) morphism: the coordinate ring `k[t]` of the source is integral
   over the coordinate ring `k[t^p, t^q]` of the curve. -/
