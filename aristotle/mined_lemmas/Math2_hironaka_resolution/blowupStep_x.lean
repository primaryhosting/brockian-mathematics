/-
# Hironaka Resolution
Category: Frontier Math
Target: Math2.hironaka_resolution
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede every doc comment, so the header above is
-- written as a plain block comment and repeated verbatim as the module doc comment below.)

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

open MvPolynomial

/-! ## Setup

We work with the affine plane curves `y ^ a = x ^ b` over a field `k` of characteristic
zero, given by the polynomial `curve k a b = Y ^ a - X ^ b` in `MvPolynomial (Fin 2) k`
(`X = X 0`, `Y = X 1`).  These are exactly the singularities resolved by the classical
Euclidean/continued-fraction sequence of point blowups.

Blowing up the origin of the affine plane is covered by two charts:

* the `x`-chart, `(x, y) ↦ (x, x * y)`;
* the `y`-chart, `(x, y) ↦ (x * y, y)`.

The *total transform* of a curve `p` is its pullback along one of these substitutions; the
*strict transform* is obtained by removing the largest possible power of the exceptional
divisor (`x`, resp. `y`) from the total transform.  This is the content of `BlowupStep`.
-/

/-- The plane curve `y ^ a = x ^ b`, as the polynomial `Y ^ a - X ^ b`. -/

theorem blowupStep_x {k : Type*} [Field k] {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    BlowupStep (curve k a b) (curve k a (b - a)) := by
  left
  refine ⟨a, ?_, ?_⟩
  · have hb : b = a + (b - a) := by omega
    simp only [xchart, curve, map_sub, map_pow, aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, mul_pow]
    rw [mul_sub]
    congr 1
    rw [← pow_add, ← hb]
  · rcases Nat.eq_or_lt_of_le hab with h | h
    · -- `b = a`, strict transform is `y ^ a - 1`
      apply not_dvd_X_zero _ (0 : k)
      have : b - a = 0 := by omega
      simp [curve, this, zero_pow (by omega : a ≠ 0)]
    · apply not_dvd_X_zero _ (1 : k)
      have hba : b - a ≠ 0 := by omega
      simp [curve, zero_pow hba]

/-- In the `y`-chart, the strict transform of `y ^ a = x ^ b` (with `b < a`) is
`y ^ (a - b) = x ^ b`. -/
