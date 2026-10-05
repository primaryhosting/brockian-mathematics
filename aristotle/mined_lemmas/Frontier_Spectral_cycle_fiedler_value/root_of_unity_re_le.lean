import Mathlib

/-!
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
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

namespace Frontier.Spectral

open Finset SimpleGraph Matrix

/-- The Laplacian of the cycle graph `C n` (`n ≥ 3`) acts on a vector by
`(L v) i = 2 * v i - (v (i-1) + v (i+1))`. -/

lemma root_of_unity_re_le {n : ℕ} (hn : 3 ≤ n) {z : ℂ} (hz : z ^ n = 1) (hz1 : z ≠ 1) :
    z.re ≤ Real.cos (2 * Real.pi / n) := by
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨k, hkn, hk⟩ := (Complex.isPrimitiveRoot_exp n (by omega)).eq_pow_of_pow_eq_one hz
  have hzform : z = Complex.exp (((2 * Real.pi * k / n : ℝ)) * Complex.I) := by
    rw [← hk, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hz1 (by simpa using hk.symm)
  rw [hzform, Complex.exp_ofReal_mul_I_re]
  exact cos_two_pi_mul_le hn hk0 hkn

/-- Lower bound: any eigenvalue of the cycle Laplacian whose eigenvector has zero sum is at
least `2 - 2 cos (2π/n)`. -/
