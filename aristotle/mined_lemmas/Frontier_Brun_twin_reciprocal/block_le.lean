import Mathlib
import RequestProject.Brun.Final

/-!
# Brun Twin Reciprocal
Category: Frontier — Prime Numbers
Target: Frontier.Brun_twin_reciprocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede every other command, including module
-- doc comments, so the required header comment appears immediately after the imports.)

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.

The summand is `1/n` whenever `n` and `n + 2` are both prime, and `0` otherwise; the value of
its sum is Brun's constant.  Convergence is proved from scratch by a Brun pure sieve; see the
development in `RequestProject/Brun/`. -/

lemma block_le (i j : ℕ) (hj : 16 ≤ j) (hij : 2 * E j ≤ i) :
    block i ≤ 4 * Real.exp (-(j:ℝ)) + 2 * rt^i := by
  have hcount := twin_count_le j hj (2^(i+1))
  have h2i : (0:ℝ) < 2^i := by positivity
  have hstep : block i ≤ (1/(2:ℝ)^i) * (2*(2^(i+1) : ℕ)*Real.exp (-(j:ℝ)) + 2^(E j + 1)) := by
    refine (block_le_count i).trans ?_
    apply mul_le_mul_of_nonneg_left hcount (by positivity)
  have hpow : ((2^(i+1) : ℕ) : ℝ) = 2 * 2^i := by push_cast; ring
  have hfirst : (1/(2:ℝ)^i) * (2*((2^(i+1) : ℕ) : ℝ)*Real.exp (-(j:ℝ))) = 4 * Real.exp (-(j:ℝ)) := by
    rw [hpow]
    field_simp
    ring
  have hsecond : (1/(2:ℝ)^i) * (2:ℝ)^(E j + 1) ≤ 2 * rt^i := by
    have hsq : ((2:ℝ)^(E j))^2 ≤ ((Real.sqrt 2)^i)^2 := by
      have h1 : ((2:ℝ)^(E j))^2 = 2^(2 * E j) := by
        rw [← pow_mul, mul_comm]
      have h2 : ((Real.sqrt 2)^i)^2 = (2:ℝ)^i := by
        rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]
      rw [h1, h2]
      exact pow_le_pow_right₀ (by norm_num) hij
    have hle : (2:ℝ)^(E j) ≤ (Real.sqrt 2)^i :=
      (sq_le_sq₀ (by positivity) (by positivity)).mp hsq
    have hrw : (1/(2:ℝ)^i) * (2:ℝ)^(E j + 1) = 2 * ((2:ℝ)^(E j) / 2^i) := by
      rw [pow_succ]
      field_simp
    rw [hrw]
    have hrt : rt^i = (Real.sqrt 2)^i / 2^i := by
      unfold rt
      rw [div_pow]
    rw [hrt]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact (div_le_div_iff_of_pos_right (by positivity)).mpr hle
  calc block i ≤ (1/(2:ℝ)^i) * (2*((2^(i+1) : ℕ) : ℝ)*Real.exp (-(j:ℝ)) + 2^(E j + 1)) := hstep
    _ = (1/(2:ℝ)^i) * (2*((2^(i+1) : ℕ) : ℝ)*Real.exp (-(j:ℝ))) + (1/(2:ℝ)^i) * 2^(E j + 1) := by
        ring
    _ ≤ 4 * Real.exp (-(j:ℝ)) + 2 * rt^i := by rw [hfirst]; linarith [hsecond]

