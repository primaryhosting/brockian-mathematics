/-
# Cycle Laplacian Spectrum
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_laplacian_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to be the first command; the module docstring below
-- repeats the header verbatim.)
import Mathlib

/-!
# Cycle Laplacian Spectrum
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_laplacian_spectrum
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

open Matrix Polynomial

/-- The cyclic shift matrix on `ZMod n`: `shiftM n a i j = 1` exactly when `i - j = a`. -/

lemma eval_at_root (n : ℕ) [NeZero n] (hn : 1 ≤ n) (k : ℕ) :
    (2 : ℂ) - (Complex.exp (2 * Real.pi * Complex.I / n)) ^ k
        - ((Complex.exp (2 * Real.pi * Complex.I / n)) ^ k) ^ (n - 1)
      = ((2 - 2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ) := by
  have hn0 : (n : ℂ) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := ℂ)).2 (by omega : n ≠ 0)
  set theta : ℝ := 2 * Real.pi * k / n with htheta
  set z : ℂ := Complex.exp (2 * Real.pi * Complex.I / n) with hzdef
  have hzn : z ^ n = 1 := (Complex.isPrimitiveRoot_exp n (by omega)).pow_eq_one
  have hzk : z ^ k = Complex.exp ((theta : ℂ) * Complex.I) := by
    rw [hzdef, ← Complex.exp_nat_mul]
    congr 1
    rw [htheta]
    push_cast
    field_simp
    ring
  have hzkn : (z ^ k) ^ n = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hzn, one_pow]
  have h1 : (z ^ k) ^ (n - 1) * (z ^ k) = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hn, hzkn]
  have hinv : (z ^ k) ^ (n - 1) = (z ^ k)⁻¹ := eq_inv_of_mul_eq_one_left h1
  rw [hinv, hzk, ← Complex.exp_neg]
  have hcos : Complex.exp ((theta : ℂ) * Complex.I) + Complex.exp (-((theta : ℂ) * Complex.I))
      = 2 * Complex.cos (theta : ℂ) := by
    have h := Complex.two_cos (theta : ℂ)
    rw [h]
    ring_nf
  have hc2 : Complex.cos ((theta : ℝ) : ℂ) = ((Real.cos theta : ℝ) : ℂ) :=
    (Complex.ofReal_cos theta).symm
  push_cast
  linear_combination -hcos - 2 * hc2

/-- **Spectrum of the cycle Laplacian.** For `n ≥ 3`, the eigenvalues of the graph Laplacian
of the cycle graph `C n` — modelled as the `n × n` circulant matrix with `2` on the diagonal
and `-1` on the two cyclic off-diagonals — are exactly the numbers `2 - 2 cos (2πk/n)`
for `k ∈ Finset.range n`. -/
