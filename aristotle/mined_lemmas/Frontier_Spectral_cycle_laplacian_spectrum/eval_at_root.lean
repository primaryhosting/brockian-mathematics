import Mathlib

/-!
# Cycle Laplacian Spectrum
Category: Frontier Spectral
Target: Frontier.Spectral.cycle_laplacian_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Frontier.Spectral

open Complex Matrix Polynomial

/-- The cyclic shift matrix indexed by `ZMod n`: the circulant matrix whose `(i, j)` entry is `1`
exactly when `i - j = 1`. -/

lemma eval_at_root (n k : ℕ) (hn : 1 ≤ n) :
    eval (Complex.exp (2 * Real.pi * Complex.I * k / n)) (C 2 - X - X ^ (n - 1) : ℂ[X]) =
      ((2 - 2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ) := by
  set z : ℂ := Complex.exp (2 * Real.pi * Complex.I * k / n) with hzdef
  have hzn : z ^ n = 1 := by
    rw [hzdef, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨k, ?_⟩
    have h : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
    push_cast
    ring
  have hz0 : z ≠ 0 := Complex.exp_ne_zero _
  have hpow : z ^ (n - 1) = z⁻¹ := by
    have h : z ^ (n - 1) * z = 1 := by rw [← pow_succ, Nat.sub_add_cancel hn, hzn]
    field_simp at h ⊢
    linear_combination h
  set t : ℝ := 2 * Real.pi * k / n with ht
  have hzt : z = Complex.exp ((t : ℂ) * Complex.I) := by
    rw [hzdef, ht]; push_cast; ring_nf
  simp only [eval_sub, eval_pow, eval_C, eval_X]
  rw [hpow, hzt, ← Complex.exp_neg]
  push_cast
  rw [Complex.cos, show -((t : ℂ) * Complex.I) = -(t : ℂ) * Complex.I by ring]
  ring

/-- **Spectrum of the cycle Laplacian.** For `n ≥ 3` the eigenvalues of the graph Laplacian of
the cycle graph `C n` are exactly the numbers `2 - 2 cos (2 π k / n)` for `k = 0, …, n - 1`.

The instance argument `[NeZero n]` is implied by `3 ≤ n`; it appears in the statement only so
that the index type `ZMod n` of the matrix is finite. -/
