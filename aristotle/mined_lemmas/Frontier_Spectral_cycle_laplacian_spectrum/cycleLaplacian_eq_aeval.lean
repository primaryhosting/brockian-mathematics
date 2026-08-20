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

lemma cycleLaplacian_eq_aeval (n : ℕ) [NeZero n] (hn : 3 ≤ n) :
    cycleLaplacian n = aeval (cycleShift n) (C 2 - X - X ^ (n - 1) : ℂ[X]) := by
  obtain ⟨e1, e2, e3⟩ := zmod_zero_one_neg_one_distinct n hn
  have hcast : ((n - 1 : ℕ) : ZMod n) = -1 := by
    have h1 : (1 : ℕ) ≤ n := by omega
    push_cast [Nat.cast_sub h1]
    simp
  rw [show (aeval (cycleShift n) (C 2 - X - X ^ (n - 1) : ℂ[X]))
      = algebraMap ℂ (Matrix (ZMod n) (ZMod n) ℂ) 2 - cycleShift n - (cycleShift n) ^ (n - 1) by
    simp [map_sub]]
  rw [cycleShift_pow, hcast, cycleShift, cycleLaplacian]
  ext i j
  simp only [Matrix.circulant_apply, Matrix.sub_apply, Pi.single_apply,
    Matrix.algebraMap_matrix_apply, ← sub_eq_zero (a := i) (b := j)]
  by_cases h0 : i - j = 0 <;> by_cases h1 : i - j = 1 <;> by_cases h2 : i - j = -1 <;> simp_all

/-- If `v ^ n = 1` then the exponent of `v` only matters modulo `n`. -/
