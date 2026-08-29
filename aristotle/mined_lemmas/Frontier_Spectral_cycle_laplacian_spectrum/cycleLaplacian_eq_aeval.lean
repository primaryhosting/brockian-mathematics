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

lemma cycleLaplacian_eq_aeval (hn : 3 ≤ n) :
    (Polynomial.aeval (shiftM n (-1))) ((C 2 - X - X ^ (n - 1) : ℂ[X])) = cycleLaplacian n := by
  have hcast : ((n - 1 : ℕ) : ZMod n) = -1 := by
    have h : ((n - 1 : ℕ) : ZMod n) = ((n : ℕ) : ZMod n) - ((1 : ℕ) : ZMod n) := by
      rw [← Nat.cast_sub (by omega)]
    rw [h, ZMod.natCast_self]
    simp
  rw [map_sub, map_sub, aeval_C, map_pow, aeval_X, shiftM_neg_one_pow, hcast, neg_neg]
  have h10 : (1 : ZMod n) ≠ 0 := one_ne_zero_zmod hn
  have h1n : (1 : ZMod n) ≠ -1 := one_ne_neg_one_zmod hn
  ext i j
  have hij : (i = j) ↔ (i - j = 0) := sub_eq_zero.symm
  simp only [Matrix.sub_apply, shiftM_apply, cycleLaplacian_apply,
    Algebra.algebraMap_eq_smul_one, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, hij]
  exact laplacian_entry_identity h10 h1n (i - j)

end Distinct

section Eigen

variable {n : ℕ} [NeZero n]

/-- If `M *ᵥ v = μ • v` for some nonzero `v`, then `μ` lies in the spectrum of `M`. -/
