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

lemma shiftM_mulVec (a : ZMod n) (v : ZMod n → ℂ) (i : ZMod n) :
    (shiftM n a *ᵥ v) i = v (i - a) := by
  have hcond : ∀ j : ZMod n, (i - j = a) = (j = i - a) := by
    intro j
    apply propext
    constructor <;> intro h <;> linear_combination -h
  simp only [Matrix.mulVec, dotProduct, shiftM_apply, hcond, ite_mul, one_mul, zero_mul]
  exact (Finset.sum_ite_eq' Finset.univ (i - a) v).trans (by simp)

