/-
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open Finset Matrix SimpleGraph

namespace Frontier.Spectral

/-! ## The root of unity `ζ = exp (2 π i / n)` -/

/-- The primitive `n`-th root of unity `exp (2 π i / n)`. -/

lemma dft_eigen {n : ℕ} [NeZero n] (y : Fin n → ℂ) (mu : ℂ) (k : ℤ)
    (hy : ∀ v : Fin n, 2 * y v - y (v - 1) - y (v + 1) = mu * y v) :
    (2 - zeta n ^ k - zeta n ^ (-k)) * dft n y k = mu * dft n y k := by
  have h : ∑ v : Fin n, (2 * y v - y (v - 1) - y (v + 1)) * zeta n ^ (-(k * (v : ℕ)))
      = ∑ v : Fin n, (mu * y v) * zeta n ^ (-(k * (v : ℕ))) :=
    Finset.sum_congr rfl fun v _ => by rw [hy v]
  have e1 : ∑ v : Fin n, (2 * y v - y (v - 1) - y (v + 1)) * zeta n ^ (-(k * (v : ℕ)))
      = 2 * dft n y k - zeta n ^ (-k) * dft n y k - zeta n ^ k * dft n y k := by
    rw [← dft_shift_left y k, ← dft_shift_right y k]
    nth_rewrite 1 [dft]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  have e2 : ∑ v : Fin n, (mu * y v) * zeta n ^ (-(k * (v : ℕ))) = mu * dft n y k := by
    rw [dft, Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [e1, e2] at h
  linear_combination h

/-! ## The eigenvectors -/

/-- The real eigenvector `j ↦ cos (2 π k j / n)` of the cycle Laplacian. -/
