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

lemma dft_shift_right {n : ℕ} [NeZero n] (y : Fin n → ℂ) (k : ℤ) :
    ∑ v : Fin n, y (v + 1) * zeta n ^ (-(k * (v : ℕ))) = zeta n ^ k * dft n y k := by
  have hn : n ≠ 0 := NeZero.ne n
  rw [← Fintype.sum_equiv (Equiv.subRight (1 : Fin n))
    (fun u => y (u - 1 + 1) * zeta n ^ (-(k * ((u - 1 : Fin n) : ℕ))))
    (fun v => y (v + 1) * zeta n ^ (-(k * (v : ℕ)))) (fun u => rfl)]
  rw [dft, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [sub_add_cancel]
  rw [show zeta n ^ (-(k * (((u - 1 : Fin n) : ℕ) : ℤ))) = zeta n ^ (k + -(k * ((u : ℕ) : ℤ))) from
    zeta_zpow_congr hn (by
      obtain ⟨c, hc⟩ := fin_shift_dvd (u - 1)
      rw [sub_add_cancel] at hc
      exact ⟨k * c, by linear_combination k * hc⟩)]
  rw [zpow_add₀ (zeta_ne_zero n)]
  ring

/-- If `y` satisfies the eigenvalue equation for the discrete Laplacian, each Fourier
coefficient is either zero or forces `μ` to be the corresponding eigenvalue. -/
