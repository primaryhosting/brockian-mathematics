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

lemma cos_two_pi_div_lt_one {n : ℕ} (hn : 3 ≤ n) : Real.cos (2 * Real.pi / n) < 1 := by
  have hnpos : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpi := Real.pi_pos
  have hth_pos : 0 < 2 * Real.pi / n := by positivity
  have hthpi : 2 * Real.pi / n ≤ Real.pi := by
    rw [div_le_iff₀ hnpos]
    nlinarith
  have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hthpi hth_pos
  simpa using this

/-! ## The spectrum of the cycle Laplacian -/

/-- Every eigenvalue of the cycle Laplacian is of the form `2 - 2 cos (2 π k / n)`, witnessed
by a Fourier mode `k` which is nonzero whenever the eigenvector has vanishing sum. -/
