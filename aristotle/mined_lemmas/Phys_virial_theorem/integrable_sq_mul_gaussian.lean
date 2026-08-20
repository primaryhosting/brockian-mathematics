/-
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Filter Set Topology

namespace Phys

/-- The auxiliary "virial current"
`F x = x * ψ' x ^ 2 - x * (V x - E) * ψ x ^ 2 + ψ x * ψ' x`,
whose derivative is exactly `2 * ψ' x ^ 2 - x * V' x * ψ x ^ 2` for a solution of the
stationary Schrödinger equation. -/

private theorem integrable_sq_mul_gaussian :
    Integrable (fun x : ℝ => x ^ 2 * Real.exp (-1 * x ^ 2)) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1) one_pos (s := 2) (by norm_num)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  have hx : x ^ (2 : ℝ) = x ^ (2 : ℕ) := by rw [← Real.rpow_natCast x 2]; norm_num
  show x ^ (2 : ℝ) * Real.exp (-1 * x ^ 2) = x ^ 2 * Real.exp (-1 * x ^ 2)
  rw [hx]

/-- Instance of the virial theorem for the harmonic oscillator `H = -d²/dx² + x²` with ground
state `ψ x = exp (-x²/2)`, energy `E = 1`: it shows that the hypotheses of
`Phys.virial_theorem` are not vacuous. -/
