/-
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Statement: For a bound stationary state, 2⟨T⟩ = ⟨r·∇V⟩ (quantum virial theorem).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open MeasureTheory Filter Topology

namespace Phys

/-- **Auxiliary integration-by-parts fact.**  If `f` is everywhere differentiable with
integrable derivative `f'` and `f` tends to `0` at both ends of the real line, then the
integral of `f'` over `ℝ` vanishes. -/

theorem integrable_sq_mul_exp_neg_sq :
    Integrable (fun x : ℝ => x ^ 2 * Real.exp (-x ^ 2)) volume := by
  simpa using integrable_rpow_mul_exp_neg_mul_sq (b := 1) (s := 2) one_pos (by norm_num)

/-- **Non-vacuity of `Phys.virial_theorem`.**  All of its hypotheses hold for the
harmonic-oscillator ground state `ψ(x) = exp (-x²/2)`, `V(x) = x²`, `E = 1`, which is a
nonzero state. -/
