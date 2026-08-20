/-
# Expander Uniform Gap Witness
Category: Frontier Spectral
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Expander Uniform Gap Witness
Category: Frontier Spectral
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

/-- Flip the `i`-th coordinate of a vertex of the hypercube. -/

theorem energy_ge_of_sum_eq_zero {k : ℕ} (f : (Fin k → Bool) → ℝ)
    (hf : ∑ x : Fin k → Bool, f x = 0) :
    2 * ∑ x : Fin k → Bool, (f x) ^ 2 ≤ f ⬝ᵥ ((hypercube k).lapMatrix ℝ *ᵥ f) := by
  have := poincare k f
  rw [dotProduct_lap]
  rw [hf] at this
  simp at this
  linarith

/-- **Uniform spectral gap for the hypercube family.** For every `k ≥ 1`, the smallest nonzero
eigenvalue of the Laplacian of the hypercube graph `Q_k` on `2^k` vertices equals `2`, a bound
independent of `k`. -/
