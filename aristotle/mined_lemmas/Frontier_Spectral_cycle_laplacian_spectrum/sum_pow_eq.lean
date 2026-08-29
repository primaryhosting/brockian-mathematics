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

open Matrix

/-- The graph Laplacian of the cycle graph `C n`: the `n × n` circulant matrix with `2` on the
diagonal and `-1` on the two cyclic off-diagonals. -/

lemma sum_pow_eq {n : ℕ} {z : ℂ} (hz : z ^ n = 1) :
    ∑ p : Fin n, z ^ (p : ℕ) = if z = 1 then (n : ℂ) else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => z ^ i) n]
  by_cases h : z = 1
  · simp [h]
  · rw [if_neg h, geom_sum_eq h, hz, sub_self, zero_div]

