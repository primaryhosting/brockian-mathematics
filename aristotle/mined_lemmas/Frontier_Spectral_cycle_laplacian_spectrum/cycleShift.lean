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

noncomputable def cycleShift (n : ℕ) [NeZero n] : Matrix (ZMod n) (ZMod n) ℂ :=
  Matrix.circulant (Pi.single 1 1)

/-- The graph Laplacian of the cycle graph `C n`, modelled as the `n × n` circulant matrix with
diagonal `2` and `-1` on the two cyclic off-diagonals. -/
