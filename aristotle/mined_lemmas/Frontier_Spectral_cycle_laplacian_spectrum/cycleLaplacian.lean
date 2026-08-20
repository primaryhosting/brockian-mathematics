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

noncomputable def cycleLaplacian (n : ℕ) [NeZero n] : Matrix (ZMod n) (ZMod n) ℂ :=
  Matrix.circulant (fun i => if i = 0 then 2 else if i = 1 ∨ i = -1 then -1 else 0)

/-- Circulant matrices of "delta functions" multiply by adding the indices. -/
