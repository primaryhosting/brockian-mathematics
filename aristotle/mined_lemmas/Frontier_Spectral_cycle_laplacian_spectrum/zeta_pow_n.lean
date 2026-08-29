/-
# Cycle Laplacian Spectrum
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_laplacian_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cycle Laplacian Spectrum
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_laplacian_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header above is repeated as a plain comment at the very top of the file, since Lean does not
allow a module docstring to precede the `import` commands.)

We model the cycle graph `C n` on the vertex set `ZMod n` and its graph Laplacian as the circulant
matrix with `2` on the diagonal and `-1` on the two cyclic off-diagonals.  Conjugating by the
discrete Fourier matrix `F j k = exp (2 π i j k / n)` diagonalises it, which identifies the spectrum
as `{2 - 2 cos (2 π k / n) : k ∈ range n}`.
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

/-- The graph Laplacian of the cycle graph `C n`, indexed by `ZMod n`:
the circulant matrix with `2` on the diagonal and `-1` on the two cyclic off-diagonals. -/

theorem zeta_pow_n : zeta n ^ n = 1 := (isPrimitiveRoot_zeta n).pow_eq_one

omit [NeZero n] in
