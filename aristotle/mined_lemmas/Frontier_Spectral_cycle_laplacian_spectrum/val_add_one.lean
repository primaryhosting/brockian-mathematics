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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier.Spectral

open Matrix Complex

/-- The graph Laplacian `L(C n)` of the cycle graph on `n` vertices: the `n × n` circulant
matrix with `2` on the diagonal and `-1` on the two cyclic off-diagonals. -/

lemma val_add_one (hn : 2 ≤ n) (i : Fin n) : ((i + 1 : Fin n) : ℕ) = (i.val + 1) % n := by
  rw [Fin.val_add, val_one hn]

omit [NeZero n] in
/-- If `z ^ n = 1` then the exponent of `z` may be reduced mod `n`. -/
