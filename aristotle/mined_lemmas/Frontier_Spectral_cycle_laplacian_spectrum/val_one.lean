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

lemma val_one (hn : 2 ≤ n) : ((1 : Fin n) : ℕ) = 1 := by
  simp [Nat.mod_eq_of_lt (by omega : 1 < n)]

