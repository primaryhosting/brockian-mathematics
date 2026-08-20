/-
# Cycle Laplacian Spectrum
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_laplacian_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

open Matrix Finset

/-- The graph Laplacian of the cycle graph `C n`, as the `n × n` circulant matrix with `2` on the
diagonal and `-1` on the two cyclic off-diagonals. -/

def finZModEquiv : Fin n ≃ ZMod n where
  toFun i := (i.val : ZMod n)
  invFun a := ⟨a.val, a.val_lt⟩
  left_inv i := by ext; simp [ZMod.val_natCast_of_lt i.isLt]
  right_inv a := by simp [ZMod.natCast_val]

/-- The cycle Laplacian, indexed by `ZMod n`. -/
